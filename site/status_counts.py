#!/usr/bin/env python3
"""Statement counts per problem status across the repository's git history.

The status counts on the website come from `lake exe extract_names`, which
needs a full Lean build and so cannot be repeated for every commit. The counts
here are read from the source text instead, following the rules that decide
which declarations `extract_names` reports:

* Only `theorem`, `lemma` and `instance` declarations carry a category.
* Declarations Lean treats as internal are dropped, that is `private` ones and
  those with a `_`-prefixed name component.
* A declaration counts once towards `formally proved` however many
  `formal_proof` attributes it carries.

Before #3645 a formal proof was recorded as the category
`research formally solved` rather than as a separate `formal_proof` attribute,
so both spellings are recognised.
"""

import re
import subprocess
from datetime import datetime

# Same set of files the file count covers.
SOURCE_PATH = re.compile(r'^FormalConjectures/(?!ForMathlib/).*\.lean$')

# Declaration keywords that may follow an attribute block. `private` is listed
# so that it can be recognised and skipped; the modifiers before it are not.
DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:protected\s+|noncomputable\s+|public\s+|nonrec\s+)*"
    r"(private|theorem|lemma|instance|def|abbrev|example)\b[ \t]*([^\s:({\[]*)")
CATEGORISED = ('theorem', 'lemma', 'instance')

CATEGORY = re.compile(
    r'\bcategory\s+(research\s+solved|research\s+open|textbook|test|API)\b')
FORMAL_PROOF = re.compile(r'\bformal_proof\s+using\b')
FORMALLY_SOLVED = re.compile(r'\bcategory\s+research\s+formally\s+solved\b')

STATUSES = ('open', 'solved', 'formal')


def strip_comments(source):
    """Blanks out comments and string literals, keeping every other offset.

    Attribute names are mentioned in docstrings and in commented-out code, so
    they have to go before anything is matched. Offsets are preserved so that a
    declaration still follows its attribute block.

    Args:
        source (str): Contents of a Lean file

    Returns:
        str: The same text with comments and string literals replaced by spaces
    """
    out = list(source)
    end = len(source)
    i = 0
    while i < end:
        if source.startswith('/-', i):
            # Block comments nest, so track the depth rather than taking the
            # first closing marker.
            depth = 1
            j = i + 2
            while j < end and depth:
                if source.startswith('/-', j):
                    depth += 1
                    j += 2
                elif source.startswith('-/', j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
        elif source.startswith('--', i):
            j = source.find('\n', i)
            j = end if j < 0 else j
        elif source[i] == '"':
            j = i + 1
            while j < end and source[j] != '"':
                j += 2 if source[j] == '\\' else 1
            j = min(j + 1, end)
        else:
            i += 1
            continue
        for k in range(i, j):
            if out[k] != '\n':
                out[k] = ' '
        i = j
    return ''.join(out)


def attribute_blocks(source):
    """Yields each `@[...]` block with the text that follows it.

    Args:
        source (str): Contents of a Lean file, with comments already stripped

    Yields:
        tuple[str, str]: The contents of the brackets, and the text after them
    """
    end = len(source)
    i = 0
    while True:
        start = source.find('@[', i)
        if start < 0:
            return
        depth = 1
        j = start + 2
        while j < end and depth:
            if source[j] == '[':
                depth += 1
            elif source[j] == ']':
                depth -= 1
            j += 1
        # A declaration header is never long enough to need more than this.
        yield source[start + 2:j - 1], source[j:j + 400]
        i = j


def count_statuses(source):
    """Counts the statements per status in one Lean file.

    Args:
        source (str): Contents of a Lean file

    Returns:
        dict[str, int]: Count for each of `STATUSES`
    """
    counts = dict.fromkeys(STATUSES, 0)
    for attributes, following in attribute_blocks(strip_comments(source)):
        declaration = DECLARATION.match(following)
        if not declaration or declaration.group(1) not in CATEGORISED:
            continue
        if any(part.startswith('_') for part in declaration.group(2).split('.')):
            continue
        if FORMALLY_SOLVED.search(attributes):
            counts['solved'] += 1
            counts['formal'] += 1
            continue
        category = CATEGORY.search(attributes)
        if category is None:
            continue
        if category.group(1) == 'research open':
            counts['open'] += 1
        elif category.group(1) == 'research solved':
            counts['solved'] += 1
        if FORMAL_PROOF.search(attributes):
            counts['formal'] += 1
    return counts


def get_status_counts_over_time(start_date, columns):
    """Retrieves statement counts per status over time.

    Args:
        start_date (str): Date from which to start collecting commits
        columns (list[str]): Column labels for the returned rows, the first for
            the date and the rest for `STATUSES` in order

    Returns:
        list[list]: One row per commit, each holding a date and the counts
    """
    if not isinstance(columns, list) or len(columns) != len(STATUSES) + 1:
        raise ValueError(
            f"The `columns` parameter should be a list of length {len(STATUSES) + 1}.")

    command = ['git', 'log', '--pretty=format:%H,%ct']
    result = subprocess.run(command, capture_output=True, text=True, check=True)
    commit_lines = [line for line in result.stdout.strip().split('\n') if line]
    commit_lines.reverse()

    data = []
    # A blob is its own content hash, so a file that did not change between two
    # commits is only read and counted once. Without this the same few hundred
    # files would be parsed again for every commit.
    counted_blobs = {}
    reader = subprocess.Popen(['git', 'cat-file', '--batch'],
                             stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for line in commit_lines:
            sha, timestamp = line.split(',')
            timestamp = int(timestamp)
            if timestamp <= datetime.fromisoformat(start_date).timestamp():
                continue

            tree_command = ['git', 'ls-tree', '-r', sha]
            tree_result = subprocess.run(tree_command, capture_output=True,
                                         text=True, check=True)
            totals = dict.fromkeys(STATUSES, 0)
            for entry in tree_result.stdout.strip().split('\n'):
                if not entry:
                    continue
                metadata, _, path = entry.partition('\t')
                if not SOURCE_PATH.match(path):
                    continue
                blob = metadata.split(' ')[2]
                if blob not in counted_blobs:
                    reader.stdin.write(f'{blob}\n'.encode())
                    reader.stdin.flush()
                    size = int(reader.stdout.readline().split()[2])
                    # `git cat-file --batch` appends a newline to the contents.
                    contents = reader.stdout.read(size + 1)[:-1]
                    counted_blobs[blob] = count_statuses(
                        contents.decode('utf-8', 'replace'))
                for status, count in counted_blobs[blob].items():
                    totals[status] += count

            data.append([datetime.fromtimestamp(timestamp)] +
                        [totals[status] for status in STATUSES])
    finally:
        reader.stdin.close()
        reader.wait()

    return data
