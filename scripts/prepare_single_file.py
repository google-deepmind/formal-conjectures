import argparse
import os
import json
import shutil
import re
from typing import Dict, List

import requests

from scripts.split_conjecture_tasks import parse_stubs, lean_explore_search


def fetch_pr_comments(pr_url: str, token: str | None = None) -> List[dict]:
    """Return PR review comments from GitHub."""
    m = re.match(r"https://github.com/(?P<owner>[^/]+)/(?P<repo>[^/]+)/pull/(?P<num>\d+)", pr_url)
    if not m:
        raise ValueError("Invalid PR URL")
    owner = m.group('owner')
    repo = m.group('repo')
    num = m.group('num')
    headers = {'Accept': 'application/vnd.github+json'}
    if token:
        headers['Authorization'] = f'Bearer {token}'

    comments: List[dict] = []
    page = 1
    while True:
        resp = requests.get(
            f"https://api.github.com/repos/{owner}/{repo}/pulls/{num}/comments",
            headers=headers,
            params={'per_page': 100, 'page': page},
        )
        if resp.status_code != 200:
            raise RuntimeError(f"GitHub API error: {resp.status_code} {resp.text}")
        data = resp.json()
        if not data:
            break
        comments.extend(data)
        page += 1
    return comments


def insert_review_comments(path: str, comments: List[dict]) -> None:
    """Insert review comments as docstrings in the file at *path*."""
    if not comments:
        return
    with open(path, 'r') as fh:
        lines = fh.readlines()

    comments_by_line: Dict[int, List[str]] = {}
    for c in comments:
        line_no = c.get('original_line') or c.get('line')
        if line_no is None:
            continue
        body = c.get('body')
        if not body:
            continue
        comments_by_line.setdefault(int(line_no), []).append(body)

    for line_no in sorted(comments_by_line.keys(), reverse=True):
        bodies = comments_by_line[line_no]
        for body in bodies[::-1]:
            prefix = "-- REVIEW COMMENT: "
            for i, line in enumerate(body.splitlines()):
                if i == 0:
                    lines.insert(line_no, prefix + line + "\n")
                else:
                    lines.insert(line_no + i, "-- " + line + "\n")

    with open(path, 'w') as fh:
        fh.writelines(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description="Prepare single Lean file task")
    parser.add_argument('--lean', required=True, help='Lean file to process')
    parser.add_argument('--out', required=True, help='Output directory')
    parser.add_argument('--pool', default='docs/definitions_pool.json',
                        help='Global pool of definitions')
    parser.add_argument('--lean-explore', dest='lean_explore', default=None,
                        help='LeanExplore API base URL')
    parser.add_argument('--lean-explore-key', dest='lean_explore_key', default=None,
                        help='LeanExplore API key')
    parser.add_argument('--lean-explore-local', dest='lean_explore_local',
                        action='store_true', help='Use LeanExplore local dataset')
    parser.add_argument('--pr', dest='pull_request', required=True,
                        help='GitHub pull request URL to fetch comments from')
    parser.add_argument('--gh-token', dest='github_token', default=None,
                        help='GitHub token for API access')
    args = parser.parse_args()

    os.makedirs(args.out, exist_ok=True)

    local_service = None
    if args.lean_explore_local:
        try:
            from lean_explore.local.service import Service
            local_service = Service()
        except Exception:
            local_service = None

    stubs = parse_stubs(args.lean)

    pool = {}
    if os.path.exists(args.pool):
        with open(args.pool) as fh:
            pool = json.load(fh)

    def merge_def(name: str, definition: str) -> None:
        current = pool.get(name)
        if current is None:
            pool[name] = definition
        elif isinstance(current, list):
            if definition not in current:
                current.append(definition)
        else:
            if definition != current:
                pool[name] = [current, definition]

    for name, definition in stubs.items():
        merge_def(name, definition)

    with open(args.pool, 'w') as fh:
        json.dump(pool, fh, indent=2, sort_keys=True)

    # fetch PR comments and insert them into a copy of the file
    pr_comments = fetch_pr_comments(args.pull_request, args.github_token)
    relevant_comments = [c for c in pr_comments if os.path.normpath(c.get('path', '')) == os.path.normpath(args.lean)]
    copied_file = os.path.join(args.out, os.path.basename(args.lean))
    shutil.copy(args.lean, copied_file)
    insert_review_comments(copied_file, relevant_comments)

    with open(os.path.join(args.out, 'task.md'), 'w') as f_task:
        f_task.write(f"# Task for {os.path.basename(args.lean)}\n\n")
        f_task.write("Implement the following definitions and address reviewer comments.\n\n")
        for d, code in stubs.items():
            f_task.write(f"## {d}\n")
            f_task.write("```lean\n" + code + "\n```\n")
            for ref in lean_explore_search(
                d,
                args.lean_explore,
                args.lean_explore_key,
                backend='local' if args.lean_explore_local else 'remote',
                service=local_service,
            ):
                code_snip = ref.get('code')
                path = ref.get('file')
                start = ref.get('start')
                end = ref.get('end')
                if code_snip:
                    f_task.write(
                        f"LeanExplore reference `{path}` lines {start}-{end}:\n")
                    f_task.write("```lean\n" + code_snip + "\n```\n")
                elif path:
                    f_task.write(
                        f"-- LeanExplore reference: {path} lines {start}-{end}\n")
            f_task.write("\n")

    with open(os.path.join(args.out, 'AGENTS_single_task.md'), 'w') as f_agent:
        f_agent.write("# Single File Task\n\n")
        f_agent.write(f"Work on `{args.lean}`. Implement the missing definitions and incorporate the reviewer comments added to the file.\n\n")
        f_agent.write("1. Fill in the missing definitions.\n")
        f_agent.write(f"2. Run `lake build {args.lean}` and ensure it compiles.\n")
        f_agent.write("3. Do not delete existing code.\n")
        f_agent.write("4. Use `python3 scripts/local_search_tool.py <string> --limit 5` to find additional Lean and mathlib references.\n")
        f_agent.write("   For example:\n   `python3 scripts/local_search_tool.py \"bipartite graph\" --limit 5`\n")
        f_agent.write("5. Deleting the theorem or definitions is not allowed.\n")
        f_agent.write("6. Work until the compilation succeeds. Do not give up.\n")
        f_agent.write("7. If patching does not work then write the file from scratch, using for example `cat > {args.lean} << 'EOF'`.\n")
        f_agent.write("8. You work in a sandbox. Simple commands such as `lake build` are going to work, but hacking the manifest or rebuilding the whole of mathlib is unlikely to succeed. Focus on simple changes.\n")
        f_agent.write("9. It is not allowed to leave definitions and theorems inside a docstring / comment, because you need to check whether they can be compiled with `lake build`.\n")
        f_agent.write("10. Ensure reviewer comments have been addressed in your implementation.\n")


if __name__ == '__main__':
    main()
