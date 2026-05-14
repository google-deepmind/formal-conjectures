#!/usr/bin/env python3
"""
Extract Verso fragments from literate HTML output.

Produces a compact JSON with:
- moduleDocs: module path -> rendered module docstring HTML
- constLinks: Lean const name -> { url, anchor, docHtml }

Usage: python3 extract_verso_fragments.py <literate-html-dir> <output-json>
"""

import json
import os
import sys

from bs4 import BeautifulSoup


def walk_html_files(root):
    """Find all index.html files under root."""
    for dirpath, _, filenames in os.walk(root):
        for f in filenames:
            if f == 'index.html':
                yield os.path.join(dirpath, f)


def extract_from_html(html_path, base_dir):
    """Extract module doc and const links from a Verso HTML file."""
    with open(html_path, encoding='utf-8') as f:
        soup = BeautifulSoup(f, 'lxml')

    rel = os.path.relpath(os.path.dirname(html_path), base_dir)
    module_path = '/' + rel.replace(os.sep, '/') + '/'

    # 1. Module docstring: <div class="mod-doc">...</div>
    mod_doc_el = soup.find('div', class_='mod-doc')
    module_doc = mod_doc_el.decode_contents().strip() if mod_doc_el else None

    # 2. Find ALL const bindings that have an id (defining sites only).
    #    Usage-site references (like Nat.primeFactors inside a proof)
    #    have data-binding but no id.
    const_map = {}
    bindings = soup.find_all(
        attrs={
            'data-binding': lambda v: v and v.startswith('const-'),
            'id': True,
        }
    )

    for binding in bindings:
        lean_name = binding['data-binding'].removeprefix('const-')
        verso_id = binding['id']

        # Find the enclosing <code class="hl lean"> block
        code_block = binding.find_parent('code', class_='hl')
        doc_html = None

        if code_block:
            # Walk backward from the code block to find the nearest
            # <div class="md-text"> sibling (the docstring).
            prev_md = code_block.find_previous_sibling('div', class_='md-text')

            if prev_md:
                # Ensure this docstring belongs to *this* definition,
                # not an earlier one. Check for any intervening code block
                # that contains a defining-site binding.
                is_immediate = True
                for sibling in prev_md.find_next_siblings('code', class_='hl'):
                    if sibling == code_block:
                        break
                    if sibling.find(
                        attrs={
                            'data-binding': lambda v: v and v.startswith('const-'),
                            'id': True,
                        }
                    ):
                        is_immediate = False
                        break

                if is_immediate:
                    doc_html = prev_md.decode_contents().strip()

        entry = {
            'url': module_path + '#' + verso_id,
            'anchor': verso_id,
        }
        if doc_html:
            entry['docHtml'] = doc_html
        const_map[lean_name] = entry

    return module_path, module_doc, const_map


def main():
    if len(sys.argv) < 3:
        print('Usage: python3 extract_verso_fragments.py <literate-html-dir> <output-json>',
              file=sys.stderr)
        sys.exit(1)

    input_dir, output_json = sys.argv[1], sys.argv[2]

    if not os.path.isdir(input_dir):
        print(f'  Warning: {input_dir} not found, writing empty fragments.', file=sys.stderr)
        os.makedirs(os.path.dirname(output_json), exist_ok=True)
        with open(output_json, 'w') as f:
            json.dump({'moduleDocs': {}, 'constLinks': {}}, f)
        return

    html_files = list(walk_html_files(input_dir))
    print(f'  Scanning {len(html_files)} Verso HTML files...')

    module_docs = {}
    const_links = {}

    for html_file in html_files:
        module_path, module_doc, const_map = extract_from_html(html_file, input_dir)
        if module_doc:
            module_docs[module_path] = module_doc
        const_links.update(const_map)

    output = {
        'moduleDocs': module_docs,
        'constLinks': const_links,
    }
    os.makedirs(os.path.dirname(output_json), exist_ok=True)
    with open(output_json, 'w') as f:
        json.dump(output, f)

    file_size = os.path.getsize(output_json)
    with_doc = sum(1 for v in const_links.values() if v.get('docHtml'))
    print(f'  Extracted {len(module_docs)} module docstrings, '
          f'{len(const_links)} constants ({with_doc} with docstrings).')
    print(f'  Output: {file_size / 1024:.0f} KB')


if __name__ == '__main__':
    main()
