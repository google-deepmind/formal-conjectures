#!/usr/bin/env python3
"""
Extract Verso fragments from literate HTML output.

Produces a compact JSON with:
- modules: [{ name, url }] for every rendered module page, across all libraries
- moduleDocs: module path -> rendered module docstring HTML
- constLinks: Lean const name -> { url, anchor, docHtml }

Usage: python3 extract_verso_fragments.py <literate-html-dir> <output-json> --catalog-dir <catalog-dir>
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import os
import re
import sys

from bs4 import BeautifulSoup

# A module page's <title> is the bare module name, e.g.
# `FormalConjectures.ErdosProblems.«1»`. Anything else (the search page, the
# redirect at the root) is not a module.
MODULE_NAME_RE = re.compile(r'^[A-Za-z_][\w«»\'.]*$')


def walk_html_files(root):
    """Find all index.html files under root."""
    for dirpath, _, filenames in os.walk(root):
        for f in filenames:
            if f == 'index.html':
                yield os.path.join(dirpath, f)


def extract_from_html(html_path, base_dir, hover_docs=None):
    """Extract module doc and const links from a Verso HTML file."""
    with open(html_path, encoding='utf-8') as f:
        soup = BeautifulSoup(f, 'lxml')

    rel = os.path.relpath(os.path.dirname(html_path), base_dir)
    module_path = '/' + rel.replace(os.sep, '/') + '/'

    # 0. Module name, from the page title. The search results page is the one
    #    non-module page with a title that looks like a module name.
    title_el = soup.find('title')
    title = title_el.get_text(strip=True) if title_el else ''
    module_name = title if MODULE_NAME_RE.match(title) and rel != 'search' else None

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
        if code_block:
            entry['codeHtml'] = str(code_block)
            hover_ids = {node['data-verso-hover'] for node in code_block.select('[data-verso-hover]')}
            entry['hoverDocs'] = {key: hover_docs[key] for key in sorted(hover_ids) if key in (hover_docs or {})}
        const_map[lean_name] = entry

    return module_path, module_name, module_doc, const_map


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input_dir', type=Path)
    parser.add_argument('output_json', type=Path)
    parser.add_argument('--catalog-dir', type=Path, required=True,
                        help='Complete catalog generated from this same build')
    args = parser.parse_args()
    input_dir, output_json = args.input_dir, args.output_json
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'toolkit'))
    from conjectures.catalog_data import verify, parse
    raw = (args.catalog_dir / 'catalog.json').read_bytes()
    descriptor = parse((args.catalog_dir / 'catalog-manifest.json').read_bytes())
    catalog = verify(descriptor, raw)
    root = Path(__file__).resolve().parents[1]
    revision = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != catalog['provenance']['source']['commit']:
        parser.error('Verso must be built from the catalog source revision')
    if subprocess.check_output(['git', '-C', str(root), 'status', '--porcelain', '--',
                                'FormalConjectures', 'FormalConjecturesUtil',
                                'FormalConjecturesForMathlib', 'docbuild',
                                'lean-toolchain', 'lake-manifest.json'], text=True).strip():
        parser.error('Verso source and dependency inputs must be committed')
    if not input_dir.is_dir():
        parser.error('Literate HTML is missing; run the Verso build first')
    targets = {entry['theorem'] for entry in catalog['problems']}
    hover_path = input_dir / '-verso-docs.json'
    hover_docs = json.loads(hover_path.read_text()) if hover_path.exists() else {}

    html_files = list(walk_html_files(input_dir))
    print(f'  Scanning {len(html_files)} Verso HTML files...')

    modules = []
    module_docs = {}
    const_links = {}

    for html_file in html_files:
        module_path, module_name, module_doc, const_map = extract_from_html(html_file, input_dir, hover_docs)
        if module_name:
            modules.append({'name': module_name, 'url': module_path})
        if module_doc:
            module_docs[module_path] = module_doc
        const_links.update({name: value for name, value in const_map.items() if name in targets})

    modules.sort(key=lambda m: m['name'])

    if not modules:
        parser.error('No rendered modules found; run the Verso build first')
    output = {
        'catalog_sha256': hashlib.sha256(raw).hexdigest(),
        'modules': modules,
        'moduleDocs': module_docs,
        'constLinks': const_links,
    }
    os.makedirs(os.path.dirname(output_json), exist_ok=True)
    with open(output_json, 'w') as f:
        json.dump(output, f)

    file_size = os.path.getsize(output_json)
    with_doc = sum(1 for v in const_links.values() if v.get('docHtml'))
    print(f'  Extracted {len(modules)} module pages, {len(module_docs)} module docstrings, '
          f'{len(const_links)} constants ({with_doc} with docstrings).')
    print(f'  Output: {file_size / 1024:.0f} KB')


if __name__ == '__main__':
    main()
