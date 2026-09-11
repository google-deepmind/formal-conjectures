#!/usr/bin/env python3
"""Render copyable versioned fork release instructions; no publishing side effects."""
import re
import sys


def notes(tag,repo):
    if not re.fullmatch(r'toolkit-v[0-9]+\.[0-9]+\.[0-9]+(?:rc[0-9]+)?',tag):raise ValueError('Expected toolkit-vVERSION')
    if repo!='williamjblair/formal-conjectures':raise ValueError('Only the qualification fork is enabled')
    version=tag.removeprefix('toolkit-v')
    url=f'https://github.com/{repo}/releases/download/{tag}/formal_conjectures_toolkit-{version}-py3-none-any.whl'
    return f'''Fork release candidate {version}. Upstream adoption and complete release qualification remain separate.

Try without permanent installation:

```sh
uvx --python 3.11 --from {url} conjectures doctor
```

Install:

```sh
uv tool install --python 3.11 {url}
conjectures find erdos/730 --catalog-url https://williamjblair.github.io/formal-conjectures/data/conjectures.json
conjectures show erdos/730 --catalog-url https://williamjblair.github.io/formal-conjectures/data/conjectures.json
```

See [the usage guide](https://github.com/{repo}/blob/{tag}/toolkit/README.md) for review setup and [the qualification checklist](https://github.com/{repo}/blob/{tag}/toolkit/RELEASE.md) for current limits. Checksums are in SHA256SUMS.

The examples explicitly select the deployed fork. Default browsing requires upstream #5375 and its catalog deployment; there is no automatic fork fallback.

The CLI uses existing agent sessions and has no model login or launcher. Human-readable output, structured JSON, review drafts, run inspection, setup, and bounded waiting are included. Proof verification and evidence publication remain experimental until their real acceptance journeys are recorded. Deterministic tests and installation success do not establish mathematical review accuracy.
'''

if __name__=='__main__':print(notes(*sys.argv[1:]))
