#!/usr/bin/env python3
"""Reuse published native data for a site preview without rewriting provenance."""
import argparse
from pathlib import Path
import sys
from urllib.request import urlopen
from urllib.parse import urljoin
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'toolkit'))
from conjectures.catalog_data import verify, parse


def download(url, out):
    def read(target,limit):
        with urlopen(target,timeout=30) as response:raw=response.read(limit+1)
        if len(raw)>limit:raise ValueError('Catalog response too large')
        return raw
    descriptor=read(url,1024*1024)
    metadata=parse(descriptor)
    if metadata.get('catalog')!='conjectures.json':raise ValueError('Unexpected catalog filename')
    raw=read(urljoin(url,'conjectures.json'),64*1024*1024)
    verify(metadata,raw)
    # The problem catalog cannot enumerate utility-library source pages.
    # Reuse Verso's complete index from the same published snapshot.
    index=read(urljoin(url,f"rendered/{metadata['sha256']}/modules.json"),4*1024*1024)
    modules=parse(index)
    if not isinstance(modules,dict) or modules.get('schema_version')!='fc.website-modules.v1' or modules.get('catalog_sha256')!=metadata['sha256'] or not isinstance(modules.get('modules'),list) or not modules['modules']:
        raise ValueError('Missing module index or module index belongs to another catalog')
    out.mkdir(parents=True,exist_ok=True)
    (out/'conjectures.json').write_bytes(raw)
    (out/'catalog-manifest.json').write_bytes(descriptor)
    (out/'verso-modules.json').write_bytes(index)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--url',default='https://google-deepmind.github.io/formal-conjectures/data/catalog-manifest.json')
    p.add_argument('--out',type=Path,default=Path('site/data'))
    args=p.parse_args();download(args.url,args.out)
