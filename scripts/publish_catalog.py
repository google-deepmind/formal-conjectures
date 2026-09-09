#!/usr/bin/env python3
"""Prepare a complete, reproducible static catalog; this script does not upload."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'toolkit'))
from conjectures.catalog_data import complete, encode, manifest


def prepare(source, repository, data, out):
    def git(*args):return subprocess.check_output(['git','-C',str(source),*args],text=True).strip()
    scope=['FormalConjectures','FormalConjecturesUtil','FormalConjecturesForMathlib',
           'scripts/extract_names.lean','lakefile.toml','lean-toolchain','lake-manifest.json']
    if git('status','--porcelain','--',*scope):
        raise ValueError('Catalog source or extraction inputs have uncommitted changes')
    revision=git('rev-parse','HEAD')
    data={**data,'provenance':{'source':{'repository':repository,'commit':revision},
        'extractor':{'repository':repository,'commit':revision,'path':'scripts/extract_names.lean'},
        'lean_toolchain':(source/'lean-toolchain').read_text().strip(),
        'dependencies_sha256':hashlib.sha256((source/'lake-manifest.json').read_bytes()).hexdigest(),
        'scope':'FormalConjectures','answer_mode':'postpone'}}
    complete(data)
    raw=encode(data);out.mkdir(parents=True,exist_ok=True)
    (out/'catalog.json').write_bytes(raw)
    (out/'catalog-manifest.json').write_bytes(encode(manifest(data,raw)))
    return data


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path);parser.add_argument('--repository',required=True)
    parser.add_argument('--source',type=Path,default=Path.cwd());parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    data=prepare(args.source,args.repository,json.loads(args.input.read_text()),args.out)
    print(f"Prepared {len(data['problems'])} statements at {data['provenance']['source']['commit']}")
