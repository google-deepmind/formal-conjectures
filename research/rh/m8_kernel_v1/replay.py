"""Exact-source M8 replay. The one-line compatibility patch is explicit, never hidden."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

BASE = 'e279d5765b2dc0cb8b4ec4f62b8db96b4dc69121'
AEGIS = '2c3d041b633147ec97c7ef753aa9d157a47bb9f5'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
WORKFLOW_BLOB = 'c29025bd1fcc7f6c851e04b079fadae16b70d1ec'
ORIGINAL_BLOB = 'eaec6e0ebd43e5b528b2eea0bb05a1ffa93cd51c'
PATCHED_BLOB = '5c39770f4cf027f785928a104c3025f4ba34207c'
TARGET = 'AEGISOverlay.RHKreinM8AnalyticV1'
UPSTREAM = ['AEGISOverlay.RHKreinExplicitCorrectionV1', 'AEGISOverlay.RHKreinM8CertificateV1',
            'AEGISOverlay.RHKreinCorrectionTaylorBridgeV1', 'AEGISOverlay.RHKreinSplineL1NormV1']
E = Path('evidence-m8-kernel')

def blob(b: bytes) -> str:
    return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()

def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

def source_code(text: str) -> str:
    out=[]; i=0; depth=0; string=False
    while i<len(text):
        pair=text[i:i+2]; c=text[i]
        if depth:
            if pair=='/-': depth+=1; i+=2; continue
            if pair=='-/': depth-=1; i+=2; continue
            out.append('\n' if c=='\n' else ' '); i+=1; continue
        if string:
            if c=='\\': out.extend('  '); i+=2; continue
            if c=='"': string=False
            out.append('\n' if c=='\n' else ' '); i+=1; continue
        if pair=='/-': depth=1; i+=2; out.append(' '); continue
        if pair=='--':
            j=text.find('\n',i); i=len(text) if j<0 else j; continue
        if c=='"': string=True; out.append(' '); i+=1; continue
        out.append(c); i+=1
    if depth or string: raise ValueError('unterminated source comment/string')
    return ''.join(out)

def imports(text: str) -> list[str]:
    result=[]
    for line in source_code(text).splitlines():
        m=re.match(r'^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(.*)$',line)
        if m:
            for name in m.group(1).split():
                if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',name): raise ValueError('unsupported import '+name)
                result.append(name)
    return result

def axiom_probes(source: str) -> list[tuple[str, str]]:
    # Resolve only explicit namespace/section scopes, never open declarations
    # or arbitrary suffixes. Unsupported scope syntax fails closed.
    scopes=[]; probes=[]; namespace=''
    identifier=r'[A-Za-z_][A-Za-z_0-9.]*'
    for line in source.splitlines():
        line=line.strip()
        scope=re.fullmatch(r'(namespace|(?:noncomputable\s+)?section)(?:\s+('+identifier+r'))?',line)
        if scope:
            kind,label=scope.groups()
            if kind=='namespace' and label is None: raise ValueError('unnamed namespace')
            scopes.append((label,namespace))
            if kind=='namespace': namespace='.'.join(x for x in (namespace,label) if x)
        elif re.match(r'(?:namespace|(?:noncomputable\s+)?section)\b',line):
            raise ValueError('unsupported namespace/section syntax')
        elif re.match(r'end\b',line):
            end=re.fullmatch(r'end(?:\s+('+identifier+r'))?',line)
            if end is None or not scopes: raise ValueError('unmatched scope end')
            label,previous=scopes.pop()
            if end.group(1) is not None and end.group(1)!=label: raise ValueError('scope end mismatch')
            namespace=previous
        elif line.startswith('#print axioms'):
            probe=re.fullmatch(r'#print axioms\s+('+identifier+r')',line)
            if probe is None: raise ValueError('unsupported axiom probe')
            name=probe.group(1)
            resolved=namespace+'.'+name if namespace and '.' not in name else name
            probes.append((name,resolved))
    if (len(probes)!=len({name for name,_ in probes}) or
            len(probes)!=len({resolved for _,resolved in probes})):
        raise ValueError('duplicate source axiom probe')
    return probes

def audit(source: str, log: str, module_name: str | None = None) -> int:
    source=source_code(source)
    probes=axiom_probes(source)
    if re.search(r'sorryAx|\berror(?:\([^)]*\))?:',log): raise ValueError('compiler error or placeholder')
    flat=re.sub(r'\s+',' ',log)
    allowed={'propext','Classical.choice','Quot.sound'}
    for name,resolved in probes:
        patterns=[re.escape(spelling) for spelling in dict.fromkeys((name,resolved))]
        leaf=name.rsplit('.',1)[-1]
        private=re.search(r'\bprivate\s+(?:noncomputable\s+)?(?:theorem|lemma|def|opaque)\s+'
                          +re.escape(leaf)+r'\b',source)
        if module_name is not None and private:
            patterns.append(re.escape('_private.'+module_name)+r'\.[0-9]+\.'+re.escape(resolved))
        spelling='(?:'+'|'.join(patterns)+')'
        matches=re.findall("'"+spelling+r"' depends on axioms: \[([^\]]*)\]",flat)
        zero=len(re.findall("'"+spelling+"' does not depend on any axioms",flat))
        if len(matches)+zero!=1: raise ValueError('missing/duplicate probe '+name)
        if matches and not {x.strip() for x in matches[0].split(',') if x.strip()}<=allowed:
            raise ValueError('nonstandard axiom '+name)
    return len(probes)

def patched_correction(b: bytes) -> bytes:
    if blob(b)!=ORIGINAL_BLOB: raise ValueError('correction source pin mismatch')
    old=b'  change HasCompactSupport (\xe2\x88\x91 i, f i)\n'
    new=b'  rw [\xe2\x86\x90 Finset.sum_fn]\n'
    if b.count(old)!=1: raise ValueError('patch occurrence count')
    result=b.replace(old,new)
    if blob(result)!=PATCHED_BLOB: raise ValueError('patched blob mismatch')
    return result

def shell_block(text: str, name: str) -> str:
    key='      - name: '+name+'\n'
    if text.count(key)!=1: raise ValueError('missing/duplicate workflow step '+name)
    tail=text.split(key,1)[1]
    if '        run: |\n' not in tail.split('      - name:',1)[0]: raise ValueError('missing shell block')
    lines=tail.split('        run: |\n',1)[1].splitlines()
    block=[]
    for line in lines:
        if line and not line.startswith('          '): break
        block.append(line[10:] if line else '')
    return '\n'.join(block).rstrip()+'\n'

def command(args: list[str], log: Path, good: bool=True) -> subprocess.CompletedProcess:
    log.parent.mkdir(parents=True,exist_ok=True)
    p=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    log.write_text(p.stdout)
    print(p.stdout,flush=True)
    if good and p.returncode: raise RuntimeError(f'{args} exited {p.returncode}; {log}')
    return p

def provider() -> None:
    p=Path('.baseline/.github/workflows/rh-snowflake-log23-globalization-v1.yml')
    b=p.read_bytes()
    if blob(b)!=WORKFLOW_BLOB: raise ValueError('provider workflow pin')
    code=shell_block(b.decode(),'Build exact LiCriterion provider for Krein closure')
    E.mkdir(exist_ok=True); (E/'provider-build.sh').write_text(code)
    command(['bash','-euo','pipefail',str(E/'provider-build.sh')],E/'provider.log')

class Builder:
    def __init__(self):
        self.done=set(); self.active=set(); self.records=[]
    def origin(self,name: str):
        rel=Path(*name.split('.')).with_suffix('.lean')
        if name.split('.')[0] in {'Mathlib','Batteries','Aesop','Qq','Plausible','Lean','Init','Std','ImportGraph','ProofWidgets','LeanSearchClient'}:
            return None
        if name.split('.')[0] in {'Lc','Hadamard','FunctionsOfOneComplexVariable'}:
            if not rel.exists(): raise ValueError('missing provider source '+name)
            return None
        if name==TARGET:
            return Path('research/rh/m8_kernel_v1/RHKreinM8AnalyticV1.lean')
        p=Path('.baseline')/rel
        if p.exists(): return p
        if '.' not in name:
            p=Path('.baseline/AEGISOverlay')/(name+'.lean')
            if p.exists(): return p
            p=Path('.aegis/sovereign-omega-v2/formal/bridges/lean')/(name+'.lean')
            if p.exists(): return p
        raise ValueError('unresolved local import '+name)
    def build(self,name: str):
        if name in self.done: return
        origin=self.origin(name)
        if origin is None: return
        if name in self.active: raise ValueError('import cycle '+name)
        self.active.add(name)
        original=origin.read_bytes(); data=original
        deps=imports(original.decode())
        for dep in deps: self.build(dep)
        rel=Path(*name.split('.')).with_suffix('.lean')
        out=Path('.lake/build/lib/lean')/rel.with_suffix('.olean')
        rel.parent.mkdir(parents=True,exist_ok=True); out.parent.mkdir(parents=True,exist_ok=True)
        stem=name.replace('.','_')
        if name=='AEGISOverlay.RHKreinExplicitCorrectionV1':
            rel.write_bytes(original); out.unlink(missing_ok=True)
            red=command(['lake','env','lean','-o',str(out),str(rel)],E/(stem+'-red.log'),False)
            if red.returncode==0 or "'change' tactic failed" not in red.stdout or 'sorryAx' not in red.stdout:
                raise ValueError('expected exact compact-support red baseline missing')
            out.unlink(missing_ok=True); data=patched_correction(original)
        rel.write_bytes(data)
        log=E/(stem+'.log')
        command(['lake','env','lean','-o',str(out),str(rel)],log)
        count=audit(data.decode(),log.read_text(),module_name=name)
        if not out.exists() or out.stat().st_size==0: raise ValueError('missing olean '+name)
        dep_log=E/(stem+'-deps.log')
        command(['lake','env','lean','--deps',str(rel)],dep_log)
        (E/'sources'/rel).parent.mkdir(parents=True,exist_ok=True); (E/'sources'/rel).write_bytes(data)
        (E/'oleans'/rel.with_suffix('.olean')).parent.mkdir(parents=True,exist_ok=True)
        (E/'oleans'/rel.with_suffix('.olean')).write_bytes(out.read_bytes())
        self.records.append({'module':name,'origin':str(origin),'original_git_blob':blob(original),
            'compiled_git_blob':blob(data),'source_sha256':sha(data),'olean_sha256':sha(out.read_bytes()),
            'imports':deps,'axiom_probes':count,'log_sha256':sha(log.read_bytes()),'deps_sha256':sha(dep_log.read_bytes())})
        self.active.remove(name); self.done.add(name)
    def save(self):
        (E/'local-closure.json').write_text(json.dumps(self.records,indent=2)+'\n')

def upstream():
    for path,pin in [('.baseline',BASE),('.aegis',AEGIS),('.lake/packages/mathlib',MATHLIB)]:
        actual=subprocess.check_output(['git','-C',path,'rev-parse','HEAD'],text=True).strip()
        if actual!=pin: raise ValueError('checkout mismatch '+path)
    E.mkdir(exist_ok=True)
    b=Builder()
    try:
        for name in UPSTREAM: b.build(name)
    finally: b.save()
    p=Path('M8AbsentProbe.lean')
    p.write_text('import AEGISOverlay.RHKreinCorrectionTaylorBridgeV1\n#check AEGIS.RHKreinM8AnalyticV1.correctionSymbol_eighth_abs_le_serialized\n')
    red=command(['lake','env','lean',str(p)],E/'absent-theorem.log',False)
    if red.returncode==0 or 'Unknown identifier' not in red.stdout and 'unknownIdentifier' not in red.stdout:
        raise ValueError('absent-theorem red baseline not observed')
    (E/'upstream-status.json').write_text(json.dumps({'status':'UPSTREAM_PATCH_REPLAY_PASS','new_m8_proven':False,
        'baseline':BASE,'patch_blob':PATCHED_BLOB,'local_modules':len(b.records),'authority_effect':'NONE'})+'\n')

def candidate():
    # The preceding upstream step has freshly built every dependency for this run.
    records=json.loads((E/'local-closure.json').read_text())
    b=Builder(); b.records=records; b.done={r['module'] for r in records}
    b.build(TARGET); b.save()
    log=E/(TARGET.replace('.','_')+'.log')
    source=Path('research/rh/m8_kernel_v1/RHKreinM8AnalyticV1.lean').read_text()
    if audit(source,log.read_text())<1: raise ValueError('candidate lacks probes')
    head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
    receipt={'status':'PASS_PATCHED_BASELINE_AND_M8_PRODUCER','head':head,'baseline':BASE,'aegis':AEGIS,'mathlib':MATHLIB,
        'correction_original_blob':ORIGINAL_BLOB,'correction_patched_blob':PATCHED_BLOB,'RH_PROVEN':False,
        'authority_effect':'NONE','pure_pr51_replay':False,
        'files':{str(p.relative_to(E)):sha(p.read_bytes()) for p in sorted(E.rglob('*')) if p.is_file() and p.name!='receipt.json'}}
    (E/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('phase',choices=['provider','upstream','candidate'])
    globals()[ap.parse_args().phase]()
