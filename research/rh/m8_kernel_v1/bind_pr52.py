"""Replay the byte-identical PR52 producer against the patched original PR51 definitions."""
from pathlib import Path
import json
import subprocess
import replay as r

PRODUCER_BLOB='50d60b68282b9f17d25a4f9cacaa50e09ba892dc'
PRODUCER_HEAD='f352135eef3575364922f9fa428fb0af0750185b'
PRODUCER='AEGISOverlay.RHKreinCorrectionM8BoundV1'
ADAPTER='AEGISOverlay.RHKreinCorrectionSymbolV1'
ADAPTER_BYTES=b'/-\nCopyright 2026 The Formal Conjectures Authors.\n\nLicensed under the Apache License, Version 2.0 (the "License");\nyou may not use this file except in compliance with the License.\nYou may obtain a copy of the License at\n\n    https://www.apache.org/licenses/LICENSE-2.0\n\nUnless required by applicable law or agreed to in writing, software\ndistributed under the License is distributed on an "AS IS" BASIS,\nWITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.\nSee the License for the specific language governing permissions and\nlimitations under the License.\n-/\n\nimport AEGISOverlay.RHKreinExplicitCorrectionV1\n'

class ReboundBuilder(r.Builder):
    def origin(self,name):
        if name==PRODUCER:
            p=Path('research/rh/m8_kernel_v1/RHKreinCorrectionM8BoundV1.lean')
            if r.blob(p.read_bytes())!=PRODUCER_BLOB: raise ValueError('PR52 producer pin changed')
            return p
        if name==ADAPTER:
            p=Path('research/rh/m8_kernel_v1/CorrectionSymbolAdapter.lean')
            if p.read_bytes()!=ADAPTER_BYTES: raise ValueError('adapter must only import original definitions')
            return p
        return super().origin(name)

def main():
    records=json.loads((r.E/'local-closure.json').read_text())
    b=ReboundBuilder(); b.records=records; b.done={x['module'] for x in records}
    b.build(r.TARGET); b.save()
    checks={PRODUCER:10,r.TARGET:8}
    for name,count in checks.items():
        src=b.origin(name).read_text();log=(r.E/(name.replace('.','_')+'.log')).read_text()
        if r.audit(src,log)!=count:raise ValueError('endpoint count '+name)
    head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
    receipt={'status':'PASS_ORIGINAL_DEFINITIONS_M8_REBIND_AND_CELL_BRIDGE','head':head,
        'baseline':r.BASE,'aegis':r.AEGIS,'mathlib':r.MATHLIB,'lean':'leanprover/lean4:v4.33.1',
        'reused_producer_head':PRODUCER_HEAD,'reused_producer_blob':PRODUCER_BLOB,
        'correction_original_blob':r.ORIGINAL_BLOB,'correction_compiled_blob':r.PATCHED_BLOB,
        'adapter_git_blob':r.blob(ADAPTER_BYTES),'upstream_source_overlay':'one-line compact-support repair',
        'pure_pr51_replay':False,'RH_PROVEN':False,'authority_effect':'NONE','all_cells_sound_proven':False,
        'files':{str(p.relative_to(r.E)):r.sha(p.read_bytes()) for p in sorted(r.E.rglob('*'))
                 if p.is_file() and p.name!='receipt.json'}}
    (r.E/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')

if __name__=='__main__':main()
