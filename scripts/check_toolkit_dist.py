#!/usr/bin/env python3
"""Test the actual wheel outside a checkout and without provider credentials."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import zipfile


def check(wheel):
    with zipfile.ZipFile(wheel) as archive:
        names=archive.namelist()
        assert 'conjectures/resources/review/SKILL.md' in names
        assert 'conjectures/resources/agent-skill/SKILL.md' in names
        if 'conjectures/evaluation.py' in names:
            assert 'conjectures/resources/schemas/proof-suite-v1.schema.json' in names
        assert 'conjectures/resources/review.Dockerfile' in names
        for schema in ('catalog-v2', 'catalog-manifest-v1', 'website-rendering-v1'):
            assert f'conjectures/resources/schemas/{schema}.schema.json' in names
        assert 'conjectures/resources/verification-workflow.yml' in names
        if 'conjectures/publisher.py' in names:
            assert 'conjectures/resources/publisher-workflow.yml' in names
        assert not any('/evals/' in name or 'review_model_' in name for name in names)
        if 'conjectures/proof.py' in names:
            for name in ('ExportProblem.lean','WorkspaceTest.lean','export_problem.py'):
                assert 'conjectures/resources/exporter/'+name in names
    with tempfile.TemporaryDirectory(prefix='fc-install-') as temp:
        root=Path(temp);env={k:v for k,v in os.environ.items() if k not in ('PYTHONPATH','OPENAI_API_KEY','ANTHROPIC_API_KEY','GH_TOKEN','GITHUB_TOKEN','CONJECTURES_GH')}
        env.update(XDG_CONFIG_HOME=str(root/'config'),XDG_CACHE_HOME=str(root/'cache'),GH_CONFIG_DIR=str(root/'gh'))
        subprocess.run(['uv','venv','--python',sys.executable,str(root/'venv')],check=True,env=env)
        python=root/'venv/bin/python';exe=root/'venv/bin/conjectures'
        subprocess.run(['uv','pip','install','--python',str(python),str(wheel)],check=True,env=env)
        catalog=root/'catalog.json';catalog.write_text(json.dumps({'schemaVersion':2,'problems':[{'theorem':'Example.self','module':'FormalConjectures.Example','statement':'∀ n : Nat, n = n'}]}))
        for args in [[],['--help'],['help','review','prepare'],['--version'],['doctor','--json'],['skill','path','--json'],['skill','install','--dir',str(root/'agent skills'),'--json'],['find','Example','--catalog',str(catalog),'--json'],['show','Example.self','--catalog',str(catalog)]]:
            result=subprocess.run([str(exe),*args],cwd=root,env=env,capture_output=True,text=True)
            assert result.returncode==0,(args,result.stdout,result.stderr)
            if '--json' in args:assert json.loads(result.stdout)['command_status']=='success'
            else:assert not result.stdout.startswith('{'),args
            if args[:1]==['show']:assert '∀ n : Nat, n = n' in result.stdout,result.stdout
        subprocess.run([str(python),'-c','import importlib.util; assert importlib.util.find_spec("mcp") is None; from conjectures.review import skill_path; assert (skill_path()/"SKILL.md").is_file()'],cwd=root,env=env,check=True)
    print('Wheel installation, resources, outside-checkout commands, and no-model runtime passed.')

if __name__=='__main__':check(Path(sys.argv[1]).resolve())
