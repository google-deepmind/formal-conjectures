"""Command contracts exercised without model calls or external services."""
import contextlib
import io
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
from conjectures import cli, core, interface, inspection, onboarding, catalog
from test_toolkit import ToolkitFixture


class CLITests(ToolkitFixture):
    def test_native_catalog_preferred_and_projection_fallback_only_on_404(self):
        native={'schemaVersion':2,'problems':[]}
        with patch.object(catalog,'user_cache',return_value=self.root/'native'),patch.object(catalog.urllib.request,'urlopen',return_value=io.BytesIO(json.dumps(native).encode())) as network:
            self.assertEqual(catalog.load(None),native)
            self.assertEqual(network.call_args.args[0],catalog.NATIVE_URL)
        missing=catalog.urllib.error.HTTPError(catalog.NATIVE_URL,404,'missing',{},None)
        with patch.object(catalog,'user_cache',return_value=self.root/'fallback'),patch.object(catalog.urllib.request,'urlopen',side_effect=[missing,io.BytesIO(b'{"conjectures":[]}')]):
            self.assertEqual(catalog.load(None)['projection'],'website')
        denied=catalog.urllib.error.HTTPError(catalog.NATIVE_URL,403,'denied',{},None)
        with patch.object(catalog,'user_cache',return_value=self.root/'denied'),patch.object(catalog.urllib.request,'urlopen',side_effect=denied) as network:
            with self.assertRaises(catalog.urllib.error.HTTPError):catalog.load(None)
            self.assertEqual(network.call_count,1)

    def invoke(self,*args):
        out=io.StringIO();err=io.StringIO()
        with contextlib.redirect_stdout(out),contextlib.redirect_stderr(err):
            try:code=cli.main(list(args))
            except SystemExit as e:code=e.code
        return code,out.getvalue(),err.getvalue()

    def test_no_checkout_help_version_and_doctor(self):
        with patch.object(Path,'cwd',return_value=self.root),patch.object(onboarding,'probe',return_value=False),patch.object(core,'config_path',return_value=self.root/'config.json'):
            self.assertEqual(self.invoke()[0],0)
            code,out,_=self.invoke('--version','--json');self.assertEqual(code,0);self.assertIn('version',json.loads(out))
            code,out,_=self.invoke('doctor','--json');self.assertEqual(code,0);self.assertEqual(json.loads(out)['capabilities']['browse']['status'],'ready')
            self.assertEqual(self.invoke('doctor','--for','verify','--json')[0],4)

    def test_browse_catalog_outside_checkout_and_readable_output(self):
        path=self.root/'catalog.json';core.save(path,{'schemaVersion':2,'problems':[{'theorem':'Example.a','module':'FormalConjectures.Example','statement':'∀ n : Nat, n = n'}]})
        with patch.object(Path,'cwd',return_value=self.root),patch.object(core,'config_path',return_value=self.root/'config.json'):
            code,out,_=self.invoke('show','Example.a','--catalog',str(path));self.assertEqual(code,0);self.assertIn('∀ n',out);self.assertFalse(out.startswith('{'))
            code,out,_=self.invoke('find','missing','--catalog',str(path),'--json');self.assertEqual(code,0);self.assertEqual(json.loads(out)['problems'],[])

    def test_global_flags_and_witness_arguments(self):
        args=interface.parse(['review','exec','RUN','--files','some path','--json','--repo',str(self.root),'--','echo','--json','--repo','private'])
        self.assertEqual(args.arguments,['echo','--json','--repo','private']);self.assertTrue(args.json)
        self.assertEqual(args.files,Path('some path'));self.assertEqual(args.repo,self.root)
        args=interface.parse(['review','--pr','4941']);self.assertEqual(args.operation,'prepare')

    def test_json_argument_errors(self):
        code,out,err=self.invoke('--json','review','prepare','--pr','not-a-number')
        self.assertEqual(code,2);self.assertEqual(json.loads(out)['reason'],'invalid_arguments');self.assertEqual(err,'')

    def test_run_selection_and_read_failure_exit(self):
        self.repository()
        directory,record=core.start_run(self.root,'check');core.finish(directory,record,'fail')
        self.assertEqual(core.run_dir(self.root,'latest',readonly=True),directory)
        with self.assertRaises(core.Failure):core.run_dir(self.root,'latest')
        self.assertEqual(core.run_dir(self.root,record['id'][:-2]),directory)
        core.start_run(self.root,'check')
        with self.assertRaises(core.Failure) as e:core.run_dir(self.root,record['id'][:8])
        self.assertEqual(e.exception.reason,'ambiguous_run')
        with patch.object(core,'config_path',return_value=self.root/'cfg'):
            code,out,_=self.invoke('--repo',str(self.root),'run','show',record['id'],'--json')
        self.assertEqual(code,0);self.assertEqual(json.loads(out)['outcome'],'fail')

    def test_operation_success_is_separate_from_review_outcome(self):
        args=SimpleNamespace(command='review',operation='prepare')
        result={'outcome':'incomplete','status':'awaiting_review','build_status':'pass','target':{'source_collection':{'coverage':'available'}}}
        self.assertEqual(cli.operation_code(args,result),0)
        for state,code in [('not_run',4),('fail',1),('error',3)]:
            self.assertEqual(cli.operation_code(args,{**result,'build_status':state}),code)
        result['target']['source_collection']['coverage']='incomplete';self.assertEqual(cli.operation_code(args,result),4)
        self.assertEqual(cli.operation_code(SimpleNamespace(command='verify'),{'outcome':'incomplete','status':'queued'}),0)

    def test_noop_and_shared_check_scope(self):
        self.assertEqual(inspection.check_local(self.root,['README.md'],{})['reason'],'no_changed_modules')
        with self.assertRaises(core.Failure) as e:inspection.check_local(self.root,['lakefile.toml'],{})
        self.assertIn('lake --wfail',str(e.exception));self.assertEqual(e.exception.code,4)

    def test_logs_have_contents_and_reject_escape(self):
        directory,record=core.start_run(self.root,'check');(directory/'build.log').write_text('Lean build failed\n')
        value=inspection.logs(directory,record);self.assertIn('Lean build failed',value['logs'][0]['text'])
        with self.assertRaises(ValueError):inspection.logs(directory,record,'../secret')
        (directory/'link.log').symlink_to('/etc/passwd')
        with self.assertRaises(core.Failure):inspection.logs(directory,record,'link.log')

    def test_terminal_controls_removed(self):
        from conjectures.presentation import clean
        self.assertEqual(clean('hello\x1b[31mred\x1b[0m\rworld'),'helloredworld')

    def test_missing_catalog_does_not_download(self):
        with patch.object(catalog.urllib.request,'urlopen') as network:
            with self.assertRaises(core.Failure):catalog.load(None,self.root/'absent.json')
        network.assert_not_called()

    def test_setup_preserves_configuration_and_uses_recorded_digest(self):
        self.repository();core.save(core.config_path(self.root),{'limits':{'scratch_calls':8},'evidence':{'repository':'a/b','branch':'data'}})
        args=SimpleNamespace(operation='review',source_ref='main',image=None,global_config=False)
        digest='sha256:'+'a'*64
        with patch.object(onboarding,'review_image',return_value=(digest,{'image':digest})):
            onboarding.setup(self.root,args)
        saved=json.loads(core.config_path(self.root).read_text());self.assertEqual(saved['image'],digest);self.assertEqual(saved['limits']['scratch_calls'],8)

    def test_setup_refuses_untrusted_build_source(self):
        with patch.object(onboarding,'probe',return_value=True),patch.object(onboarding,'github',side_effect=[{'sha':'a'*40},{'status':'diverged'}]):
            with self.assertRaises(core.Failure) as e:onboarding.review_image('candidate')
        self.assertEqual(e.exception.reason,'untrusted_source')

    def test_shell_completion_generated_from_parser(self):
        self.assertIn('prepare',interface.complete(['review','p']))
        self.assertIn('--report',interface.complete(['review','finish','--r']))
        self.assertIn('complete -F',interface.completion('bash'))
        self.assertIn('compdef',interface.completion('zsh'))
        self.assertIn('complete -c',interface.completion('fish'))

if __name__=='__main__':unittest.main()
