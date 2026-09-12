"""Human output, source isolation and machine contracts share the same operations."""
import contextlib
import io
import json
import os
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from rich.console import Console
from conjectures import catalog, catalog_data, cli, core, interface, onboarding, presentation, ui
import unittest
import test_catalog
import test_cli
from test_toolkit import ToolkitFixture
native=test_catalog.native


class TerminalUXTests(ToolkitFixture):
    invoke=test_cli.CLITests.invoke

    def test_output_options_anywhere_leave_witness_opaque(self):
        args=interface.parse(['review','exec','run','--color=never','--quiet','--verbose','--pager','--','echo','--color','always'])
        self.assertEqual(args.color,'never');self.assertTrue(args.quiet);self.assertTrue(args.verbose)
        self.assertEqual(args.arguments,['echo','--color','always'])
        self.assertIn('Browse',interface.parser().format_help())
        self.assertIn('Prove and evaluate',interface.parser().format_help())
        self.assertIn('--catalog-url',interface.complete(['show','--catalog']))

    def test_rich_table_wraps_without_losing_identifiers(self):
        name='Example.'+'long_declaration_component_'*8
        value={'problems':[{'theorem':name,'module':'FormalConjectures.Example','category':'research open'}]}
        stream=io.StringIO();out=Console(file=stream,width=44,color_system=None,force_terminal=True)
        out.print(presentation.rich_table(['Declaration'],[[name]]))
        self.assertIn(name,''.join(stream.getvalue().split()))
        self.assertNotIn('…',stream.getvalue())
        self.assertIn(name,presentation.render(value,SimpleNamespace(command='find')))

    def test_show_shared_sources_once_and_preserves_lean(self):
        data=native();p=data['problems'][0]
        value={'problems':[p,{**p,'theorem':'Other.variant'}],'moduleDocstrings':data['moduleDocstrings']}
        args=SimpleNamespace(command='show')
        plain=presentation.render(value,args)
        self.assertEqual(plain.count('Source https://example.org/92'),1)
        stream=io.StringIO();Console(file=stream,width=70).print(presentation.rich_view(value,args))
        self.assertEqual(stream.getvalue().count('Source https://example.org/92'),1)
        self.assertIn('∀ n : ℕ, n = n',stream.getvalue())

    def test_color_no_color_and_literal_source_markup(self):
        value={'message':'[bold red]literal[/bold red]\x1b[31m unsafe'}
        args=interface.parse(['doctor','--color','always'])
        for disabled in (False,True):
            stream=io.StringIO()
            with patch.dict(os.environ,{},clear=True),contextlib.redirect_stdout(stream):
                if disabled:os.environ['NO_COLOR']='1'
                ui.output(value,args)
            self.assertIn('[bold red]literal[/bold red]',stream.getvalue())
            self.assertNotIn('\x1b[31m unsafe',stream.getvalue())
            if disabled:self.assertNotIn('\x1b',stream.getvalue())
        args=interface.parse(['doctor','--color','never'])
        with contextlib.redirect_stdout(stream):ui.output(value,args)

    def test_json_progress_and_quiet_have_clean_stdout(self):
        def operation(args):
            ui.stage('Building fixture')
            return {'outcome':'pass','message':'complete'}
        with patch.object(cli,'dispatch',side_effect=operation):
            code,out,err=self.invoke('doctor','--json')
            self.assertEqual(json.loads(out)['exit_code'],0);self.assertIn('Working:',err);self.assertNotIn('\x1b',err)
            code,out,err=self.invoke('doctor','--json','--quiet')
            self.assertEqual(json.loads(out)['exit_code'],0);self.assertEqual(err,'')

    def test_failure_and_interrupt_do_not_leave_spinner(self):
        for error,expected in [(core.Failure('missing','Install the required tool.',4),4),(KeyboardInterrupt(),5)]:
            def operation(args):
                ui.stage('Checking fixture');raise error
            with patch.object(cli,'dispatch',side_effect=operation):
                code,out,err=self.invoke('doctor','--json')
            self.assertEqual(code,expected);self.assertEqual(json.loads(out)['exit_code'],expected)
            self.assertIn('Stopped:',err);self.assertIsNone(ui._current.get())

    def test_errors_lead_with_remedy_without_losing_json_reason(self):
        with patch.object(cli,'dispatch',side_effect=core.Failure('missing','Install the required tool.',4)):
            code,out,err=self.invoke('doctor')
            self.assertEqual(code,4);self.assertEqual(out,'');self.assertIn('Install the required tool.',err)
            self.assertNotIn('missing:',err)
            _,out,_=self.invoke('doctor','--json');self.assertEqual(json.loads(out)['reason'],'missing')

    def test_pager_only_for_explicit_interactive_human_output(self):
        args=interface.parse(['status','--pager'])
        out=Console(file=io.StringIO(),force_terminal=True)
        with patch.object(ui,'console',return_value=out),patch('sys.stdin.isatty',return_value=True),patch.object(out,'pager') as pager:
            ui.output({'message':'fixture'},args);pager.assert_called_once()
        out=Console(file=io.StringIO(),force_terminal=False)
        with patch.object(ui,'console',return_value=out),patch.object(out,'pager') as pager:
            ui.output({'message':'fixture'},args);pager.assert_not_called()

    def test_logged_build_retains_output_and_quiet_hides_progress(self):
        import sys
        path=self.root/'build.log'
        args=interface.parse(['doctor','--quiet'])
        err=io.StringIO()
        with contextlib.redirect_stderr(err),ui.session(args):
            core.logged_command([sys.executable,'-c','print("build diagnostic")'],path)
        self.assertEqual(err.getvalue(),'')
        self.assertIn('build diagnostic',path.read_text())

    def test_always_color_works_with_dumb_term_without_styling_json(self):
        stream=io.StringIO()
        with patch.dict(os.environ,{'TERM':'dumb'},clear=True),contextlib.redirect_stdout(stream):
            ui.output({'next_action':'conjectures status'},interface.parse(['status','--color','always']))
        self.assertIn('\x1b[',stream.getvalue())
        with patch.object(cli,'dispatch',return_value={'outcome':'pass'}):
            code,out,_=self.invoke('doctor','--json','--color','always')
        self.assertEqual(code,0);self.assertNotIn('\x1b',out);json.loads(out)

    def test_never_color_disables_styles_on_a_terminal(self):
        class Terminal(io.StringIO):
            def isatty(self):return True
        stream=Terminal()
        with contextlib.redirect_stdout(stream):
            ui.output({'next_action':'conjectures status'},interface.parse(['status','--color','never']))
        self.assertNotIn('\x1b',stream.getvalue())

    def test_incomplete_preparation_does_not_claim_ready(self):
        args=SimpleNamespace(command='review')
        value={'status':'awaiting_review','build_status':'fail','source_coverage':'available'}
        self.assertIn('needs attention',presentation.render(value,args))
        value['build_status']='pass'
        self.assertIn('Prepared — semantic review pending',presentation.render(value,args))


class CatalogSelectionTests(unittest.TestCase):
    setUp=test_catalog.CatalogTests.setUp
    fetch=test_catalog.CatalogTests.fetch

    fork='https://example.org/fork/data/conjectures.json'

    def fetch_fork(self):
        data=native();data['provenance']['source']['repository']='fork/fc';data['provenance']['extractor']['repository']='fork/fc'
        raw=catalog_data.encode(data);descriptor=catalog_data.encode(catalog_data.manifest(data,raw))
        with patch.object(catalog,'read_url',side_effect=[descriptor,raw]) as network:
            result=catalog.load(None,url=self.fork)
        self.assertEqual(network.call_args_list[0].args[0],'https://example.org/fork/data/catalog-manifest.json')
        return result

    def test_sources_have_separate_caches_and_do_not_fallback(self):
        self.fetch();self.fetch_fork()
        with patch.object(catalog,'read_url',side_effect=AssertionError('network')):
            self.assertEqual(catalog.load(None,offline=True)['provenance']['source']['repository'],'owner/fc')
            self.assertEqual(catalog.load(None,offline=True,url=self.fork)['provenance']['source']['repository'],'fork/fc')
            with self.assertRaises(core.Failure):catalog.load(None,offline=True,url='https://other.org/conjectures.json')

    def test_integrity_failure_does_not_substitute_stale_cache(self):
        self.fetch_fork()
        with patch.object(catalog,'read_url',return_value=b'{"catalog":"wrong.json"}'):
            with self.assertRaises(core.Failure) as failure:catalog.load(None,url=self.fork,refresh=True)
        self.assertEqual(failure.exception.reason,'catalog_invalid')
        self.assertEqual(catalog.load(None,url=self.fork,offline=True)['catalog_origin']['state'],'offline')

    def test_invalid_urls_and_conflicting_source_flags(self):
        for url in ['http://example.org/conjectures.json','https://user:secret@example.org/conjectures.json',
                    'https://example.org/wrong.json','https://example.org/conjectures.json?q=x',42]:
            with self.subTest(url=url),self.assertRaises(core.Failure):catalog.catalog_url(url)
        with self.assertRaises(core.Failure):catalog.load(None,self.root/'data.json',url=self.fork)

    def test_setup_validates_before_saving_and_preserves_configuration(self):
        path=self.root/'settings/config.json';core.save(path,{'limits':{'scratch_calls':7}})
        args=SimpleNamespace(operation='catalog',url=self.fork,global_config=True)
        result=self.fetch_fork()
        with patch.object(onboarding,'config_path',return_value=path),patch.object(catalog,'load',return_value=result):
            onboarding.setup(None,args)
        self.assertEqual(json.loads(path.read_text()),{'limits':{'scratch_calls':7},'catalog_url':self.fork})
        before=path.read_bytes()
        with patch.object(onboarding,'config_path',return_value=path),patch.object(catalog,'load',side_effect=core.Failure('catalog_invalid','invalid',4)):
            with self.assertRaises(core.Failure):onboarding.setup(None,args)
        self.assertEqual(path.read_bytes(),before)

