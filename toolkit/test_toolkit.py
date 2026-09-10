"""Deterministic qualification of snapshots, source boundaries, and proof outcomes."""
import copy
import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from conjectures import catalog, core, execution, report, review, sources

class ToolkitFixture(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name).resolve()
    def git(self,*args,**kwargs):
        return subprocess.check_output(['git','-C',str(self.root),*args],**kwargs)
    def repository(self):
        self.git('init','-q');self.git('config','user.name','Fixture');self.git('config','user.email','fixture@invalid')
        (self.root/'FormalConjectures').mkdir();(self.root/'FormalConjectures/A.lean').write_text('theorem original : True := by trivial\n')
        self.git('add','.');self.git('commit','-qm','base')

class ToolkitTests(ToolkitFixture):
    def test_optional_workspace_does_not_require_git(self):
        with patch.object(core,'command',side_effect=FileNotFoundError('git')):
            self.assertIsNone(core.workspace(required=False))
            with self.assertRaises(core.Failure) as caught:core.workspace(required=True)
        self.assertEqual(caught.exception.reason,'missing_tool')

    def test_snapshot_preserves_branch_index_and_worktree(self):
        self.repository();head=self.git('rev-parse','HEAD');before=self.git('ls-files','--stage')
        (self.root/'FormalConjectures/A.lean').write_text('changed\n')
        (self.root/'FormalConjectures/New.lean').write_text('new\n')
        (self.root/'private.txt').write_text('private\n')
        commit,local=review.snapshot(self.root,'HEAD')
        self.assertTrue(local);self.assertEqual(self.git('rev-parse','HEAD'),head)
        self.assertEqual(self.git('ls-files','--stage'),before)
        self.assertEqual(self.git('show',commit+':FormalConjectures/New.lean'),b'new\n')
        self.assertNotIn(b'private.txt',self.git('ls-tree','-r',commit))
        self.assertEqual((self.root/'FormalConjectures/A.lean').read_text(),'changed\n')
    def test_staged_new_problem_is_included(self):
        self.repository();(self.root/'FormalConjectures/New.lean').write_text('new')
        self.git('add','FormalConjectures/New.lean');index=self.git('ls-files','--stage')
        commit,_=review.snapshot(self.root,'HEAD')
        self.assertIn(b'New.lean',self.git('ls-tree','-r',commit));self.assertEqual(index,self.git('ls-files','--stage'))
    def test_scope_rejects_configuration_deletion_and_large_change(self):
        self.repository()
        for scope in [['lakefile.toml'],['FormalConjectures/Deleted.lean'],['FormalConjectures/A.lean']*6,[]]:
            with self.subTest(scope=scope),self.assertRaises(ValueError):execution.build_targets(scope,self.root)
    def test_quoted_module_path_is_preserved(self):
        p=self.root/'FormalConjectures/A.B.lean';p.parent.mkdir();p.write_text('')
        self.assertEqual(execution.build_targets(['FormalConjectures/A.B.lean'],self.root),['«FormalConjectures».«A.B»'])
    def test_unavailable_source_is_incomplete(self):
        with patch.object(sources,'retrieve',side_effect=OSError('unavailable')):
            result=sources.collect(self.root/'sources',[b'https://www.erdosproblems.com/730'])
        self.assertEqual(result['coverage'],'incomplete')
        self.assertEqual(result['records'][0]['url'],'https://www.erdosproblems.com/latex/730')
    def test_no_source_is_incomplete(self):
        self.assertEqual(sources.collect(self.root/'sources',[b'no links'])['coverage'],'incomplete')
    def test_public_source_rejects_private_addresses(self):
        with patch.object(sources.socket,'getaddrinfo',return_value=[(2,1,6,'',('127.0.0.1',80))]):
            with self.assertRaises(ValueError):sources.public_url('http://example.org')
    def test_html_discards_scripts(self):
        p=sources.Text();p.feed('<p>Source</p><script>untrusted()</script>')
        self.assertIn('Source',''.join(p.parts));self.assertNotIn('untrusted',''.join(p.parts))
    def test_shortcut_requires_exact_declaration_for_init(self):
        data={'problems':[{'module':'FormalConjectures.ErdosProblems.«730»','theorem':n} for n in ('Erdos730.main','Erdos730.variant')]}
        self.assertEqual(len(catalog.matches(data,'erdos/730')),2)
        with self.assertRaises(core.Failure) as error:catalog.select(data,'erdos/730')
        self.assertEqual(error.exception.reason,'ambiguous_target')
    def test_run_records_preserve_failure_reason(self):
        path,record=core.start_run(self.root,'review')
        core.finish(path,record,'error',reason='timeout')
        self.assertEqual(core.runs(self.root)[0]['reason'],'timeout')
        with self.assertRaises(core.Failure):core.run_dir(self.root,'../../private')

if __name__=='__main__':unittest.main()
