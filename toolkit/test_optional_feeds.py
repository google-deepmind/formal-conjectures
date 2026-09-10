import importlib.util
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

class OptionalFeedTests(unittest.TestCase):
    def test_failed_work_feed_is_explicit_and_does_not_prevent_evidence_projection(self):
        path=Path(__file__).resolve().parents[1]/'scripts/contribution_context.py'
        spec=importlib.util.spec_from_file_location('context_build',path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        saved={}
        with patch.dict(os.environ,{'FC_WORK_CONTEXT_URL':'https://example.invalid/work.json'}),patch.object(module,'read_url',side_effect=OSError('offline')),patch.object(module,'load',return_value={'status':'not_configured','runs':[]}),patch.object(module,'save',side_effect=lambda p,v:saved.update({str(p):v})):
            module.main()
        self.assertEqual(saved['site/data/work.json']['status'],'unavailable')
        self.assertEqual(saved['site/data/evidence.json']['runs'],[])

    def test_partial_evidence_configuration_is_visible_without_blocking_build(self):
        path=Path(__file__).resolve().parents[1]/'scripts/contribution_context.py'
        spec=importlib.util.spec_from_file_location('context_build',path);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        saved={}
        with patch.dict(os.environ,{'FC_EVIDENCE_REPOSITORY':'owner/repo'},clear=True),patch.object(module,'save',side_effect=lambda p,v:saved.update({str(p):v})):
            module.main()
        self.assertEqual(saved['site/data/evidence.json']['status'],'invalid')
        self.assertEqual(saved['site/data/work.json']['status'],'not_configured')
