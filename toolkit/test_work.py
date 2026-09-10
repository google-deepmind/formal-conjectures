import unittest
from unittest.mock import patch
from conjectures import work, projections, report as rr

class WorkTests(unittest.TestCase):
    def test_exact_module_and_repository_join_and_untrusted_url(self):
        context=projections.work_context({'schema_version':'fc.work-context.v1','repository':'owner/fc',
            'observed_at':'2026-09-09T00:00:00Z','pull_requests':[{'number':42,'title':'A','files':['A.lean'],
            'head':'a'*40,'base':'b'*40,'url':'javascript:bad'}]})
        self.assertEqual(work.related({'githubPath':'A.lean'},context,{'repository':'other/fc'}),[])
        self.assertEqual(work.related({'githubPath':'B.lean'},context,{'repository':'owner/fc'}),[])
        self.assertEqual(work.related({'githubPath':'A.lean'},context,{'repository':'owner/fc'})[0]['url'],'https://github.com/owner/fc/pull/42')
        entry={'validation':'validated_bundle','target':{'repository':'owner/fc','pr':42,'head':'c'*40,'base':'b'*40}}
        value=projections.contribution_context({'runs':[entry]},context)['runs'][0]
        self.assertEqual(value['changes'],['head_changed']);self.assertEqual(value['applicability'],'historical')

    def test_transport_failure_is_explicit(self):
        with patch.object(work,'read_url',side_effect=OSError('offline')):
            self.assertEqual(work.load()['status'],'unavailable')
