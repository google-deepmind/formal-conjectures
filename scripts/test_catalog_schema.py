"""The public JSON Schemas describe actual publication bytes, not another model."""
import json
from pathlib import Path
import unittest
from jsonschema import Draft202012Validator
import test_catalog_publication as publication_tests
import publish_catalog
from conjectures import catalog_data

SCHEMAS=Path(__file__).resolve().parents[1]/'toolkit/conjectures/resources/schemas'

class CatalogSchemaTests(unittest.TestCase):
    setUp = publication_tests.PublicationTests.setUp
    def test_public_catalog_and_manifest_validate(self):
        out=self.root/'published'
        data=publish_catalog.prepare(self.root,'owner/fc',publication_tests.fixture(),out)
        for name,instance in [('catalog-v2.schema.json',data),('catalog-manifest-v1.schema.json',json.loads((out/'catalog-manifest.json').read_bytes()))]:
            schema=json.loads((SCHEMAS/name).read_bytes())
            Draft202012Validator.check_schema(schema)
            validator=Draft202012Validator(schema);validator.validate(instance)
            self.assertEqual((out/'schemas'/name).read_bytes(),(SCHEMAS/name).read_bytes())
        bad={**data,'problems':[{**data['problems'][0],'answerKinds':['unknown']}]}
        self.assertTrue(list(Draft202012Validator(json.loads((SCHEMAS/'catalog-v2.schema.json').read_bytes())).iter_errors(bad)))

    def test_json_is_unambiguous_and_finite(self):
        for raw in ['{"a":1,"a":2}','{"a":NaN}','{"a":Infinity}']:
            with self.assertRaises(ValueError):catalog_data.parse(raw)
        with self.assertRaises(ValueError):catalog_data.encode({'a':float('nan')})

    def test_rendering_schema_binds_the_catalog(self):
        schema=json.loads((SCHEMAS/'website-rendering-v1.schema.json').read_bytes())
        Draft202012Validator.check_schema(schema)
        value={'schema_version':'fc.website-rendering.v1','catalog_sha256':'a'*64,
               'module':'FormalConjectures.Example','moduleDocs':{},'constLinks':{},'contributors':[]}
        Draft202012Validator(schema).validate(value)
