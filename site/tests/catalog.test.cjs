const assert = require('node:assert/strict');
const test = require('node:test');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const crypto = require('node:crypto');
const {readCatalog} = require('../catalog.cjs');

test('site preserves the native snapshot and rejects partial or corrupted data', () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'fc-catalog-'));
  try {
    function write(data) {
      const raw = JSON.stringify(data);
      fs.writeFileSync(path.join(directory,'conjectures.json'),raw);
      fs.writeFileSync(path.join(directory,'catalog-manifest.json'),JSON.stringify({schema_version:'fc.catalog.v1',catalog:'catalog.json',
        bytes:Buffer.byteLength(raw),sha256:crypto.createHash('sha256').update(raw).digest('hex'),problem_count:1,provenance:data.provenance}));
    }
    const data = {schemaVersion:2,problems:[{statement:'∀ n : ℕ, n = n'}],provenance:{source:{repository:'owner/fc',commit:'a'.repeat(40)}}};
    write(data);assert.deepEqual(readCatalog(directory),data);
    fs.appendFileSync(path.join(directory,'conjectures.json'),' ');
    assert.throws(() => readCatalog(directory),/publication descriptor/);
    delete data.problems[0].statement;write(data);
    assert.throws(() => readCatalog(directory),/complete statements/);
  } finally { fs.rmSync(directory,{recursive:true,force:true}); }
});
