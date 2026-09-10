/* A preview must publish the exact catalog snapshot it consumed. */
const fs = require('node:fs');
const crypto = require('node:crypto');
const path = require('node:path');
const {sameJSON} = require('./src/js/catalog.js');

function readCatalog(directory) {
  const raw = fs.readFileSync(path.join(directory, 'conjectures.json'));
  const descriptor = JSON.parse(fs.readFileSync(path.join(directory, 'catalog-manifest.json')));
  if (descriptor.schema_version !== 'fc.catalog.v1' || descriptor.catalog !== 'conjectures.json' ||
      descriptor.bytes !== raw.length || descriptor.sha256 !== crypto.createHash('sha256').update(raw).digest('hex')) {
    throw new Error('Catalog does not match its publication descriptor. Generate or download the full native catalog.');
  }
  const data = JSON.parse(raw);
  const source = data.provenance?.source;
  if (data.schemaVersion !== 2 || !data.problems?.length ||
      !/^[\w.-]+\/[\w.-]+$/.test(source?.repository || '') || !/^[a-f0-9]{40}$/.test(source?.commit || '') ||
      data.problems.some(p => typeof p.statement !== 'string' || !p.statement.trim()) ||
      descriptor.problem_count !== data.problems.length ||
      !sameJSON(data.provenance, descriptor.provenance)) {
    throw new Error('A site build requires complete statements and matching catalog provenance.');
  }
  return data;
}

module.exports = {readCatalog};
