/* A preview must publish the exact catalog snapshot it consumed. */
const fs = require('node:fs');
const crypto = require('node:crypto');
const path = require('node:path');
const {sameJSON, validateCatalog} = require('./src/js/catalog.js');

function readCatalog(directory) {
  const raw = fs.readFileSync(path.join(directory, 'conjectures.json'));
  const descriptor = JSON.parse(fs.readFileSync(path.join(directory, 'catalog-manifest.json')));
  if (descriptor.schema_version !== 'fc.catalog.v1' || descriptor.catalog !== 'conjectures.json' ||
      descriptor.bytes !== raw.length || descriptor.sha256 !== crypto.createHash('sha256').update(raw).digest('hex')) {
    throw new Error('Catalog does not match its publication descriptor. Generate or download the full native catalog.');
  }
  const data = validateCatalog(JSON.parse(raw));
  if (descriptor.problem_count !== data.problems.length || !sameJSON(data.provenance, descriptor.provenance)) {
    throw new Error('Catalog provenance or count differs from its publication descriptor.');
  }
  return data;
}

/** Verso, rather than the problem catalog, owns the complete source-page index. */
function validateModuleIndex(index, digest) {
  if (!index || index.schema_version !== 'fc.website-modules.v1' || index.catalog_sha256 !== digest ||
      !Array.isArray(index.modules) || !index.modules.length) {
    throw new Error('Missing module index or module index belongs to another catalog. Run a full build or download its matching index.');
  }
  const names = new Set();
  const urls = new Set();
  for (const entry of index.modules) {
    if (!entry || typeof entry.name !== 'string' || !/^FormalConjectures(?:ForMathlib|Util|Test)?(?:\.|$)/.test(entry.name) ||
        typeof entry.url !== 'string' || !/^\/FormalConjectures(?:ForMathlib|Util|Test)?\//.test(entry.url) ||
        !entry.url.endsWith('/') || /[\\\\?#%]/.test(entry.url) ||
        entry.url.slice(1,-1).split('/').some(part => !part || part === '.' || part === '..') ||
        names.has(entry.name) || urls.has(entry.url)) {
      throw new Error('Invalid or duplicate Verso module index entry');
    }
    names.add(entry.name); urls.add(entry.url);
  }
  return index;
}

module.exports = {readCatalog, validateModuleIndex};
