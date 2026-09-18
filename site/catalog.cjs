/* A preview must publish the exact catalog snapshot it consumed. */
const fs = require('node:fs');
const crypto = require('node:crypto');
const path = require('node:path');
const {decodeSnapshot, moduleToGitHubPath} = require('./src/js/catalog.js');

/** Retain the validated bytes so the build publishes exactly the snapshot it read. */
function readSnapshot(directory) {
  const catalogBytes = fs.readFileSync(path.join(directory, 'conjectures.json'));
  const descriptorBytes = fs.readFileSync(path.join(directory, 'catalog-manifest.json'));
  const descriptor = JSON.parse(descriptorBytes);
  const digest = crypto.createHash('sha256').update(catalogBytes).digest('hex');
  const catalog = decodeSnapshot(catalogBytes, descriptor, digest);
  return {catalog, descriptor, catalogBytes, descriptorBytes};
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
        !entry.url.endsWith('/') || /[\\?#%]/.test(entry.url) ||
        entry.url.slice(1,-1).split('/').some(part => !part || part === '.' || part === '..') ||
        names.has(entry.name) || urls.has(entry.url)) {
      throw new Error('Invalid or duplicate Verso module index entry');
    }
    names.add(entry.name); urls.add(entry.url);
  }
  return index;
}

/** Full builds read local rendering; previews read only its published navigation. */
function readRendering(directory, digest, preview) {
  const filename = path.join(directory, preview ? 'verso-modules.json' : 'verso-fragments.json');
  if (!fs.existsSync(filename)) {
    throw new Error(preview
      ? `Verso module index is missing (${filename}). Download the snapshot with scripts/download_catalog.py.`
      : 'Verso fragments are missing. Run the full build in site/README.md, or use site/dev.sh for a published snapshot.');
  }
  const data = JSON.parse(fs.readFileSync(filename, 'utf8'));
  if (data.catalog_sha256 !== digest) throw new Error('Verso data belongs to another catalog. Rebuild or download the matching snapshot.');
  const moduleIndex = validateModuleIndex(preview ? data
    : {schema_version:'fc.website-modules.v1', catalog_sha256:digest, modules:data.modules}, digest);
  return {moduleIndex, fragments:preview ? null : data};
}

/** Publish navigation and, for full builds, rendering scoped to each problem module. */
function writeRendering(directory, digest, conjectures, {moduleIndex, fragments}, contributors) {
  const output = path.join(directory, 'rendered', digest);
  function write(relative, data) {
    const filename = path.join(output, relative);
    fs.mkdirSync(path.dirname(filename), {recursive:true});
    fs.writeFileSync(filename, JSON.stringify(data));
  }
  write('modules.json', moduleIndex);
  if (!fragments) return;

  const groups = new Map();
  for (const entry of conjectures) {
    if (!groups.has(entry.module)) groups.set(entry.module, []);
    groups.get(entry.module).push(entry);
  }
  for (const [module, entries] of groups) {
    const first = entries[0];
    const moduleKey = first.sourceUrl.replace(/^\/src/, '');
    const constLinks = {};
    for (const entry of entries) {
      if (fragments.constLinks[entry.theorem]) constLinks[entry.theorem] = fragments.constLinks[entry.theorem];
    }
    write(moduleToGitHubPath(module).replace(/\.lean$/, '.json'), {
      schema_version:'fc.website-rendering.v1', catalog_sha256:digest, module,
      moduleDocs:{[moduleKey]:fragments.moduleDocs[moduleKey] || ''}, constLinks,
      contributors:contributors[first.githubPath] || [],
    });
  }
}

module.exports = {readSnapshot, readRendering, writeRendering, validateModuleIndex};
