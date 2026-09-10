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
      fs.writeFileSync(path.join(directory,'catalog-manifest.json'),JSON.stringify({schema_version:'fc.catalog.v1',catalog:'conjectures.json',
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

test('full site publishes one unchanged catalog and bound module rendering', () => {
  const {spawnSync} = require('node:child_process');
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'fc-site-build-'));
  const site = path.join(directory,'site');
  try {
    fs.mkdirSync(path.join(site,'data'),{recursive:true});
    for (const name of ['build.js','catalog.cjs','src']) fs.cpSync(path.join(__dirname,'..',name),path.join(site,name),{recursive:true});
    fs.cpSync(path.join(__dirname,'../../toolkit/conjectures/resources/schemas'),path.join(directory,'toolkit/conjectures/resources/schemas'),{recursive:true});
    const data = {schemaVersion:2,problems:[{theorem:'Example.test',module:'FormalConjectures.Example',
      category:'research open',subjects:['11'],statement:'True',docstring:'Native description',formalProofs:[]}],
      provenance:{source:{repository:'owner/fc',commit:'a'.repeat(40)}},moduleDocstrings:{'FormalConjectures.Example':'Source'}};
    const raw = JSON.stringify(data);
    const digest = crypto.createHash('sha256').update(raw).digest('hex');
    fs.writeFileSync(path.join(site,'data/conjectures.json'),raw);
    fs.writeFileSync(path.join(site,'data/catalog-manifest.json'),JSON.stringify({schema_version:'fc.catalog.v1',catalog:'conjectures.json',
      bytes:Buffer.byteLength(raw),sha256:digest,problem_count:1,provenance:data.provenance}));
    const fragments = {catalog_sha256:digest,modules:[],moduleDocs:{'/FormalConjectures/Example/':'Rendered source'},
      constLinks:{'Example.test':{url:'/FormalConjectures/Example/#test',anchor:'test',docHtml:'Rendered description',
        codeHtml:'<code>theorem test : True := by sorry</code>',hoverDocs:{used:'True'}}}};
    const fragmentsPath = path.join(site,'data/verso-fragments.json');
    fs.writeFileSync(fragmentsPath,JSON.stringify(fragments));
    const env = {...process.env,BASE_PATH:'/fc',FC_RENDER_BASE:'',GITHUB_TOKEN:'',GH_TOKEN:''};
    const build = () => spawnSync(process.execPath,['build.js'],{cwd:site,env,encoding:'utf8'});
    const result = build();
    assert.equal(result.status,0,result.stdout+result.stderr);
    assert.equal(fs.readFileSync(path.join(site,'site/data/conjectures.json'),'utf8'),raw);
    assert.equal(fs.existsSync(path.join(site,'site/data/catalog.json')),false);
    assert.equal(fs.existsSync(path.join(site,'site/data/verso-fragments.json')),false);
    const rendered = JSON.parse(fs.readFileSync(path.join(site,`site/data/rendered/${digest}/FormalConjectures/Example.json`)));
    assert.equal(rendered.catalog_sha256,digest);
    assert.equal(rendered.constLinks['Example.test'].hoverDocs.used,'True');
    fs.writeFileSync(fragmentsPath,JSON.stringify({...fragments,catalog_sha256:'b'.repeat(64)}));
    const mismatch=build();assert.notEqual(mismatch.status,0);assert.match(mismatch.stderr,/another catalog/);
    fs.unlinkSync(fragmentsPath);
    const missing=build();assert.notEqual(missing.status,0);assert.match(missing.stderr,/fragments are missing/);
    env.FC_RENDER_BASE='https://example.org/fc';
    const preview=build();assert.equal(preview.status,0,preview.stderr);
    assert.equal(fs.existsSync(path.join(site,'site/data/rendered')),false);
    assert.match(fs.readFileSync(path.join(site,'site/theorem/index.html'),'utf8'),/data-render-base="https:\/\/example.org\/fc"/);
  } finally { fs.rmSync(directory,{recursive:true,force:true}); }
});
