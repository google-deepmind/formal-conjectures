const assert = require('node:assert/strict');
const test = require('node:test');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const crypto = require('node:crypto');
const {readSnapshot, validateModuleIndex} = require('../catalog.cjs');
function fixture() { return structuredClone(require('./fixtures/catalog.json')); }

test('site preserves the native snapshot and rejects partial or corrupted data', () => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), 'fc-catalog-'));
  try {
    function write(data) {
      const raw = JSON.stringify(data);
      fs.writeFileSync(path.join(directory,'conjectures.json'),raw);
      fs.writeFileSync(path.join(directory,'catalog-manifest.json'),JSON.stringify({schema_version:'fc.catalog.v1',catalog:'conjectures.json',
        bytes:Buffer.byteLength(raw),sha256:crypto.createHash('sha256').update(raw).digest('hex'),problem_count:1,provenance:data.provenance}));
    }
    const data = fixture();
    write(data);assert.deepEqual(readSnapshot(directory).catalog,data);
    fs.appendFileSync(path.join(directory,'conjectures.json'),' ');
    assert.throws(() => readSnapshot(directory),/publication descriptor/);
    delete data.problems[0].statement;write(data);
    assert.throws(() => readSnapshot(directory),/catalog statement/);
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
    const data = fixture();
    const raw = JSON.stringify(data);
    const digest = crypto.createHash('sha256').update(raw).digest('hex');
    fs.writeFileSync(path.join(site,'data/conjectures.json'),raw);
    fs.writeFileSync(path.join(site,'data/catalog-manifest.json'),JSON.stringify({schema_version:'fc.catalog.v1',catalog:'conjectures.json',
      bytes:Buffer.byteLength(raw),sha256:digest,problem_count:1,provenance:data.provenance}));
    const fragments = {catalog_sha256:digest,modules:['FormalConjectures.Example','FormalConjecturesForMathlib.Example','FormalConjecturesUtil.Example','FormalConjecturesTest.Example'].map(name=>({name,url:'/'+name.replaceAll('.','/')+'/'})),moduleDocs:{'/FormalConjectures/Example/':'Rendered source'},
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
    assert.match(fs.readFileSync(path.join(site,'site/modules/index.html'),'utf8'),/href="\/fc\/src\/FormalConjectures\/Example\/"/);
    const rendered = JSON.parse(fs.readFileSync(path.join(site,`site/data/rendered/${digest}/FormalConjectures/Example.json`)));
    const index=JSON.parse(fs.readFileSync(path.join(site,`site/data/rendered/${digest}/modules.json`)));
    assert.deepEqual(index.modules,fragments.modules);
    assert.equal(rendered.catalog_sha256,digest);
    assert.equal(rendered.constLinks['Example.test'].hoverDocs.used,'True');
    fs.writeFileSync(fragmentsPath,JSON.stringify({...fragments,catalog_sha256:'b'.repeat(64)}));
    const mismatch=build();assert.notEqual(mismatch.status,0);assert.match(mismatch.stderr,/another catalog/);
    fs.unlinkSync(fragmentsPath);
    const missing=build();assert.notEqual(missing.status,0);assert.match(missing.stderr,/fragments are missing/);
    env.FC_RENDER_BASE='https://example.org/fc';
    const missingIndex=build();assert.notEqual(missingIndex.status,0);assert.match(missingIndex.stderr,/verso-modules.json/);
    const indexPath=path.join(site,'data/verso-modules.json');
    fs.writeFileSync(indexPath,JSON.stringify({...index,catalog_sha256:'b'.repeat(64)}));
    const wrongIndex=build();assert.notEqual(wrongIndex.status,0);assert.match(wrongIndex.stderr,/another catalog/);
    fs.writeFileSync(indexPath,JSON.stringify(index));
    const preview=build();assert.equal(preview.status,0,preview.stderr);
    assert.equal(fs.existsSync(path.join(site,`site/data/rendered/${digest}/FormalConjectures/Example.json`)),false);
    assert.match(fs.readFileSync(path.join(site,'site/theorem/index.html'),'utf8'),/data-render-base="https:\/\/example.org\/fc"/);
    for (const base of ['/fc', '']) {
      env.BASE_PATH=base;
      assert.equal(build().status,0);
      const modules=fs.readFileSync(path.join(site,'site/modules/index.html'),'utf8');
      assert.match(modules,/href="https:\/\/example.org\/fc\/src\/FormalConjectures\/Example\/"/);
      for (const entry of fragments.modules) assert.ok(modules.includes(`href="https://example.org/fc/src${entry.url}"`),entry.name);
      assert.ok(!modules.includes(`href="${base}/src/`));
      assert.ok(modules.includes(`href="${base}/browse/"`));
    }
  } finally { fs.rmSync(directory,{recursive:true,force:true}); }
});

test('Node rejects all malformed publication fields before site assembly',()=>{
  const directory=fs.mkdtempSync(path.join(os.tmpdir(),'fc-catalog-invalid-'));
  try {
    for (const change of require('./fixtures/catalog-invalid.json')) {
      const data=fixture();
      const parent=change.path.slice(0,-1).reduce((v,k)=>v[k],data);
      if(change.remove) delete parent[change.path.at(-1)]; else parent[change.path.at(-1)]=change.value;
      const raw=JSON.stringify(data);
      fs.writeFileSync(path.join(directory,'conjectures.json'),raw);
      fs.writeFileSync(path.join(directory,'catalog-manifest.json'),JSON.stringify({schema_version:'fc.catalog.v1',catalog:'conjectures.json',
        bytes:Buffer.byteLength(raw),sha256:crypto.createHash('sha256').update(raw).digest('hex'),problem_count:1,provenance:data.provenance}));
      assert.throws(()=>readSnapshot(directory),/Invalid or missing catalog/,JSON.stringify(change));
    }
  } finally {fs.rmSync(directory,{recursive:true,force:true});}
});

test('module navigation rejects duplicates and unsafe source paths',()=>{
  const digest='a'.repeat(64);
  const entry={name:'FormalConjectures.Example',url:'/FormalConjectures/Example/'};
  const index={schema_version:'fc.website-modules.v1',catalog_sha256:digest,modules:[entry]};
  assert.equal(validateModuleIndex(index,digest),index);
  for(const url of ['//example.org/','/FormalConjectures/../','/FormalConjectures/%2e%2e/','/FormalConjectures/x?bad/','/FormalConjectures/\\bad/']) {
    assert.throws(()=>validateModuleIndex({...index,modules:[{...entry,url}]},digest),/Invalid/);
  }
  assert.throws(()=>validateModuleIndex({...index,modules:[entry,entry]},digest),/duplicate/);
});
