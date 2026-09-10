#!/usr/bin/env node
/**
 * Build script for the Formal Conjectures website.
 *
 * Reads data/conjectures.json (produced by `lake exe extract_names` in the
 * formal-conjectures repo), processes it, and generates a static site under
 * site/.
 *
 * No external dependencies — only Node.js built-ins.
 */

const fs = require('fs');
const path = require('path');
const { execFileSync } = require('child_process');

// Base path for deployment (e.g. '/formal-conjectures' for GitHub Pages project sites).
// Set via BASE_PATH env var. Must NOT have a trailing slash.
const BASE_PATH = (process.env.BASE_PATH || '').replace(/\/$/, '');

const {AMS_SUBJECTS, SOURCE_COLLECTIONS, getCategoryMeta, moduleToGitHubPath, moduleToSourceURL, processEntry} = require('./src/js/catalog.js');
let GITHUB_API_BASE;

/** Compute site-wide statistics from processed entries. */
function computeStats(conjectures) {
  const byCategory = {};
  const byCollection = {};
  const bySubject = {};

  // Track distinct files (modules) per collection for the "Browse by source" list
  const filesByCollection = {};

  for (const c of conjectures) {
    byCategory[c.category] = (byCategory[c.category] || 0) + 1;
    byCollection[c.collection] = (byCollection[c.collection] || 0) + 1;
    for (const s of c.subjects) {
      bySubject[s.name] = (bySubject[s.name] || 0) + 1;
    }
    if (!filesByCollection[c.collection]) filesByCollection[c.collection] = new Set();
    filesByCollection[c.collection].add(c.module);
  }

  // Convert Sets to counts
  const fileCountByCollection = {};
  for (const [col, modules] of Object.entries(filesByCollection)) {
    fileCountByCollection[col] = modules.size;
  }

  return {
    total: conjectures.length,
    byCategory,
    byCollection,
    bySubject,
    fileCountByCollection,
  };
}

/**
 * Cross-tabulations and derived ratios for the /stats/ page.
 *
 * Note on multi-AMS theorems: a theorem with `@[AMS 5 11]` contributes to
 * both subject rows, so row totals can exceed `conjectures.length`. This is
 * consistent with `bySubject` in computeStats and is documented on the page.
 */
function computeAdvancedStats(conjectures) {
  const subjectByCategory = {};   // subjectName -> { category -> count, _formal: n, _total: n }
  for (const c of conjectures) {
    for (const s of c.subjects) {
      const row = subjectByCategory[s.name] ||
        (subjectByCategory[s.name] = { _formal: 0, _total: 0 });
      row[c.category] = (row[c.category] || 0) + 1;
      row._total += 1;
      if (c.hasFormalProof) row._formal += 1;
    }
  }
  return { subjectByCategory };
}

// ---------------------------------------------------------------------------
// File-system helpers
// ---------------------------------------------------------------------------

function ensureDir(dir) {
  if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
}

function copyDir(src, dest) {
  ensureDir(dest);
  for (const entry of fs.readdirSync(src, { withFileTypes: true })) {
    const s = path.join(src, entry.name);
    const d = path.join(dest, entry.name);
    if (entry.isDirectory()) copyDir(s, d);
    else fs.copyFileSync(s, d);
  }
}

function readTemplate(name) {
  return fs.readFileSync(path.join('src', 'templates', name), 'utf8');
}

/**
 * Simple template fill: replaces {{key}} with values[key].
 * Unrecognised placeholders are left as-is.
 */
function fill(template, values) {
  return template.replace(/\{\{(\w+)\}\}/g, (_, k) =>
    values[k] !== undefined ? String(values[k]) : `{{${k}}}`
  );
}

function writePage(destPath, html) {
  ensureDir(path.dirname(destPath));
  fs.writeFileSync(destPath, html, 'utf8');
}

// ---------------------------------------------------------------------------
// Contributor metadata
// ---------------------------------------------------------------------------

function getGitRoot() {
  if (process.env.FORMAL_CONJECTURES_ROOT) {
    return process.env.FORMAL_CONJECTURES_ROOT;
  }
  try {
    return execFileSync('git', ['rev-parse', '--show-toplevel'], {
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
    }).trim();
  } catch (_) {
    return null;
  }
}

function parseContributorLine(line) {
  const [sha, name, email, rawEmail, date] = line.split('\x1f');
  if (!sha || !name || !date) return null;
  return { sha, name, email: email || '', rawEmail: rawEmail || '', date };
}

function contributorKey(name, email) {
  return (email || name || 'unknown').trim().toLowerCase();
}

function dateOnly(isoDate) {
  return isoDate ? isoDate.slice(0, 10) : null;
}

function getContributorHistory(repoRoot, githubPath, revision) {
  let output = '';
  try {
    output = execFileSync('git', [
      '-C', repoRoot,
      'log',
      revision,
      '--follow',
      '--no-merges',
      '--format=%H%x1f%aN%x1f%aE%x1f%ae%x1f%aI',
      '--',
      githubPath,
    ], {
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'ignore'],
      maxBuffer: 10 * 1024 * 1024,
    });
  } catch (_) {
    return [];
  }

  const commits = output
    .split('\n')
    .map(line => parseContributorLine(line.trim()))
    .filter(Boolean);
  if (commits.length === 0) return [];

  const originalKey = contributorKey(commits[commits.length - 1].name, commits[commits.length - 1].email);
  const byAuthor = new Map();

  for (const commit of commits) {
    const key = contributorKey(commit.name, commit.email);
    let contributor = byAuthor.get(key);
    if (!contributor) {
      contributor = {
        _key: key,
        name: commit.name,
        email: commit.email,
        rawEmail: commit.rawEmail,
        emails: new Set([commit.email, commit.rawEmail].filter(Boolean)),
        latestCommit: commit.sha,
        commitCount: 0,
        firstCommitDate: dateOnly(commit.date),
        lastCommitDate: dateOnly(commit.date),
        originalAuthor: key === originalKey,
      };
      byAuthor.set(key, contributor);
    }

    contributor.commitCount += 1;
    if (commit.email) contributor.emails.add(commit.email);
    if (commit.rawEmail) contributor.emails.add(commit.rawEmail);
    contributor.firstCommitDate = dateOnly(commit.date);
  }

  return Array.from(byAuthor.values()).sort((a, b) => {
    if (a.originalAuthor !== b.originalAuthor) return a.originalAuthor ? -1 : 1;
    return b.commitCount - a.commitCount || a.name.localeCompare(b.name);
  });
}

function githubUserFromNoreply(email) {
  const numbered = email.match(/^(\d+)\+([A-Za-z0-9-]+)@users\.noreply\.github\.com$/);
  if (numbered) {
    const [, id, login] = numbered;
    return {
      login,
      profileUrl: `https://github.com/${login}`,
      avatarUrl: `https://avatars.githubusercontent.com/u/${id}?v=4`,
    };
  }

  const legacy = email.match(/^([A-Za-z0-9-]+)@users\.noreply\.github\.com$/);
  if (legacy) {
    const [, login] = legacy;
    return {
      login,
      profileUrl: `https://github.com/${login}`,
      avatarUrl: null,
    };
  }

  return null;
}

async function lookupCommitAuthor(sha, token) {
  if (!token || typeof fetch !== 'function') return null;

  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 5000);

  try {
    const headers = {
      Accept: 'application/vnd.github+json',
      'User-Agent': 'formal-conjectures-site-build',
    };
    headers.Authorization = `Bearer ${token}`;

    const resp = await fetch(`${GITHUB_API_BASE}/commits/${encodeURIComponent(sha)}`, {
      headers,
      signal: controller.signal,
    });
    if (!resp.ok) return null;

    const data = await resp.json();
    if (!data.author || !data.author.login) return null;

    return {
      login: data.author.login,
      profileUrl: data.author.html_url || `https://github.com/${data.author.login}`,
      avatarUrl: data.author.avatar_url || null,
    };
  } catch (_) {
    return null;
  } finally {
    clearTimeout(timeout);
  }
}

async function enrichContributorsWithGitHub(contributors) {
  const token = process.env.GITHUB_TOKEN || process.env.GH_TOKEN || '';
  let resolved = 0;

  for (const contributor of contributors) {
    const fromEmail = Array.from(contributor.emails || [contributor.email])
      .map(githubUserFromNoreply)
      .find(Boolean);
    if (fromEmail) {
      Object.assign(contributor, fromEmail);
      resolved += 1;
    }
  }

  if (!token) {
    console.log('  Skipping GitHub contributor profile lookup (no GITHUB_TOKEN or GH_TOKEN).');
    return resolved;
  }

  for (const contributor of contributors) {
    if (contributor.login || !contributor.latestCommit) continue;
    const fromCommit = await lookupCommitAuthor(contributor.latestCommit, token);
    if (fromCommit) {
      Object.assign(contributor, fromCommit);
      resolved += 1;
    }
  }

  return resolved;
}

function publicContributor(contributor) {
  const login = contributor.login || null;
  return {
    name: contributor.name,
    login,
    profileUrl: contributor.profileUrl || (login ? `https://github.com/${login}` : null),
    avatarUrl: contributor.avatarUrl || null,
    commitCount: contributor.commitCount,
    firstCommitDate: contributor.firstCommitDate,
    lastCommitDate: contributor.lastCommitDate,
    originalAuthor: contributor.originalAuthor,
  };
}

function rememberContributorIdentity(identities, contributor) {
  let identity = identities.get(contributor._key);
  if (!identity) {
    identity = {
      _key: contributor._key,
      name: contributor.name,
      email: contributor.email,
      rawEmail: contributor.rawEmail,
      emails: new Set(contributor.emails || []),
      latestCommit: contributor.latestCommit,
      lastCommitDate: contributor.lastCommitDate,
    };
    identities.set(contributor._key, identity);
    return;
  }

  for (const email of contributor.emails || []) identity.emails.add(email);
  if (!identity.lastCommitDate || contributor.lastCommitDate > identity.lastCommitDate) {
    identity.name = contributor.name;
    identity.email = contributor.email;
    identity.rawEmail = contributor.rawEmail;
    identity.latestCommit = contributor.latestCommit;
    identity.lastCommitDate = contributor.lastCommitDate;
  }
}

function applyContributorProfile(contributor, identity) {
  return {
    ...contributor,
    login: identity?.login || contributor.login,
    profileUrl: identity?.profileUrl || contributor.profileUrl,
    avatarUrl: identity?.avatarUrl || contributor.avatarUrl,
  };
}

async function buildContributorMetadata(conjectures, revision) {
  const repoRoot = getGitRoot();
  if (!repoRoot) {
    console.log('  No git repository found; skipping contributor metadata.');
    return {};
  }

  const paths = Array.from(new Set(conjectures.map(c => c.githubPath).filter(Boolean)));
  const contributorsByPath = {};
  const contributorsByIdentity = new Map();

  for (const githubPath of paths) {
    const contributors = getContributorHistory(repoRoot, githubPath, revision);
    if (contributors.length === 0) continue;

    contributorsByPath[githubPath] = contributors;
    for (const contributor of contributors) {
      rememberContributorIdentity(contributorsByIdentity, contributor);
    }
  }

  const uniqueContributors = Array.from(contributorsByIdentity.values());
  const resolvedCount = await enrichContributorsWithGitHub(uniqueContributors);

  for (const [githubPath, contributors] of Object.entries(contributorsByPath)) {
    contributorsByPath[githubPath] = contributors.map(contributor =>
      publicContributor(applyContributorProfile(contributor, contributorsByIdentity.get(contributor._key)))
    );
  }

  console.log(`  Loaded contributor history for ${Object.keys(contributorsByPath).length} files (${resolvedCount}/${uniqueContributors.length} GitHub profiles resolved).`);
  return contributorsByPath;
}

// ---------------------------------------------------------------------------
// HTML snippet generators
// ---------------------------------------------------------------------------

function statsCard(value, label) {
  return `<div class="stat-card"><span class="stat-value">${value}</span><span class="stat-label">${label}</span></div>`;
}

function categoryStatsHTML(byCategory) {
  const order = [
    'research open', 'research solved',
    'textbook', 'test', 'API',
  ];
  return order
    .filter(k => byCategory[k])
    .map(k => {
      const meta = getCategoryMeta(k);
      return `<a href="/browse/?category=${encodeURIComponent(k)}" class="cat-stat"><span class="badge ${meta.css}">${meta.label}</span><span class="cat-count">${byCategory[k]}</span></a>`;
    })
    .join('\n');
}

function collectionListHTML(byCollection, fileCountByCollection) {
  return Object.entries(byCollection)
    .sort((a, b) => b[1] - a[1])
    .map(([name, count]) => {
      const files = fileCountByCollection?.[name] || 0;
      return `<li><a href="/browse/?collection=${encodeURIComponent(name)}">${name}</a> <span class="count-badge">${files} files with ${count} statements</span></li>`;
    })
    .join('\n');
}

function subjectListHTML(bySubject) {
  return Object.entries(bySubject)
    .sort((a, b) => b[1] - a[1])
    .slice(0, 20) // top 20 subjects on landing page
    .map(([name, count]) => `<li><a href="/browse/?subject=${encodeURIComponent(name)}">${name}</a> <span class="count-badge">${count} statements</span></li>`)
    .join('\n');
}

// ---------------------------------------------------------------------------
// Modules page
// ---------------------------------------------------------------------------

/** Libraries with literate pages, in display order, with a one-line description. */
const LIBRARIES = {
  FormalConjectures: {
    lede: 'The problem statements themselves, organised by the collection they come from.',
  },
  FormalConjecturesForMathlib: {
    lede: 'Definitions and lemmas that the statements need but Mathlib does not yet have; candidates for upstreaming.',
  },
  FormalConjecturesUtil: {
    lede: 'Attributes, linters, and metadata infrastructure used by the problem files.',
  },
  FormalConjecturesTest: {
    lede: 'Tests of the infrastructure.',
  },
};

function escapeHtml(s) {
  return String(s)
    .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

/** Split a module name on dots, keeping «quoted» segments intact. */
function moduleSegments(module) {
  return module.replace(/«[^»]*»|\./g, (m) => (m[0] === '«' ? m : '/')).split('/');
}

/** Source-page navigation uses the full, validated Verso module index. */
function literateModules(index) {
  return index.modules.map(m => ({name: m.name, href: `/src${m.url}`}));
}

/**
 * Render the module index: one section per library, each split into groups by
 * the segment after the library name (the source collection, for problems).
 * A library whose modules all share that segment is shown as a flat list.
 */
function modulesPageHTML(modules) {
  const byLibrary = new Map();
  for (const m of modules) {
    const segs = moduleSegments(m.name);
    const lib = segs[0];
    if (!byLibrary.has(lib)) byLibrary.set(lib, []);
    byLibrary.get(lib).push({ ...m, segs });
  }

  const order = Object.keys(LIBRARIES);
  const libraries = [...byLibrary.keys()].sort((a, b) => {
    const ia = order.indexOf(a), ib = order.indexOf(b);
    if (ia !== -1 || ib !== -1) return (ia === -1 ? order.length : ia) - (ib === -1 ? order.length : ib);
    return a.localeCompare(b);
  });

  const listHTML = (items, depth) => `<ul class="module-list">
${items.map(m => {
    const label = m.segs.length > depth ? m.segs.slice(depth).join('.') : m.name;
    return `  <li data-name="${escapeHtml(m.name)}"><a href="${escapeHtml(m.href)}">${escapeHtml(label)}</a></li>`;
  }).join('\n')}
</ul>`;

  return libraries.map(lib => {
    const items = byLibrary.get(lib).sort((a, b) => a.name.localeCompare(b.name));
    const lede = LIBRARIES[lib]?.lede;

    // Group by the segment after the library name; the library's root module
    // (no such segment) and any module directly below it stay ungrouped.
    const groups = new Map();
    for (const m of items) {
      const key = m.segs.length > 2 ? m.segs[1] : '';
      if (!groups.has(key)) groups.set(key, []);
      groups.get(key).push(m);
    }
    const keys = [...groups.keys()].sort((a, b) => {
      if (a === '') return -1;
      if (b === '') return 1;
      return (SOURCE_COLLECTIONS[a]?.name || a).localeCompare(SOURCE_COLLECTIONS[b]?.name || b);
    });

    let body;
    if (keys.filter(k => k !== '').length < 2) {
      body = listHTML(items, 1);
    } else {
      body = keys.map(key => {
        const members = groups.get(key);
        if (key === '') {
          return `<div class="module-group">\n${listHTML(members, 1)}\n</div>`;
        }
        const collection = lib === 'FormalConjectures' ? SOURCE_COLLECTIONS[key] : null;
        const title = collection
          ? `<a href="/browse/?collection=${encodeURIComponent(collection.name)}">${escapeHtml(collection.name)}</a>`
          : escapeHtml(key);
        return `<div class="module-group">
<h3 class="module-group__title">${title} <span class="count-badge">${members.length} modules</span></h3>
${listHTML(members, 2)}
</div>`;
      }).join('\n');
    }

    return `  <section class="section module-library" id="${escapeHtml(lib)}">
    <div class="container">
      <h2 class="section__title">${escapeHtml(lib)} <span class="count-badge">${items.length} modules</span></h2>
      ${lede ? `<p class="module-library__lede">${lede}</p>` : ''}
${body}
    </div>
  </section>`;
  }).join('\n');
}

/** Render the subject × category cross-tab as an HTML table. */
function subjectStatusTableHTML(subjectByCategory) {
  const columns = [
    'research open', 'research solved', 'textbook', 'test', 'API',
  ];
  const rows = Object.entries(subjectByCategory)
    .filter(([, row]) => row._total > 0)
    .sort((a, b) => b[1]._total - a[1]._total);

  const head =
    `<tr>` +
    `<th scope="col">Subject</th>` +
    columns.map(cat => {
      const meta = getCategoryMeta(cat);
      const href = `/browse/?category=${encodeURIComponent(cat)}`;
      return `<th scope="col"><a href="${href}"><span class="badge ${meta.css}">${meta.label}</span></a></th>`;
    }).join('') +
    `<th scope="col" title="Has a formal proof linked"><a href="/browse/?formal_proof=true">Formal</a></th>` +
    `<th scope="col"><a href="/browse/">Total</a></th>` +
    `</tr>`;

  const body = rows.map(([subject, row]) => {
    const cells = columns.map(cat => {
      const n = row[cat] || 0;
      if (n === 0) return `<td class="empty">0</td>`;
      const href = `/browse/?subject=${encodeURIComponent(subject)}&category=${encodeURIComponent(cat)}`;
      return `<td><a href="${href}">${n}</a></td>`;
    }).join('');
    const formalCell = row._formal === 0
      ? `<td class="empty">0</td>`
      : `<td><a href="/browse/?subject=${encodeURIComponent(subject)}&formal_proof=true">${row._formal}</a></td>`;
    const totalCell =
      `<td><a href="/browse/?subject=${encodeURIComponent(subject)}"><strong>${row._total}</strong></a></td>`;
    return `<tr><th scope="row"><a href="/browse/?subject=${encodeURIComponent(subject)}">${subject}</a></th>${cells}${formalCell}${totalCell}</tr>`;
  }).join('\n');

  return `<table class="stats-table"><thead>${head}</thead><tbody>${body}</tbody></table>`;
}

// ---------------------------------------------------------------------------
// Main build
// ---------------------------------------------------------------------------

async function main() {
  console.log('Building Formal Conjectures website...');

  // Read raw data
  const catalog = require('./catalog.cjs').readCatalog('data');
  GITHUB_API_BASE = `https://api.github.com/repos/${catalog.provenance.source.repository}`;
  const rawData = catalog.problems;

  if (rawData.length === 0) {
    console.error('Error: no conjectures loaded. Generate a complete catalog as described in site/README.md.');
    process.exit(1);
  }

  const conjectures = rawData.map(entry => processEntry(entry, catalog.provenance.source));
  const stats = computeStats(conjectures);
  const advancedStats = computeAdvancedStats(conjectures);

  const descriptor = JSON.parse(fs.readFileSync('data/catalog-manifest.json'));

  // Load Verso literate fragments (module docstrings + const links)
  let versoFragments = { moduleDocs: {}, constLinks: {} };
  if (!process.env.FC_RENDER_BASE && fs.existsSync('data/verso-fragments.json')) {
    versoFragments = JSON.parse(fs.readFileSync('data/verso-fragments.json', 'utf8'));
    if (versoFragments.catalog_sha256 !== descriptor.sha256) throw new Error('Verso fragments belong to another catalog. Rebuild them from the same source revision.');
    console.log(`  Loaded ${Object.keys(versoFragments.moduleDocs).length} module docstrings, ${Object.keys(versoFragments.constLinks).length} constant links from Verso.`);
  } else if (!process.env.FC_RENDER_BASE) {
    throw new Error('Verso fragments are missing. Run the full build in site/README.md, or use site/dev.sh for a published snapshot.');
  }

  if (process.env.FC_RENDER_BASE && !fs.existsSync('data/verso-modules.json')) {
    throw new Error('Verso module index is missing (data/verso-modules.json). Download the published snapshot with scripts/download_catalog.py.');
  }
  const moduleIndex = require('./catalog.cjs').validateModuleIndex(process.env.FC_RENDER_BASE
    ? JSON.parse(fs.readFileSync('data/verso-modules.json', 'utf8'))
    : {schema_version:'fc.website-modules.v1', catalog_sha256:descriptor.sha256, modules:versoFragments.modules},
    descriptor.sha256);

  const contributors = process.env.FC_RENDER_BASE ? {}
    : await buildContributorMetadata(conjectures, catalog.provenance.source.commit);

  console.log(`  Loaded ${conjectures.length} conjectures.`);

  // Clean and recreate site directory
  if (fs.existsSync('site')) fs.rmSync('site', { recursive: true });
  fs.mkdirSync('site');

  // Copy static assets
  copyDir('src/css', 'site/assets/css');
  copyDir('src/js', 'site/assets/js');
  if (fs.existsSync('src/img')) copyDir('src/img', 'site/assets/img');
  if (fs.existsSync('src/fonts')) copyDir('src/fonts', 'site/assets/fonts');

  // The browser reads the same canonical catalog as the CLI. Verso output is a
  // per-module rendering sidecar, bound to that catalog's bytes, never metadata input.
  ensureDir('site/data');
  // Previews retain navigation, but continue loading rich rendering at its explicit origin.
  const moduleIndexPath = `site/data/rendered/${descriptor.sha256}/modules.json`;
  ensureDir(path.dirname(moduleIndexPath));
  fs.writeFileSync(moduleIndexPath, JSON.stringify(moduleIndex));
  const groups = new Map();
  for (const entry of conjectures) {
    if (!groups.has(entry.module)) groups.set(entry.module, []);
    groups.get(entry.module).push(entry);
  }
  for (const [module, entries] of (process.env.FC_RENDER_BASE ? [] : groups)) {
    const first = entries[0];
    const moduleKey = first.sourceUrl.replace(/^\/src/, '');
    const constLinks = {};
    for (const entry of entries) {
      if (versoFragments.constLinks[entry.theorem]) constLinks[entry.theorem] = versoFragments.constLinks[entry.theorem];
    }
    const filename = `site/data/rendered/${descriptor.sha256}/${moduleToGitHubPath(module).replace(/\.lean$/, '.json')}`;
    ensureDir(path.dirname(filename));
    fs.writeFileSync(filename, JSON.stringify({schema_version:'fc.website-rendering.v1',
      catalog_sha256:descriptor.sha256, module,
      moduleDocs: {[moduleKey]:versoFragments.moduleDocs[moduleKey] || ''}, constLinks,
      contributors:contributors[first.githubPath] || []}));
  }
  // One native catalog is shared by browser, CLI, status and link consumers.
  fs.copyFileSync('data/conjectures.json', 'site/data/conjectures.json');
  fs.copyFileSync('data/catalog-manifest.json', 'site/data/catalog-manifest.json');
  copyDir('../toolkit/conjectures/resources/schemas', 'site/data/schemas');
  const whitePlotPath = path.join('data', 'file_counts_white.html');
  const darkPlotPath = path.join('data', 'file_counts_dark.html');
  if (fs.existsSync(whitePlotPath)) fs.copyFileSync(whitePlotPath, 'site/data/file_counts_white.html');
  if (fs.existsSync(darkPlotPath)) fs.copyFileSync(darkPlotPath, 'site/data/file_counts_dark.html');

  // ---- Landing page ----
  const indexHtml = readTemplate('index.html');
  const openCount   = stats.byCategory['research open'] || 0;
  const solvedCount = stats.byCategory['research solved'] || 0;
  const formalCount = conjectures.filter(c => c.hasFormalProof).length;
  writePage('site/index.html', applyBasePath(fill(indexHtml, {
    totalCount:      openCount + solvedCount,
    openCount,
    solvedCount,
    formalCount,
    categoryStats:   categoryStatsHTML(stats.byCategory),
    collectionList:  collectionListHTML(stats.byCollection, stats.fileCountByCollection),
    subjectList:     subjectListHTML(stats.bySubject),
  })));

  // ---- Browse page ----
  copyStaticTemplate('browse.html', 'site/browse/index.html');

  // ---- Theorem detail page ----
  copyStaticTemplate('theorem.html', 'site/theorem/index.html');

  // ---- Contribute page ----
  copyStaticTemplate('contribute.html', 'site/contribute/index.html');

  // ---- About page ----
  copyStaticTemplate('about.html', 'site/about/index.html');

  // ---- Stats page ----
  let growthPlot = '';
  if (fs.existsSync(whitePlotPath) && fs.existsSync(darkPlotPath)) {
    const graphHtmlLight = fs.readFileSync(whitePlotPath, 'utf8');
    const graphHtmlDark = fs.readFileSync(darkPlotPath, 'utf8');
    growthPlot = `
      <style>
        .theme-dark { display: none; }
        @media (prefers-color-scheme: dark) {
          .theme-light { display: none; }
          .theme-dark { display: block; }
        }
      </style>
      <div class="theme-light">${graphHtmlLight}</div>
      <div class="theme-dark">${graphHtmlDark}</div>
    `;
    console.log('  Loaded repository growth plots.');
  } else {
    console.log('  Repository growth plots not found (skipping growth plot).');
  }

  const statsHtml = readTemplate('stats.html');
  writePage('site/stats/index.html', applyBasePath(fill(statsHtml, {
    totalCount:           stats.total,
    growthPlot:           growthPlot,
    subjectStatusTable:   subjectStatusTableHTML(advancedStats.subjectByCategory),
  })));

  // ---- Modules page ----
  const modules = literateModules(moduleIndex);
  writePage('site/modules/index.html', applyBasePath(fill(readTemplate('modules.html'), {
    moduleCount: modules.length,
    libraries:   modulesPageHTML(modules),
  })));
  console.log(`  Module index lists ${modules.length} modules.`);

  console.log('Done. Output in site/');
}

function copyStaticTemplate(templateName, dest) {
  const html = applyBasePath(readTemplate(templateName));
  writePage(dest, html);
}

/**
 * Rewrite absolute paths in HTML to include the BASE_PATH prefix.
 * Matches href="/..." and src="/..." attributes (but not href="//" or src="//"
 * which are protocol-relative URLs, and not href="https://" etc.).
 * Also sets the data-base attribute on the <html> tag for JavaScript use.
 */
function applyBasePath(html) {
  const renderingBase = process.env.FC_RENDER_BASE || BASE_PATH;
  if (process.env.FC_RENDER_BASE && !/^https:\/\/[A-Za-z0-9.-]+(?:\/[A-Za-z0-9._/-]*)?$/.test(renderingBase)) throw new Error('Invalid rendering origin');
  html = html.replace('data-base=""', `data-base="" data-render-base="${renderingBase}"`);
  // Annotated source belongs to the rendering origin in website-only previews.
  // Rewrite before the local base path so root-hosted previews work too.
  if (process.env.FC_RENDER_BASE) html = html.replace(/(href|src)="\/src(?=[/"?#])/g, `$1="${renderingBase}/src`);
  if (!BASE_PATH) return html;
  // Set data-base on <html> for client-side JS (main.js uses this for fetch paths)
  html = html.replace('data-base=""', `data-base="${BASE_PATH}"`);
  // Rewrite href="/..." and src="/..." to include the base path
  html = html.replace(/(href|src)="\/(?!\/)/g, `$1="${BASE_PATH}/`);
  // Rewrite url('/...') in CSS (e.g. @font-face src)
  html = html.replace(/url\('\/(?!\/)/g, `url('${BASE_PATH}/`);
  return html;
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});
