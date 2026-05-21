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

// ---------------------------------------------------------------------------
// AMS MSC2020 subject classification map (code → description)
// ---------------------------------------------------------------------------
const AMS_SUBJECTS = {
  0:  'General and overarching topics',
  1:  'History and biography',
  3:  'Mathematical logic and foundations',
  5:  'Combinatorics',
  6:  'Order, lattices, ordered algebraic structures',
  8:  'General algebraic systems',
  11: 'Number theory',
  12: 'Field theory and polynomials',
  13: 'Commutative algebra',
  14: 'Algebraic geometry',
  15: 'Linear and multilinear algebra; matrix theory',
  16: 'Associative rings and algebras',
  17: 'Nonassociative rings and algebras',
  18: 'Category theory; homological algebra',
  19: 'K-theory',
  20: 'Group theory and generalizations',
  22: 'Topological groups, Lie groups',
  26: 'Real functions',
  28: 'Measure and integration',
  30: 'Functions of a complex variable',
  31: 'Potential theory',
  32: 'Several complex variables and analytic spaces',
  33: 'Special functions',
  34: 'Ordinary differential equations',
  35: 'Partial differential equations',
  37: 'Dynamical systems and ergodic theory',
  39: 'Difference and functional equations',
  40: 'Sequences, series, summability',
  41: 'Approximations and expansions',
  42: 'Harmonic analysis on Euclidean spaces',
  43: 'Abstract harmonic analysis',
  44: 'Integral transforms, operational calculus',
  45: 'Integral equations',
  46: 'Functional analysis',
  47: 'Operator theory',
  49: 'Calculus of variations and optimal control; optimization',
  51: 'Geometry',
  52: 'Convex and discrete geometry',
  53: 'Differential geometry',
  54: 'General topology',
  55: 'Algebraic topology',
  57: 'Manifolds and cell complexes',
  58: 'Global analysis, analysis on manifolds',
  60: 'Probability theory and stochastic processes',
  62: 'Statistics',
  65: 'Numerical analysis',
  68: 'Computer science',
  70: 'Mechanics of particles and systems',
  74: 'Mechanics of deformable solids',
  76: 'Fluid mechanics',
  78: 'Optics, electromagnetic theory',
  80: 'Classical thermodynamics, heat transfer',
  81: 'Quantum theory',
  82: 'Statistical mechanics, structure of matter',
  83: 'Relativity and gravitational theory',
  85: 'Astronomy and astrophysics',
  86: 'Geophysics',
  90: 'Operations research, mathematical programming',
  91: 'Game theory, economics, social and behavioral sciences',
  92: 'Biology and other natural sciences',
  93: 'Systems theory; control',
  94: 'Information and communication, circuits',
  97: 'Mathematics education',
};

// ---------------------------------------------------------------------------
// Source collection metadata (module segment → display info)
// ---------------------------------------------------------------------------
const SOURCE_COLLECTIONS = {
  ErdosProblems:       { name: 'Erdős Problems',           url: 'https://www.erdosproblems.com' },
  Wikipedia:           { name: 'Wikipedia',                url: 'https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics' },
  GreensOpenProblems:  { name: "Green's Open Problems",    url: 'https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf' },
  HilbertProblems:     { name: 'Hilbert Problems',         url: 'https://en.wikipedia.org/wiki/Hilbert%27s_problems' },
  Millenium:           { name: 'Millennium Prize Problems', url: 'https://www.claymath.org/millennium-problems/' },
  Mathoverflow:        { name: 'MathOverflow',             url: 'https://mathoverflow.net' },
  OEIS:                { name: 'OEIS',                     url: 'https://oeis.org' },
  Arxiv:               { name: 'arXiv',                    url: 'https://arxiv.org/archive/math' },
  Paper:               { name: 'Papers',                   url: null },
  Books:               { name: 'Books',                    url: null },
  WrittenOnTheWallII:  { name: 'Written on the Wall II',   url: null },
  Kourovka:            { name: 'Kourovka Notebook',        url: 'https://arxiv.org/pdf/1401.0300' },
  Other:               { name: 'Other',                    url: null },
};

const GITHUB_BASE = 'https://github.com/google-deepmind/formal-conjectures/blob/main';
const GITHUB_API_BASE = 'https://api.github.com/repos/google-deepmind/formal-conjectures';

// ---------------------------------------------------------------------------
// Data processing helpers
// ---------------------------------------------------------------------------

/** Convert a module name to a GitHub file URL. */
function moduleToGitHubPath(module) {
  // Replace periods with slashes outside guillemets
  const withSlashes = module.replace(/«[^»]*»|\./g, (match) =>
    match[0] === '«' ? match : '/'
  );
  // and then strip Lean «guillemets» used to quote numeric/special segments
  const clean = withSlashes.replace(/[«»]/g, '');
  return `${clean}.lean`;
}
function moduleToGitHubURL(module) {
  return `${GITHUB_BASE}/${moduleToGitHubPath(module)}`;
}

/** Convert a module name to a Verso literate source page URL. */
function moduleToSourceURL(module) {
  // Use the same approach as moduleToGitHubPath: replace dots with slashes,
  // but preserve dots that are inside guillemets.
  const withSlashes = module.replace(/«[^»]*»|\./g, (match) =>
    match[0] === '«' ? match : '/'
  );
  // Add guillemets «» around path segments starting with a digit,
  // matching verso-html's output directory naming convention.
  const segments = withSlashes.split('/');
  const withGuillemets = segments.map(s =>
    // If already has guillemets, keep as-is; if starts with digit, wrap
    s.startsWith('«') ? s : /^\d/.test(s) ? `«${s}»` : s
  );
  return `/src/${withGuillemets.join('/')}/`;
}

/** Extract the source collection from a module name. */
function getCollection(module) {
  const parts = module.split('.');
  const key = parts[1]; // segment after 'FormalConjectures'
  return SOURCE_COLLECTIONS[key] || { name: key || 'Unknown', url: null };
}

/** Category metadata: label and CSS class for styling. */
const CATEGORY_META = {
  'research open':    { label: 'Open',          css: 'cat-open' },
  'research solved':  { label: 'Solved',        css: 'cat-solved' },
  'textbook':         { label: 'Textbook',      css: 'cat-textbook' },
  'test':             { label: 'Test',          css: 'cat-test' },
  'API':              { label: 'API',           css: 'cat-api' },
};

function getCategoryMeta(category) {
  return CATEGORY_META[category] || { label: category, css: 'cat-unknown' };
}

/** Enrich a raw theorem entry with derived fields. */
function processEntry(entry) {
  // Keep guillemets in theorem/module for exact lookups (avoids collisions
  // between e.g. «A.B».C and A.«B.C» which are distinct Lean names).
  // Provide display* variants with guillemets stripped for HTML rendering.
  const collection = getCollection(entry.module);
  const catMeta = getCategoryMeta(entry.category);
  const subjects = entry.subjects.map(code => ({
    code,
    name: AMS_SUBJECTS[parseInt(code, 10)] || `AMS ${code}`,
  }));
  // Pick only the fields the website actually uses. Avoids leaking large
  // unused fields (statement, docstring) into the client-side JSON.
  // Docstrings come from versoFragments instead.
  const hasFormalProof = !!entry.formalProofKind;
  return {
    theorem: entry.theorem,
    module: entry.module,
    category: entry.category,
    displayTheorem: entry.theorem.replace(/[«»]/g, ''),
    displayModule: entry.module.replace(/[«»]/g, ''),
    githubPath: moduleToGitHubPath(entry.module),
    githubUrl: moduleToGitHubURL(entry.module),
    sourceUrl: moduleToSourceURL(entry.module),
    collection: collection.name,
    collectionUrl: collection.url,
    categoryLabel: catMeta.label,
    categoryCss: catMeta.css,
    subjects,
    hasFormalProof,
    formalProofKind: entry.formalProofKind || null,
    formalProofLink: entry.formalProofLink || null,
  };
}

/** Compute site-wide statistics from processed entries. */
function computeStats(conjectures) {
  const byCategory = {};
  const byCollection = {};
  const bySubject = {};

  for (const c of conjectures) {
    byCategory[c.category] = (byCategory[c.category] || 0) + 1;
    byCollection[c.collection] = (byCollection[c.collection] || 0) + 1;
    for (const s of c.subjects) {
      bySubject[s.name] = (bySubject[s.name] || 0) + 1;
    }
  }

  return {
    total: conjectures.length,
    byCategory,
    byCollection,
    bySubject,
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

function getContributorHistory(repoRoot, githubPath) {
  let output = '';
  try {
    output = execFileSync('git', [
      '-C', repoRoot,
      'log',
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

async function buildContributorMetadata(conjectures) {
  const repoRoot = getGitRoot();
  if (!repoRoot) {
    console.log('  No git repository found; skipping contributor metadata.');
    return {};
  }

  const paths = Array.from(new Set(conjectures.map(c => c.githubPath).filter(Boolean)));
  const contributorsByPath = {};
  const contributorsByIdentity = new Map();

  for (const githubPath of paths) {
    const contributors = getContributorHistory(repoRoot, githubPath);
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

function collectionListHTML(byCollection) {
  return Object.entries(byCollection)
    .sort((a, b) => b[1] - a[1])
    .map(([name, count]) => `<li><a href="/browse/?collection=${encodeURIComponent(name)}">${name}</a> <span class="count-badge">${count}</span></li>`)
    .join('\n');
}

function subjectListHTML(bySubject) {
  return Object.entries(bySubject)
    .sort((a, b) => b[1] - a[1])
    .slice(0, 20) // top 20 subjects on landing page
    .map(([name, count]) => `<li><a href="/browse/?subject=${encodeURIComponent(name)}">${name}</a> <span class="count-badge">${count}</span></li>`)
    .join('\n');
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
  let rawData = [];
  if (fs.existsSync('data/conjectures.json')) {
    const parsed = JSON.parse(fs.readFileSync('data/conjectures.json', 'utf8'));
    // extract_names outputs { problems: [...], moduleDocstrings: {...} }
    rawData = parsed.problems || [];
  }

  if (rawData.length === 0) {
    console.error('Error: no conjectures loaded. Run `lake exe extract_names > site/data/conjectures.json` first.');
    process.exit(1);
  }

  const conjectures = rawData.map(processEntry);
  const stats = computeStats(conjectures);
  const advancedStats = computeAdvancedStats(conjectures);
  const contributors = await buildContributorMetadata(conjectures);

  // Load Verso literate fragments (module docstrings + const links)
  let versoFragments = { moduleDocs: {}, constLinks: {} };
  if (fs.existsSync('data/verso-fragments.json')) {
    versoFragments = JSON.parse(fs.readFileSync('data/verso-fragments.json', 'utf8'));
    console.log(`  Loaded ${Object.keys(versoFragments.moduleDocs).length} module docstrings, ${Object.keys(versoFragments.constLinks).length} constant links from Verso.`);
  } else {
    console.log('  No Verso fragments found (run extract_verso_fragments.py first).');
  }

  console.log(`  Loaded ${conjectures.length} conjectures.`);

  // Clean and recreate site directory
  if (fs.existsSync('site')) fs.rmSync('site', { recursive: true });
  fs.mkdirSync('site');

  // Copy static assets
  copyDir('src/css', 'site/assets/css');
  copyDir('src/js', 'site/assets/js');
  if (fs.existsSync('src/img')) copyDir('src/img', 'site/assets/img');
  if (fs.existsSync('src/fonts')) copyDir('src/fonts', 'site/assets/fonts');

  // Write processed data (for client-side pages)
  ensureDir('site/data');
  fs.writeFileSync(
    'site/data/conjectures.json',
    JSON.stringify({ conjectures, stats, advancedStats, amsSubjects: AMS_SUBJECTS, versoFragments, contributors }),
  );

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
    collectionList:  collectionListHTML(stats.byCollection),
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
  const statsHtml = readTemplate('stats.html');
  writePage('site/stats/index.html', applyBasePath(fill(statsHtml, {
    totalCount:           stats.total,
    subjectStatusTable:   subjectStatusTableHTML(advancedStats.subjectByCategory),
  })));

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
