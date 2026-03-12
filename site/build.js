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

// ---------------------------------------------------------------------------
// Data processing helpers
// ---------------------------------------------------------------------------

/** Convert a module name to a GitHub file URL. */
function moduleToGitHubURL(module) {
  // Strip Lean «guillemets» used to quote numeric/special segments
  const clean = module.replace(/[«»]/g, '');
  return `${GITHUB_BASE}/${clean.replace(/\./g, '/')}.lean`;
}

/** Extract the source collection from a module name. */
function getCollection(module) {
  const parts = module.split('.');
  const key = parts[1]; // segment after 'FormalConjectures'
  return SOURCE_COLLECTIONS[key] || { name: key || 'Unknown', url: null };
}

/** Category metadata: label and CSS class for styling. */
const CATEGORY_META = {
  'research open':             { label: 'Open',             css: 'cat-open' },
  'research solved':           { label: 'Solved',           css: 'cat-solved' },
  'research formally solved':  { label: 'Formally Solved',  css: 'cat-formal' },
  'graduate':                  { label: 'Graduate',         css: 'cat-graduate' },
  'undergraduate':             { label: 'Undergraduate',    css: 'cat-undergrad' },
  'high_school':               { label: 'High School',      css: 'cat-highschool' },
  'test':                      { label: 'Test',             css: 'cat-test' },
  'API':                       { label: 'API',              css: 'cat-api' },
};

function getCategoryMeta(category) {
  return CATEGORY_META[category] || { label: category, css: 'cat-unknown' };
}

/** Enrich a raw theorem entry with derived fields. */
function processEntry(entry) {
  // Strip Lean «guillemets» from names for display
  const theorem = entry.theorem.replace(/[«»]/g, '');
  const module = entry.module.replace(/[«»]/g, '');
  const collection = getCollection(module);
  const catMeta = getCategoryMeta(entry.category);
  const subjects = entry.subjects.map(code => ({
    code,
    name: AMS_SUBJECTS[parseInt(code, 10)] || `AMS ${code}`,
  }));
  return {
    ...entry,
    theorem,
    module,
    githubUrl: moduleToGitHubURL(entry.module),
    collection: collection.name,
    collectionUrl: collection.url,
    categoryLabel: catMeta.label,
    categoryCss: catMeta.css,
    subjects,
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
// HTML snippet generators
// ---------------------------------------------------------------------------

function statsCard(value, label) {
  return `<div class="stat-card"><span class="stat-value">${value}</span><span class="stat-label">${label}</span></div>`;
}

function categoryStatsHTML(byCategory) {
  const order = [
    'research open', 'research solved', 'research formally solved',
    'graduate', 'undergraduate', 'high_school', 'test', 'API',
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

// ---------------------------------------------------------------------------
// Main build
// ---------------------------------------------------------------------------

function main() {
  console.log('Building Formal Conjectures website...');

  // Read raw data
  let rawData = [];
  if (fs.existsSync('data/conjectures.json')) {
    try {
      rawData = JSON.parse(fs.readFileSync('data/conjectures.json', 'utf8'));
    } catch (e) {
      console.warn('Warning: could not parse data/conjectures.json:', e.message);
    }
  }

  const conjectures = rawData.map(processEntry);
  const stats = computeStats(conjectures);

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
    JSON.stringify({ conjectures, stats, amsSubjects: AMS_SUBJECTS }),
  );

  // ---- Landing page ----
  const indexHtml = readTemplate('index.html');
  writePage('site/index.html', applyBasePath(fill(indexHtml, {
    totalCount:      stats.total,
    openCount:       stats.byCategory['research open'] || 0,
    solvedCount:     stats.byCategory['research solved'] || 0,
    formalCount:     stats.byCategory['research formally solved'] || 0,
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
  return html.replace(/(href|src)="\/(?!\/)/g, `$1="${BASE_PATH}/`);
}

main();
