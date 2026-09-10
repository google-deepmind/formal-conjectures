/* Display adapters for the canonical native catalog; shared by build and browser. */
'use strict';
const FCCatalog = (() => {
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
function moduleToGitHubURL(module, source) {
  const file = moduleToGitHubPath(module).split('/').map(encodeURIComponent).join('/');
  return `https://github.com/${source.repository}/blob/${source.commit}/${file}`;
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
function processEntry(entry, source) {
  // Keep guillemets in theorem/module for exact lookups (avoids collisions
  // between e.g. «A.B».C and A.«B.C» which are distinct Lean names).
  // Provide display* variants with guillemets stripped for HTML rendering.
  const collection = getCollection(entry.module);
  const catMeta = getCategoryMeta(entry.category);
  const subjects = entry.subjects.map(code => ({
    code,
    name: AMS_SUBJECTS[parseInt(code, 10)] || `AMS ${code}`,
  }));
  // Presentation fields are derived in memory; native facts remain unchanged.
  // A declaration can carry several `formal_proof` annotations. `hasFormalProof` stays a
  // boolean about the conjecture, so the landing-page and stats counts keep counting
  // conjectures rather than proofs.
  const formalProofs = entry.formalProofs || [];
  const hasFormalProof = formalProofs.length > 0;
  return {
    ...entry,
    theorem: entry.theorem,
    module: entry.module,
    category: entry.category,
    displayTheorem: entry.theorem.replace(/[«»]/g, ''),
    displayModule: entry.module.replace(/[«»]/g, ''),
    githubPath: moduleToGitHubPath(entry.module),
    githubUrl: moduleToGitHubURL(entry.module, source),
    sourceUrl: moduleToSourceURL(entry.module),
    collection: collection.name,
    collectionUrl: collection.url,
    categoryLabel: catMeta.label,
    categoryCss: catMeta.css,
    subjects,
    hasFormalProof,
    formalProofs,
  };
}


/** JSON objects have no meaningful member order. */
function sameJSON(left, right) {
  if (left === right) return true;
  if (!left || !right || typeof left !== 'object' || typeof right !== 'object' ||
      Array.isArray(left) !== Array.isArray(right)) return false;
  const keys = Object.keys(left);
  return keys.length === Object.keys(right).length &&
    keys.every(key => Object.prototype.hasOwnProperty.call(right, key) && sameJSON(left[key], right[key]));
}

/** Exact identities take priority; display aliases must be unique. */
function resolveTheorem(entries, name) {
  const exact = entries.find(entry => entry.theorem === name);
  if (exact) return exact;
  const matches = entries.filter(entry => entry.displayTheorem === name);
  if (matches.length > 1) throw new Error('Ambiguous display name. Use the full Lean name, including quotation marks.');
  return matches[0];
}

return {sameJSON, resolveTheorem, AMS_SUBJECTS, SOURCE_COLLECTIONS, getCategoryMeta, moduleToGitHubPath, moduleToSourceURL, processEntry};
})();
if (typeof module !== 'undefined') module.exports = FCCatalog;
