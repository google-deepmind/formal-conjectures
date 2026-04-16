/**
 * theorem.js — powers the /theorem/ detail page.
 *
 * Renders the theorem detail view with:
 * - Module docstring (from Verso, with rendered LaTeX/HTML)
 * - Problem description (docstring from Verso, with rendered LaTeX)
 * - Syntax-highlighted Lean code (fetched from Verso, with full interactive hovers)
 * - Links to full annotated source and GitHub
 */

'use strict';

const detailEl = document.getElementById('theorem-detail');
const _base = document.documentElement.dataset.base || '';

async function init() {
  const params = new URLSearchParams(window.location.search);
  const name   = params.get('name');

  if (!name) {
    renderError(`No theorem name specified. Try browsing the <a href="${_base}/browse/">full list</a>.`);
    return;
  }

  let data;
  try {
    data = await FC.loadData();
  } catch (e) {
    renderError(`Could not load data: ${FC.escapeHTML(e.message)}`);
    return;
  }

  // Look up by exact name (with guillemets) or by display name (guillemets stripped)
  const theorem = data.conjectures.find(c => c.theorem === name || c.displayTheorem === name);
  if (!theorem) {
    renderError(`Theorem <code>${FC.escapeHTML(name)}</code> not found. It may have been renamed or removed.`);
    return;
  }

  document.title = `${theorem.displayTheorem} — Formal Conjectures`;
  const siblings = data.conjectures.filter(c => c.module === theorem.module);
  const verso = data.versoFragments || { moduleDocs: {}, constLinks: {} };

  renderDetail(theorem, siblings, verso);
}

/**
 * Find the Verso constant link for a theorem.
 * extract_names uses "FormalConjectures.ErdosProblems.830.erdos_830.parts.i"
 * Verso uses "Erdos830.erdos_830.parts.i".
 * We try progressively shorter suffixes.
 */
function findVersoLink(theoremName, constLinks) {
  const parts = theoremName.split('.');
  for (let i = 0; i < parts.length; i++) {
    const suffix = parts.slice(i).join('.');
    if (constLinks[suffix]) return constLinks[suffix];
  }
  return null;
}

// ─── Verso asset and script loading ────────────────────────────────

/** Helper to load an external script and return a Promise. */
function loadScript(src) {
  return new Promise((resolve, reject) => {
    if (document.querySelector(`script[src="${src}"]`)) { resolve(); return; }
    const s = document.createElement('script');
    s.src = src;
    s.onload = resolve;
    s.onerror = () => { console.warn(`Failed to load script: ${src}`); resolve(); };
    document.head.appendChild(s);
  });
}

/**
 * Load Verso CSS + JS for code rendering and interactive hovers.
 * Returns a Promise that resolves once popper.js + tippy.js are loaded.
 */
function loadVersoAssets() {
  if (document.getElementById('verso-code-css')) return Promise.resolve();

  // Load Verso's code.css for syntax highlighting
  const codeLink = document.createElement('link');
  codeLink.id = 'verso-code-css';
  codeLink.rel = 'stylesheet';
  codeLink.href = `${_base}/src/code.css`;
  document.head.appendChild(codeLink);

  // Load tippy border CSS for hover tooltips
  const tippyLink = document.createElement('link');
  tippyLink.rel = 'stylesheet';
  tippyLink.href = `${_base}/src/tippy-border.css`;
  document.head.appendChild(tippyLink);

  // Inline CSS: override/supplement Verso's code.css
  const style = document.createElement('style');
  style.textContent = `
    /* Override Verso's body overflow:hidden which breaks page scrolling */
    body { overflow: visible !important; overflow-y: auto !important; }
    /* Hide tactic goal states (shown via tippy on hover) */
    .hl.lean .tactic-state { display: none; }
    .hl.lean .tactic-toggle { position: absolute; opacity: 0; height: 0; width: 0; }
    .hl.lean .tactic-toggle:checked ~ .tactic-state { display: inline-block; }
    /* Hide compiler messages inline (but allow them in tippy popups) */
    .verso-code-container .hover-info.messages { display: none; }
    /* Style warning underlines */
    .hl.lean .has-info .token:not(.tactic-state) {
      text-decoration-style: wavy;
      text-decoration-line: underline;
    }
    .hl.lean .has-info.warning .token:not(.tactic-state) {
      text-decoration-color: #c09020;
    }
    /* Inter-text spacing */
    .hl.lean .inter-text { white-space: pre; }
    /* Make the code container match Verso's clean look */
    .verso-code-container {
      background: #fff;
      border: 1px solid #e0e0e0;
      border-radius: 6px;
      padding: 0;
    }
    .verso-code-container code.hl.lean.block {
      font-size: 16px;
      display: block;
      padding: 1.25rem;
    }
    /* Tooltip spacing: separator between type signature and docstring */
    .hover-info .sep {
      display: block;
      height: 1px;
      background: #e0e0e0;
      margin: .5rem 0;
    }
    .hover-info code.docstring {
      display: block;
      white-space: pre-wrap;
      margin-top: .25rem;
    }
    /* Tactic state layout: hypotheses as table rows, goals as blocks */
    .hl.lean .hypotheses { display: table; border-spacing: 0; }
    .hl.lean .hypothesis { display: table-row; }
    .hl.lean .hypothesis > * { display: table-cell; padding-right: .3em; }
    .hl.lean .goal, .hl.lean .conclusion { display: block; margin-top: .4em; }
  `;
  document.head.appendChild(style);

  // Load popper.js then tippy.js from the Verso source directory
  return loadScript(`${_base}/src/popper.js`)
    .then(() => loadScript(`${_base}/src/tippy.js`));
}

// ─── Fetch code block + hover data ─────────────────────────────────

/**
 * Fetch the highlighted code block for a theorem from its Verso page.
 * Also fetches the -verso-docs.json hover data for interactive tooltips.
 */
async function fetchVersoCodeBlock(versoLink) {
  try {
    const pagePath = versoLink.url.split('#')[0]; // "/FormalConjectures/.../«17»/"
    const pageUrl = `${_base}/src${pagePath}`;
    // -verso-docs.json is at the literate root, shared across all pages
    const docsUrl = `${_base}/src/-verso-docs.json`;

    const [pageResp, docsResp] = await Promise.all([
      fetch(pageUrl),
      fetch(docsUrl).catch(() => null),
    ]);
    if (!pageResp.ok) return null;
    const html = await pageResp.text();
    const docsData = docsResp && docsResp.ok ? await docsResp.json() : null;

    // Parse the HTML and find the code block containing our theorem's anchor
    const parser = new DOMParser();
    const doc = parser.parseFromString(html, 'text/html');
    const anchor = doc.getElementById(versoLink.anchor);
    if (!anchor) return null;

    // Walk up to find the enclosing <code class="hl lean block">
    let el = anchor;
    while (el && !(el.tagName === 'CODE' && el.classList.contains('hl'))) {
      el = el.parentElement;
    }
    if (!el) return null;

    return { codeHtml: el.outerHTML, docsData };
  } catch (e) {
    console.warn('Failed to fetch Verso code:', e);
    return null;
  }
}

// ─── Verso hover initialization (replicates Verso inline script) ───

/**
 * Initialize Verso-style interactive hovers on the injected code block.
 * This replicates the behavior of Verso's inline initialization script,
 * including binding highlights, tactic toggles, and type-info tooltips.
 */
function initVersoHovers(container, docsData) {
  if (typeof tippy !== 'function') {
    console.warn('tippy.js not loaded, skipping hover init');
    return;
  }

  // 1. Binding highlight on mouseover/mouseout
  for (const c of container.querySelectorAll('.hl.lean .token')) {
    if (c.dataset.binding != '') {
      c.addEventListener('mouseover', () => {
        const context = c.closest('.hl.lean')?.dataset.leanContext;
        for (const example of container.querySelectorAll('.hl.lean')) {
          if (example.dataset.leanContext == context) {
            for (const tok of example.querySelectorAll('.token')) {
              if (c.dataset.binding == tok.dataset.binding) {
                tok.classList.add('binding-hl');
              }
            }
          }
        }
      });
    }
    c.addEventListener('mouseout', () => {
      for (const tok of container.querySelectorAll('.hl.lean .token')) {
        tok.classList.remove('binding-hl');
      }
    });
  }

  // 2. Helpers
  function blockedByTactic(elem) {
    let parent = elem.parentNode;
    while (parent && 'classList' in parent) {
      if (parent.classList.contains('tactic')) {
        const toggle = parent.querySelector('input.tactic-toggle');
        if (toggle) return !toggle.checked;
      }
      parent = parent.parentNode;
    }
    return false;
  }

  function blockedByTippy(elem) {
    let block = elem;
    const topLevel = new Set(['section', 'body', 'html', 'nav', 'header', 'main']);
    while (block.parentNode && !topLevel.has(block.parentNode.nodeName.toLowerCase())) {
      block = block.parentNode;
    }
    for (const child of block.querySelectorAll('.token, .has-info')) {
      if (child._tippy && child._tippy.state.isVisible) return true;
    }
    return false;
  }

  function hideParentTooltips(element) {
    let parent = element.parentElement;
    while (parent) {
      if (parent._tippy) parent._tippy.hide();
      parent = parent.parentElement;
    }
  }

  // 3. Set tippy themes on elements
  container.querySelectorAll(
    '.hl.lean .const.token, .hl.lean .keyword.token, .hl.lean .literal.token, ' +
    '.hl.lean .option.token, .hl.lean .var.token, .hl.lean .typed.token, ' +
    '.hl.lean .level-var, .hl.lean .level-const, .hl.lean .level-op, .hl.lean .sort'
  ).forEach(el => el.setAttribute('data-tippy-theme', 'lean'));

  container.querySelectorAll('.hl.lean .has-info.warning').forEach(el =>
    el.setAttribute('data-tippy-theme', 'warning message'));
  container.querySelectorAll('.hl.lean .has-info.information').forEach(el =>
    el.setAttribute('data-tippy-theme', 'info message'));
  container.querySelectorAll('.hl.lean .has-info.error').forEach(el =>
    el.setAttribute('data-tippy-theme', 'error message'));
  container.querySelectorAll('.hl.lean .tactic').forEach(el =>
    el.setAttribute('data-tippy-theme', 'tactic'));

  // 4. Initialize tippy instances
  const tippyProps = {
    maxWidth: 'none',
    appendTo: () => document.body,
    interactive: true,
    delay: [100, null],
    followCursor: 'initial',
    onShow(inst) {
      if (inst.reference.className == 'tactic') {
        const toggle = inst.reference.querySelector('input.tactic-toggle');
        if (toggle && toggle.checked) return false;
        hideParentTooltips(inst.reference);
      } else if (inst.reference.querySelector('.hover-info') || 'versoHover' in inst.reference.dataset) {
        if (blockedByTactic(inst.reference)) return false;
        if (blockedByTippy(inst.reference)) return false;
      } else {
        return false;
      }
    },
    content(tgt) {
      const content = document.createElement('span');
      if (tgt.className == 'tactic') {
        const state = tgt.querySelector('.tactic-state')?.cloneNode(true);
        if (state) {
          state.style.display = 'block';
          content.appendChild(state);
          content.style.display = 'block';
          content.className = 'hl lean popup';
        }
      } else {
        content.className = 'hl lean';
        content.style.display = 'block';
        content.style.maxHeight = '300px';
        content.style.overflowY = 'auto';
        content.style.overflowX = 'hidden';
        const hoverId = tgt.dataset.versoHover;
        const hoverInfo = tgt.querySelector('.hover-info');
        if (hoverId && docsData) {
          const data = docsData[hoverId];
          if (data) {
            const info = document.createElement('span');
            info.className = 'hover-info';
            info.style.display = 'block';
            info.innerHTML = data;
            // Rewrite links: hover data has relative paths like /FormalConjectures/...
            // which need to be prefixed with /src/ to point to Verso pages
            for (const a of info.querySelectorAll('a[href]')) {
              const href = a.getAttribute('href');
              if (href && href.startsWith('/') && !href.startsWith('/src/')) {
                a.setAttribute('href', `${_base}/src${href}`);
              }
            }
            content.appendChild(info);
          }
        } else if (hoverInfo) {
          const clone = hoverInfo.cloneNode(true);
          clone.style.display = 'block';
          content.appendChild(clone);
        }
        const extraLinks = tgt.parentElement?.dataset['versoLinks'];
        if (extraLinks) {
          try {
            const extras = JSON.parse(extraLinks);
            const links = document.createElement('ul');
            links.className = 'extra-doc-links';
            extras.forEach(l => {
              const li = document.createElement('li');
              li.innerHTML = `<a href="${l.href}" title="${l.long}">${l.short}</a>`;
              links.appendChild(li);
            });
            content.appendChild(links);
          } catch (_) { }
        }
      }
      return content;
    },
  };

  tippy(
    container.querySelectorAll(
      '.hl.lean .const.token, .hl.lean .keyword.token, .hl.lean .literal.token, ' +
      '.hl.lean .option.token, .hl.lean .var.token, .hl.lean .typed.token, ' +
      '.hl.lean .has-info, .hl.lean .tactic, ' +
      '.hl.lean .level-var, .hl.lean .level-const, .hl.lean .level-op, .hl.lean .sort'
    ),
    tippyProps
  );
}

// ─── Page rendering ────────────────────────────────────────────────

function renderError(msg) {
  detailEl.innerHTML = `
    <div class="theorem-detail__breadcrumb">
      <a href="${_base}/browse/">&larr; Browse</a>
    </div>
    <div class="empty-state">
      <div class="empty-state__text">${msg}</div>
    </div>`;
}

function renderDetail(theorem, siblings, verso) {
  const catMeta = FC.getCategoryMeta(theorem.category);

  // Subject pills
  const subjectPillsHTML = theorem.subjects.length
    ? theorem.subjects.map(s =>
        `<span class="subject-pill">${FC.escapeHTML(s.name)} <span style="opacity:.6;font-size:.75em">(${FC.escapeHTML(s.code)})</span></span>`
      ).join('\n')
    : '<span style="color:var(--color-text-muted);font-size:.875rem">None listed</span>';

  // Collection link
  const collectionHTML = theorem.collectionUrl
    ? `<a href="${FC.escapeHTML(theorem.collectionUrl)}" target="_blank" rel="noopener">${FC.escapeHTML(theorem.collection)}</a>`
    : FC.escapeHTML(theorem.collection);

  // Siblings
  const siblingsHTML = siblings.length > 1
    ? siblings.map(s => {
        const isCurrent = s.theorem === theorem.theorem;
        const sCatMeta = FC.getCategoryMeta(s.category);
        return `
          <div class="sibling-item ${isCurrent ? 'current' : ''}">
            <span class="badge ${sCatMeta.css}">${FC.escapeHTML(sCatMeta.label)}</span>
            ${isCurrent
          ? `<span style="font-weight:500;color:var(--color-text)">${FC.escapeHTML(s.displayTheorem)}</span>`
          : `<a href="${FC.escapeHTML(FC.theoremURL(s.displayTheorem))}">${FC.escapeHTML(s.displayTheorem)}</a>`}
          </div>`;
      }).join('\n')
    : '';

  // --- Verso data ---
  const moduleDocKey = (theorem.sourceUrl || '').replace(/^\/src/, '');
  const moduleDocHTML = verso.moduleDocs[moduleDocKey] || '';
  const versoLink = findVersoLink(theorem.theorem, verso.constLinks);
  const docHtml = versoLink && versoLink.docHtml ? versoLink.docHtml : '';
  const versoSourceUrl = versoLink
    ? `${_base}/src${versoLink.url}`
    : theorem.sourceUrl
      ? `${_base}${theorem.sourceUrl}`
      : null;

  // Module overview section (with module name in heading)
  const moduleDocSection = moduleDocHTML ? `
    <div class="theorem-detail__section verso-module-doc">
      <div class="detail-label">Module overview
        <span style="font-weight:400;font-size:.8rem;margin-left:.5rem;color:var(--color-text-muted);text-transform:none">${FC.escapeHTML(theorem.displayModule)}</span>
      </div>
      <div class="verso-doc-content">${moduleDocHTML}</div>
    </div>` : '';

  // Problem description
  const docSection = docHtml ? `
    <div class="theorem-detail__section">
      <div class="detail-label">Problem description</div>
      <div class="verso-doc-content">${docHtml}</div>
    </div>` : '';

  // Code placeholder (async-filled) with GitHub + Verso links
  const codeSection = versoLink ? `
    <div class="theorem-detail__section">
      <div class="detail-label">
        Lean code
        <a href="${FC.escapeHTML(theorem.githubUrl)}" target="_blank" rel="noopener"
           style="font-weight:400;font-size:.8rem;margin-left:.5rem">GitHub ↗</a>
        ${versoSourceUrl ? `<a href="${versoSourceUrl}" target="_blank" rel="noopener"
           style="font-weight:400;font-size:.8rem;margin-left:.5rem">Verso ↗</a>` : ''}
      </div>
      <div id="verso-code-container" class="verso-code-container">
        <div class="verso-code-loading">Loading highlighted code…</div>
      </div>
    </div>` : '';

  detailEl.innerHTML = `
    <div class="theorem-detail__breadcrumb">
      <a href="${_base}/browse/">&larr; Browse</a>
      &nbsp;&rsaquo;&nbsp;
      <a href="${_base}/browse/?collection=${encodeURIComponent(theorem.collection)}">${FC.escapeHTML(theorem.collection)}</a>
    </div>

    <header class="theorem-detail__header">
      <h1 class="theorem-detail__title">${FC.escapeHTML(theorem.displayTheorem)}</h1>
      <span class="badge ${catMeta.css}" style="font-size:.9rem;padding:.3rem .9rem">${FC.escapeHTML(catMeta.label)}</span>
    </header>

    ${moduleDocSection}

    ${docSection}

    ${codeSection}



    <div class="theorem-detail__section">
      <div class="detail-label">Source collection</div>
      <div class="detail-value">${collectionHTML}</div>
    </div>

    <div class="theorem-detail__section">
      <div class="detail-label">AMS subjects</div>
      <div style="display:flex;flex-wrap:wrap;gap:.4rem;margin-top:.25rem">
        ${subjectPillsHTML}
      </div>
    </div>

    ${siblings.length > 1 ? `
    <div class="theorem-detail__section">
      <div class="detail-label">Other results in this file</div>
      <div class="siblings-list">
        ${siblingsHTML}
      </div>
    </div>` : ''}

    <nav class="theorem-detail__nav" aria-label="Page actions">
      <a href="${_base}/browse/" class="btn btn-outline">&larr; Back to browse</a>
      ${versoSourceUrl ? `<a href="${versoSourceUrl}" class="btn btn-outline">View annotated source</a>` : ''}
      <a href="${FC.escapeHTML(theorem.githubUrl)}" class="btn btn-outline" target="_blank" rel="noopener">
        View on GitHub ↗
      </a>
    </nav>
  `;

  // Render LaTeX in docstrings
  renderLatex();

  // Async: load Verso assets, fetch code block, and initialize hovers
  if (versoLink) {
    loadVersoAssets().then(() => fetchVersoCodeBlock(versoLink)).then(result => {
      const container = document.getElementById('verso-code-container');
      if (!container) return;
      if (result && result.codeHtml) {
        container.innerHTML = result.codeHtml;
        // Rewrite relative links in code block: Verso uses paths like
        // "FormalConjectures/..." which resolve against /theorem/ page.
        // Fix them to point to /src/ Verso pages instead.
        for (const a of container.querySelectorAll('a[href]')) {
          const href = a.getAttribute('href');
          if (href && !href.startsWith('http') && !href.startsWith('/')) {
            a.setAttribute('href', `${_base}/src/${href}`);
          } else if (href && href.startsWith('/') && !href.startsWith('/src/') && !href.startsWith(_base)) {
            a.setAttribute('href', `${_base}/src${href}`);
          }
        }
        // Initialize interactive hovers on the injected code
        initVersoHovers(container, result.docsData);
      } else {
        container.innerHTML = `<div class="verso-code-fallback">
          <a href="${versoSourceUrl || '#'}">View in annotated source →</a>
        </div>`;
      }
    });
  }
}

// ─── KaTeX rendering ───────────────────────────────────────────────

/**
 * Render LaTeX in docstring elements using KaTeX auto-render.
 */
function renderLatex() {
  function doRender() {
    if (typeof renderMathInElement !== 'function') {
      setTimeout(doRender, 100);
      return;
    }
    for (const el of document.querySelectorAll('.verso-doc-content')) {
      renderMathInElement(el, {
        delimiters: [
          { left: '$$', right: '$$', display: true },
          { left: '$', right: '$', display: false },
        ],
        throwOnError: false,
      });
    }
  }
  doRender();
}

init();
