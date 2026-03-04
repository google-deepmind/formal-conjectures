/**
 * theorem.js — powers the /theorem/ detail page.
 *
 * Reads ?name= from the URL, finds the theorem in the loaded data,
 * and renders the full detail view.
 */

'use strict';

const detailEl = document.getElementById('theorem-detail');

async function init() {
  const params = new URLSearchParams(window.location.search);
  const name   = params.get('name');

  if (!name) {
    renderError('No theorem name specified. Try browsing the <a href="/browse/">full list</a>.');
    return;
  }

  let data;
  try {
    data = await FC.loadData();
  } catch (e) {
    renderError(`Could not load data: ${FC.escapeHTML(e.message)}`);
    return;
  }

  const theorem = data.conjectures.find(c => c.theorem === name);
  if (!theorem) {
    renderError(`Theorem <code>${FC.escapeHTML(name)}</code> not found. It may have been renamed or removed.`);
    return;
  }

  // Update page title
  document.title = `${theorem.displayName} — Formal Conjectures`;

  // Find siblings (same module)
  const siblings = data.conjectures.filter(c => c.module === theorem.module);

  renderDetail(theorem, siblings);
}

function renderError(msg) {
  detailEl.innerHTML = `
    <div class="theorem-detail__breadcrumb">
      <a href="/browse/">&larr; Browse</a>
    </div>
    <div class="empty-state">
      <div class="empty-state__text">${msg}</div>
    </div>`;
}

function renderDetail(theorem, siblings) {
  const catMeta = FC.getCategoryMeta(theorem.category);

  // Subject pills HTML
  const subjectPillsHTML = theorem.subjects.length
    ? theorem.subjects.map(s =>
        `<span class="subject-pill">${FC.escapeHTML(s.name)} <span style="opacity:.6;font-size:.75em">(${FC.escapeHTML(s.code)})</span></span>`
      ).join('\n')
    : '<span style="color:var(--color-text-muted);font-size:.875rem">None listed</span>';

  // Collection link
  const collectionHTML = theorem.collectionUrl
    ? `<a href="${FC.escapeHTML(theorem.collectionUrl)}" target="_blank" rel="noopener">${FC.escapeHTML(theorem.collection)}</a>`
    : FC.escapeHTML(theorem.collection);

  // Siblings list
  const siblingsHTML = siblings.length > 1
    ? siblings.map(s => {
        const isCurrent = s.theorem === theorem.theorem;
        const sCatMeta = FC.getCategoryMeta(s.category);
        return `
          <div class="sibling-item ${isCurrent ? 'current' : ''}">
            <span class="badge ${sCatMeta.css}">${FC.escapeHTML(sCatMeta.label)}</span>
            ${isCurrent
              ? `<span style="font-weight:500;color:var(--color-text)">${FC.escapeHTML(s.displayName)}</span>`
              : `<a href="${FC.escapeHTML(FC.theoremURL(s.theorem))}">${FC.escapeHTML(s.displayName)}</a>`}
          </div>`;
      }).join('\n')
    : '';

  detailEl.innerHTML = `
    <div class="theorem-detail__breadcrumb">
      <a href="/browse/">&larr; Browse</a>
      &nbsp;&rsaquo;&nbsp;
      <a href="/browse/?collection=${encodeURIComponent(theorem.collection)}">${FC.escapeHTML(theorem.collection)}</a>
    </div>

    <header class="theorem-detail__header">
      <h1 class="theorem-detail__title">${FC.escapeHTML(theorem.displayName)}</h1>
      <span class="badge ${catMeta.css}" style="font-size:.9rem;padding:.3rem .9rem">${FC.escapeHTML(catMeta.label)}</span>
    </header>

    <div class="theorem-detail__section">
      <div class="detail-label">Full Lean name</div>
      <div class="detail-mono">${FC.escapeHTML(theorem.theorem)}</div>
    </div>

    <div class="theorem-detail__section">
      <div class="detail-label">Module</div>
      <div class="detail-mono">${FC.escapeHTML(theorem.module)}</div>
    </div>

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

    <div class="theorem-detail__section">
      <div class="detail-label">View source</div>
      <div class="detail-value">
        <a href="${FC.escapeHTML(theorem.githubUrl)}" target="_blank" rel="noopener">
          ${FC.escapeHTML(theorem.module.replace(/\./g, '/')}.lean on GitHub ↗
        </a>
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
      <a href="/browse/" class="btn btn-outline">&larr; Back to browse</a>
      <a href="${FC.escapeHTML(theorem.githubUrl)}" class="btn btn-outline" target="_blank" rel="noopener">
        View on GitHub ↗
      </a>
    </nav>
  `;
}

init();
