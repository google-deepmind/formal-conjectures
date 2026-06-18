/**
 * voting.js - giscus-backed difficulty voting for theorem pages.
 *
 * The site stays static: the range control selects a stable GitHub Discussion
 * bucket, while giscus handles GitHub sign-in, reactions, and comments.
 */

'use strict';

(function () {
  const GISCUS_ORIGIN = 'https://giscus.app';
  const STORAGE_PREFIX = 'fc_difficulty_vote:';
  const DEFAULT_DIFFICULTY = 5;
  const MIN_DIFFICULTY = 1;
  const MAX_DIFFICULTY = 10;

  const DEFAULT_GISCUS_SITE = 'upstream';
  const GISCUS_CONFIGS = {
    upstream: {
      repo: 'google-deepmind/formal-conjectures',
      repoId: 'R_kgDOOogmBw',
      category: 'Polls',
      categoryId: 'DIC_kwDOOogmB84C3u0D',
      hosts: ['google-deepmind.github.io'],
      theme: 'noborder_light',
      lang: 'en',
    },
    paulLezFork: {
      repo: 'Paul-Lez/formal-conjectures',
      repoId: 'R_kgDORiWUfA',
      category: 'Polls',
      categoryId: 'DIC_kwDORiWUfM4C_btZ',
      hosts: ['paul-lez.github.io'],
      theme: 'noborder_light',
      lang: 'en',
    },
  };

  const DIFFICULTY_SCALE = {
    1: {
      label: 'Student-level',
      description: 'Suitable for a strong student or reading-course project.',
    },
    2: {
      label: 'Graduate-level',
      description: 'Requires standard graduate material and careful work.',
    },
    3: {
      label: 'Advanced graduate',
      description: 'A hard graduate or seminar problem, but not really research-level.',
    },
    4: {
      label: 'Entry-level research',
      description: 'Plausible as a first research problem with good guidance.',
    },
    5: {
      label: 'Standard research',
      description: 'Approachable to an experienced specialist using current methods.',
    },
    6: {
      label: 'Nonstandard research',
      description: 'Existing techniques may apply only indirectly; likely needs a clever adaptation.',
    },
    7: {
      label: 'Methodologically difficult',
      description: 'A genuinely new trick or local method seems likely to be required.',
    },
    8: {
      label: 'Expert-level',
      description: 'Several experts could reasonably have thought seriously about it; a solution would be notable.',
    },
    9: {
      label: 'Breakthrough',
      description: 'Would likely unlock progress beyond the problem itself.',
    },
    10: {
      label: 'Landmark breakthrough',
      description: 'Field-shaping or Millennium-class; use sparingly.',
    },
  };

  function clampDifficulty(value) {
    const n = Number.parseInt(value, 10);
    if (Number.isNaN(n)) return DEFAULT_DIFFICULTY;
    return Math.min(MAX_DIFFICULTY, Math.max(MIN_DIFFICULTY, n));
  }

  function theoremKey(theorem) {
    return theorem?.theorem || theorem?.displayTheorem || 'unknown';
  }

  function displayName(theorem) {
    return theorem?.displayTheorem || theoremKey(theorem);
  }

  function hashString(value) {
    let hash = 2166136261;
    const input = String(value);
    for (let i = 0; i < input.length; i += 1) {
      hash ^= input.charCodeAt(i);
      hash = Math.imul(hash, 16777619);
    }
    return (hash >>> 0).toString(36);
  }

  function truncate(value, maxLength) {
    const text = String(value).replace(/\s+/g, ' ').trim();
    if (text.length <= maxLength) return text;
    return `${text.slice(0, maxLength - 3)}...`;
  }

  function storageKey(theorem) {
    return `${STORAGE_PREFIX}${theoremKey(theorem)}`;
  }

  function storedDifficulty(theorem) {
    try {
      return clampDifficulty(localStorage.getItem(storageKey(theorem)));
    } catch (_) {
      return DEFAULT_DIFFICULTY;
    }
  }

  function saveDifficulty(theorem, value) {
    try {
      localStorage.setItem(storageKey(theorem), String(value));
    } catch (_) {
      // Private browsing or disabled storage should not block the widget.
    }
  }

  function difficultyTerm(theorem, value) {
    const name = truncate(displayName(theorem), 150);
    return `Difficulty ${value}/10: ${name} [${hashString(theoremKey(theorem))}]`;
  }

  function difficultyDescription(theorem, value) {
    const info = difficultyInfo(value);
    return [
      `Difficulty bucket ${value}/10 (${info.label}) for ${displayName(theorem)}.`,
      info.description,
      `Stable theorem id: ${theoremKey(theorem)}.`,
    ].join(' ');
  }

  function syncPageDescription(theorem, value) {
    const meta = document.querySelector('meta[name="description"]');
    if (meta) meta.setAttribute('content', difficultyDescription(theorem, value));
  }

  function difficultyInfo(value) {
    return DIFFICULTY_SCALE[value] || DIFFICULTY_SCALE[DEFAULT_DIFFICULTY];
  }

  function difficultyLabel(value) {
    return difficultyInfo(value).label;
  }

  function difficultyText(value) {
    return difficultyInfo(value).description;
  }

  function meterWidth(value) {
    return `${((value - MIN_DIFFICULTY) / (MAX_DIFFICULTY - MIN_DIFFICULTY)) * 100}%`;
  }

  function pluralize(count, singular, plural) {
    return `${count.toLocaleString()} ${count === 1 ? singular : plural}`;
  }

  function currentGiscusConfig() {
    const hostname = window.location.hostname.toLowerCase().replace(/^www\./, '');
    return Object.values(GISCUS_CONFIGS).find((config) => config.hosts.includes(hostname)) ||
      GISCUS_CONFIGS[DEFAULT_GISCUS_SITE];
  }

  function makeScript(theorem, value) {
    const config = currentGiscusConfig();
    const script = document.createElement('script');
    script.src = `${GISCUS_ORIGIN}/client.js`;
    script.async = true;
    script.crossOrigin = 'anonymous';
    script.setAttribute('data-repo', config.repo);
    script.setAttribute('data-repo-id', config.repoId);
    script.setAttribute('data-category', config.category);
    script.setAttribute('data-category-id', config.categoryId);
    script.setAttribute('data-mapping', 'specific');
    script.setAttribute('data-term', difficultyTerm(theorem, value));
    script.setAttribute('data-description', difficultyDescription(theorem, value));
    script.setAttribute('data-strict', '1');
    script.setAttribute('data-reactions-enabled', '1');
    script.setAttribute('data-emit-metadata', '1');
    script.setAttribute('data-input-position', 'top');
    script.setAttribute('data-theme', config.theme);
    script.setAttribute('data-lang', config.lang);
    return script;
  }

  function updateStatus(root, value, discussion) {
    const status = root.querySelector('.difficulty-vote__status');
    if (!status) return;

    if (!discussion) {
      status.textContent = `GitHub bucket: ${value}/10`;
      return;
    }

    const count = discussion.reactionCount || 0;
    status.textContent = `${pluralize(count, 'reaction', 'reactions')} in the ${value}/10 bucket`;
  }

  function updateReadout(root, value) {
    const number = root.querySelector('.difficulty-vote__number');
    const label = root.querySelector('.difficulty-vote__label');
    const description = root.querySelector('.difficulty-vote__description');
    const meter = root.querySelector('.difficulty-vote__meter-fill');
    if (number) number.textContent = String(value);
    if (label) label.textContent = difficultyLabel(value);
    if (description) description.textContent = difficultyText(value);
    if (meter) meter.style.width = meterWidth(value);
  }

  function loadGiscus(root, theorem, value) {
    const mount = root.querySelector('.giscus');
    if (!mount) return;
    syncPageDescription(theorem, value);
    mount.innerHTML = '';
    mount.appendChild(makeScript(theorem, value));
  }

  function renderDifficultyVote(theorem, container) {
    if (!container) return;

    const initialValue = storedDifficulty(theorem);
    container.innerHTML = `
      <div class="difficulty-vote">
        <div class="difficulty-vote__control">
          <div class="difficulty-vote__topline">
            <div class="difficulty-vote__readout" aria-live="polite">
              <span class="difficulty-vote__number">${initialValue}</span>
              <span class="difficulty-vote__denominator">/10</span>
              <span class="difficulty-vote__label">${FC.escapeHTML(difficultyLabel(initialValue))}</span>
            </div>
            <span class="difficulty-vote__status">GitHub bucket: ${initialValue}/10</span>
          </div>
          <p class="difficulty-vote__description">${FC.escapeHTML(difficultyText(initialValue))}</p>
          <div class="difficulty-vote__range-row">
            <span class="difficulty-vote__end">1</span>
            <div class="difficulty-vote__range-wrap">
              <div class="difficulty-vote__meter" aria-hidden="true">
                <span class="difficulty-vote__meter-fill" style="width:${meterWidth(initialValue)}"></span>
              </div>
              <input class="difficulty-vote__range" type="range"
                min="${MIN_DIFFICULTY}" max="${MAX_DIFFICULTY}" step="1" value="${initialValue}"
                aria-label="Difficulty rating from 1 to 10">
            </div>
            <span class="difficulty-vote__end">10</span>
          </div>
        </div>
        <div class="difficulty-vote__giscus-shell">
          <div class="giscus"></div>
        </div>
      </div>
    `;

    const range = container.querySelector('.difficulty-vote__range');
    let selectedValue = initialValue;

    const commitValue = () => {
      selectedValue = clampDifficulty(range.value);
      saveDifficulty(theorem, selectedValue);
      updateReadout(container, selectedValue);
      updateStatus(container, selectedValue, null);
      loadGiscus(container, theorem, selectedValue);
    };

    range.addEventListener('input', () => {
      updateReadout(container, clampDifficulty(range.value));
    });
    range.addEventListener('change', commitValue);

    window.addEventListener('message', (event) => {
      if (event.origin !== GISCUS_ORIGIN) return;
      const data = event.data?.giscus;
      if (!data || !('discussion' in data)) return;
      updateStatus(container, selectedValue, data.discussion);
    });

    loadGiscus(container, theorem, initialValue);
  }

  window.FC.voting = {
    renderDifficultyVote,
    difficultyTerm,
  };
})();
