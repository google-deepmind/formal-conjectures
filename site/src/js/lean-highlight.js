'use strict';

(() => {
let leanHighlighter;

/** Color source text with highlight.js without replacing Verso's links or hover targets. */
async function highlightLean(container) {
  try {
    leanHighlighter ||= Promise.all([
      import('https://esm.sh/highlight.js@11.12.0/lib/core'),
      import('https://esm.sh/highlightjs-lean@1.2.0'),
    ]).then(([{ default: hljs }, { default: lean }]) => {
      hljs.registerLanguage('lean', api => {
        const grammar = lean(api);
        // Lean permits arbitrarily nested block comments.
        const blockComment = { begin: /\/-/, end: /-\//, contains: ['self'] };
        for (const mode of grammar.contains) {
          if (mode.begin === '/-[^-]' || mode.begin === '/-[-!]') {
            mode.contains = [blockComment];
          }
        }
        return grammar;
      });
      return hljs;
    });
    const highlighter = await leanHighlighter;
    for (const code of container.querySelectorAll('code.hl.lean.block')) {
      const walker = document.createTreeWalker(code, NodeFilter.SHOW_TEXT, {
        acceptNode: node => node.parentElement.closest('.hover-info, .tactic-state')
          ? NodeFilter.FILTER_REJECT : NodeFilter.FILTER_ACCEPT,
      });
      const nodes = [];
      while (walker.nextNode()) nodes.push(walker.currentNode);
      // Verso includes the spacing between declarations inside the next block.
      // The surrounding box already provides that spacing.
      let leading = nodes.map(node => node.textContent).join('')
        .match(/^(?:[ \t]*\r?\n)+/)?.[0].length || 0;
      for (const node of nodes) {
        if (!leading) break;
        const count = Math.min(leading, node.textContent.length);
        node.textContent = node.textContent.slice(count);
        leading -= count;
      }
      const source = nodes.map(node => node.textContent).join('');
      const highlighted = document.createElement('template');
      highlighted.innerHTML = highlighter.highlight(source, { language: 'lean' }).value;
      const tokenWalker = document.createTreeWalker(highlighted.content, NodeFilter.SHOW_TEXT);
      const spans = [];
      let tokenOffset = 0;
      while (tokenWalker.nextNode()) {
        const node = tokenWalker.currentNode;
        const classes = [];
        for (let parent = node.parentElement; parent; parent = parent.parentElement) {
          classes.push(...parent.classList);
        }
        spans.push({ offset: tokenOffset, content: node.textContent, classes });
        tokenOffset += node.textContent.length;
      }
      let offset = 0;
      let index = 0;
      for (const node of nodes) {
        const end = offset + node.textContent.length;
        const fragment = document.createDocumentFragment();
        while (offset < end) {
          while (index < spans.length && spans[index].offset + spans[index].content.length <= offset) index++;
          const token = spans[index];
          const colored = token && token.offset <= offset;
          const stop = Math.min(end, colored ? token.offset + token.content.length : token?.offset ?? end);
          const text = source.slice(offset, stop);
          if (colored) {
            const span = document.createElement('span');
            span.textContent = text;
            span.className = ['lean-highlight', ...token.classes].join(' ');
            fragment.appendChild(span);
          } else {
            // Preserve any whitespace between highlighted tokens.
            fragment.appendChild(document.createTextNode(text));
          }
          offset = stop;
        }
        node.replaceWith(fragment);
      }
    }
  } catch (error) {
    // Leave the original code readable when the CDN is unavailable.
    console.warn('Lean syntax highlighting unavailable:', error);
  }
}

window.FCLean = { highlight: highlightLean };
document.addEventListener('DOMContentLoaded', () => {
  const source = document.querySelector('.code-content');
  if (source) highlightLean(source);
});
})();
