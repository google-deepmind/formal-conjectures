/**
 * giscus_voting.js — giscus-backed voting system.
 *
 * Votes are stored as reactions (emojis) on the theorem page.
 */

'use strict';

(function () {

  // ---------------------------------------------------------------------------
  // Apply giscus theme (filter emojis + reaction labels)
  // ---------------------------------------------------------------------------
  function applyGiscusTheme() {
    var base = document.documentElement.dataset.base || '';
    fetch(base + '/assets/css/giscus-custom.css')
      .then(function(r) { if (!r.ok) return Promise.reject(); return r.text(); })
      .then(function(customCss) {
        function sendTheme(iframe) {
          var giscusOrigin = new URL(iframe.src).origin;
          var css = '@import url("' + giscusOrigin + '/themes/light.css");' + customCss;
          iframe.contentWindow.postMessage(
            { giscus: { setConfig: { theme: 'data:text/css,' + encodeURIComponent(css) } } },
            '*'
          );
        }

        function waitAndApply() {
          window.addEventListener('message', function onReady(event) {
            if (typeof event.data !== 'object' || !event.data.giscus || !event.data.giscus.resizeHeight) return;
            window.removeEventListener('message', onReady);
            var iframe = document.querySelector('iframe.giscus-frame');
            if (!iframe) return;
            sendTheme(iframe);
            // Re-apply if the iframe reloads (e.g. after sign-out)
            iframe.addEventListener('load', waitAndApply, { once: true });
          });
        }

        waitAndApply();
      });
  }

  applyGiscusTheme();
})();
