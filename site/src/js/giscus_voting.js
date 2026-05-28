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
    fetch('/assets/css/giscus-custom.css')
      .then(function(r) { return r.text(); })
      .then(function(customCss) {
        window.addEventListener('message', function onFirstGiscusMessage(event) {
          if (typeof event.data !== 'object' || !event.data.giscus || !event.data.giscus.resizeHeight) return;
          window.removeEventListener('message', onFirstGiscusMessage);
          var iframe = document.querySelector('iframe.giscus-frame');
          if (!iframe) return;
          var giscusOrigin = new URL(iframe.src).origin;
          var css = '@import url("' + giscusOrigin + '/themes/light.css");' + customCss;
          iframe.contentWindow.postMessage(
            { giscus: { setConfig: { theme: 'data:text/css,' + encodeURIComponent(css) } } },
            '*'
          );
        });
      });
  }

  applyGiscusTheme();
})();
