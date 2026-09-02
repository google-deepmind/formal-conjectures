(function () {
  "use strict";

  const SOURCE_ROOT = ".code-content";
  const CODE_BLOCK = "code.hl.lean.block";
  const DOCSTRING = ".md-text:not(.mod-doc), .verso-text:not(.mod-doc)";

  function withoutCopyrightHeader(text) {
    const trimmed = text.trim();
    if (!/^\/-\s*Copyright\b/i.test(trimmed)) {
      return trimmed;
    }

    const end = trimmed.indexOf("-/");
    return end === -1 ? trimmed : trimmed.slice(end + 2).trim();
  }

  function isBoilerplate(block) {
    // Declaration anchors are emitted inside their code blocks. Never hide a
    // block that contains one, even if the declaration uses an `open ... in`
    // prefix or another command that otherwise looks structural.
    if (block.querySelector("[id]")) {
      return false;
    }

    const text = withoutCopyrightHeader(block.textContent || "");
    if (!text) {
      return true;
    }

    const lines = text
      .split("\n")
      .map(function (line) { return line.trim(); })
      .filter(Boolean);

    return lines.length > 0 && lines.every(function (line) {
      return /^(?:prelude|import|open(?:\s+scoped)?|namespace|section|end)\b/.test(line) ||
        /^noncomputable\s+section\b/.test(line);
    });
  }

  function declarationKind(block) {
    const match = (block.textContent || "").match(
      /\b(theorem|lemma|proposition|corollary|def|abbrev|opaque|structure|class|instance|inductive|axiom)\b/
    );
    if (!match) {
      return { label: "declaration", theme: "def" };
    }

    const label = match[1];
    if (["theorem", "lemma", "proposition", "corollary", "axiom"].includes(label)) {
      return { label: label, theme: "theorem" };
    }
    if (["structure", "inductive"].includes(label)) {
      return { label: label, theme: "structure" };
    }
    if (label === "class") {
      return { label: label, theme: "class" };
    }
    return { label: label, theme: "def" };
  }

  function groupDocstring(docstring) {
    let declaration = docstring.nextElementSibling;
    while (declaration && declaration.classList.contains("fc-source-boilerplate")) {
      declaration = declaration.nextElementSibling;
    }

    if (!declaration || !declaration.matches(CODE_BLOCK)) {
      return;
    }

    const kind = declarationKind(declaration);
    const box = document.createElement("div");
    box.className = "fc-declaration-doc fc-declaration-doc--" + kind.theme;

    const label = document.createElement("span");
    label.className = "fc-declaration-label";
    label.setAttribute("aria-hidden", "true");
    label.textContent = kind.label;

    docstring.parentNode.insertBefore(box, docstring);
    box.appendChild(label);
    box.appendChild(declaration);
    box.appendChild(docstring);

    declaration.classList.add("fc-declaration-code");
    docstring.classList.add("fc-declaration-text");
  }

  function improveSourcePage() {
    document.querySelectorAll(SOURCE_ROOT).forEach(function (source) {
      source.querySelectorAll(".md-text.mod-doc, .verso-text.mod-doc").forEach(function (doc) {
        doc.classList.add("fc-module-doc");
      });

      source.querySelectorAll(CODE_BLOCK).forEach(function (block) {
        if (isBoilerplate(block)) {
          block.classList.add("fc-source-boilerplate");
        }
      });

      // Take a snapshot because grouping moves both nodes into a new wrapper.
      Array.from(source.querySelectorAll(DOCSTRING)).forEach(groupDocstring);
    });
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", improveSourcePage);
  } else {
    improveSourcePage();
  }
})();
