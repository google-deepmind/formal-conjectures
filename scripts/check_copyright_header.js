/*
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

const fs = require('fs');

// A close enough shim for RegExp.escape, new in node 24.
function regexEscape(s) {
  return s.replace(/\./g, '\\.')
      .replace(/\(/g, '\\(')
      .replace(/\)/g, '\\)')
      .replace(/\n/g, '\\n')
      .replace(/ /g, '\\x20');
}

module.exports = async ({github, context, core, glob}) => {
  const headerRe = new RegExp(
      `^` + regexEscape(`/-
Copyright `) +
          String.raw`(\d+) (.*)` + regexEscape(`

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/`),
      'd');


  function toLineCol(s, pos) {
    const prefix = s.substring(0, pos);
    const lines = prefix.split('\n');
    const line = lines.length;
    const col = lines[lines.length - 1].length + 1;
    return {line, col};
  }

  function checkCopyright(s, file) {
    if (!s.startsWith('/-')) {
      core.error('There must be a copyright header on the first line', {
        title: 'No Copyright Header',
        file: file,
        startLine: 1,
        startColumn: 1
      });
      return false;
    }
    let match = headerRe.exec(s);
    if (!match) {
      core.error('Could not find an Apache 2 copyright header', {
        title: 'No Copyright Header',
        file: file,
        startLine: 1,
        startColumn: 1,
        endLine: 6,
      });
      return false;
    }
    let year = match[1];
    let owner = match[2];
    if (!/^2[0-9]{3}$/.test(year)) {
      let [ys, ye] = match.indices[1];
      let ysp = toLineCol(s, ys);
      let yep = toLineCol(s, ye);
      core.error(`Copyright year of "${year}" is wrong`, {
        title: 'Bad copyright year',
        file: file,
        startLine: ysp.line,
        startColumn: ysp.col,
        endLine: yep.line,
        endColumn: yep.col,
      });
      return false;
    }
    if (owner != `The Formal Conjectures Authors.`) {
      let [os, oe] = match.indices[2];
      let osp = toLineCol(s, os);
      let oep = toLineCol(s, oe);
      core.error(
          `The owner should be exactly "The Formal Conjectures Authors.".\nPlease add yourself to AUTHORS instead.`,
          {
            title: 'Bad copyright owner',
            file: file,
            startLine: osp.line,
            startColumn: osp.col,
            endLine: oep.line,
            endColumn: oep.col,
          });
      return false;
    }
    return true;
  }


  console.log('🔍 Checking for copyright headers in .lean files...');
  const globber = await glob.create('**/*.lean', {followSymbolicLinks: false});
  const files = await globber.glob();

  let errorFound = false;
  for (const file of files) {
    const content = fs.readFileSync(file, 'utf8');
    if (!checkCopyright(content, file)) {
      errorFound = true;
    }
  }

  console.log('--------------------------------------------------');

  if (files.length === 0) {
    core.setFailed('🔴 Error: No .lean files were found to check.');
    return;
  }

  if (errorFound) {
    core.setFailed('🔴 Some files are missing their copyright headers.');
    return;
  }

  console.log(
      `✅ All ${files.length} files checked have a valid copyright header.`);
};
