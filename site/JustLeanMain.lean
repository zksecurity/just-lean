import VersoManual
import JustLean

open Verso.Genre Manual

def extraStyle : String := "<style>
:root {
  --verso-code-keyword-color: #7a2ea0;
  --verso-code-const-color: #1a5fb4;
  --verso-code-var-color: #1f2328;
}
.hl.lean .token.sort { color: #0a7b83; }
.hl.lean .token.literal { color: #b45f06; }
.hl.lean .token.doc-comment, .hl.lean .token.comment { color: #5f7a5f; font-style: italic; }
.hl.lean .token.keyword { font-weight: 600; }
pre.src-code, .hl.lean.block { overflow-x: auto; font-family: var(--verso-code-font-family); font-size: 0.9em;
  line-height: 1.4; background: #f7f7f8; padding: 0.6em 0.8em; border-radius: 4px; margin: 1em 0; }
.src-kw { color: #7a2ea0; font-weight: 600; }
.src-doc, .src-comment { color: #5f7a5f; font-style: italic; }
.src-string { color: #b45f06; }
.src-num { color: #b45f06; }
.src-attr { color: #1a5fb4; }
.src-link { text-align: right; font-size: 80%; margin-top: 0.2em; margin-bottom: 1.4em; }
.twitter-tweet { margin: 1em auto; }
</style>
<script>
document.addEventListener('DOMContentLoaded', function () {
  var table = document.querySelector('#toc .split-toc.book table');
  if (!table) return;
  var onIndex = !table.querySelector('tr.current');
  var row = document.createElement('tr');
  row.className = onIndex ? 'current' : '';
  row.innerHTML = '<td class=\"num\"></td><td><a href=\"\">Introduction</a></td>';
  table.insertBefore(row, table.firstChild);
});
</script>"

def main := manualMain (%doc JustLean) (config := {
  emitTeX := false, emitHtmlSingle := .no, emitHtmlMulti := .immediately,
  htmlDepth := 1,
  extraHead := #[.text false extraStyle],
  sourceLink := some "https://github.com/zksecurity/just-lean",
  issueLink := some "https://github.com/zksecurity/just-lean/issues" })
