import VersoManual
import JustLean

open Verso.Genre Manual

def extraStyle : String := "<style>
.src-link { text-align: right; font-size: 80%; margin-top: -0.6em; margin-bottom: 1.4em; }
.twitter-tweet { margin: 1em auto; }
</style>"

def main := manualMain (%doc JustLean) (config := {
  emitTeX := false, emitHtmlSingle := .no, emitHtmlMulti := .immediately,
  htmlDepth := 1,
  extraHead := #[.text false extraStyle],
  sourceLink := some "https://github.com/zksecurity/just-lean",
  issueLink := some "https://github.com/zksecurity/just-lean/issues" })
