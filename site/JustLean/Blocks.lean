import VersoManual
import Lean

/-! Two small extensions of the Verso manual genre used by this tutorial:
`{src Some.declaration}` shows the source text of a declaration of the library, taken from the file on
disk at build time (with a link to the same lines on GitHub), and `{rawHtml}` embeds a fragment of HTML. -/

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual Html
open Verso.Doc.Html (HtmlT)
open Verso.Output (Html)

namespace JustLean

block_extension Block.rawHtml (html : String) where
  data := Json.str html
  traverse _ _ _ := pure none
  toHtml := some <| fun _ _ _ data _ => do
    let .str s := data
      | Verso.reportError "Expected string JSON for rawHtml" *> pure .empty
    pure (.text false s)
  toTeX := some <| fun _ _ _ _ _ => pure .empty

/-- The repository the source links point at. -/
def repoUrl : String := "https://github.com/zksecurity/just-lean/blob/main/"

structure SrcConfig where
  decl : Name

meta instance : FromArgs SrcConfig DocElabM :=
  ⟨SrcConfig.mk <$> .positional `decl .name⟩

/-- The path of a module of the library, relative to the repository root. -/
def modulePath (mod : Name) : System.FilePath :=
  let rel := System.mkFilePath (mod.components.map toString) |>.addExtension "lean"
  if mod.getRoot == `Drift then ("lab" : System.FilePath) / rel else rel

/-- Escape text for HTML. -/
def escapeHtml (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"

def leanKeywords : List String :=
  ["def", "theorem", "lemma", "structure", "inductive", "class", "instance", "abbrev", "where",
   "namespace", "end", "open", "import", "section", "variable", "attribute", "deriving", "extends",
   "if", "then", "else", "let", "have", "show", "match", "with", "fun", "do", "return", "for", "in",
   "termination_by", "decreasing_by", "by", "at", "using", "from", "calc", "mut", "unless",
   "induction", "simp", "simpa", "omega", "exact", "rw", "rfl", "intro", "intros", "refine", "rcases",
   "obtain", "cases", "apply", "split", "constructor", "decide", "exists", "use", "all_goals",
   "try", "first", "subst", "unfold", "dsimp", "generalize", "specialize", "exfalso", "contradiction",
   "absurd", "trivial", "assumption", "left", "right", "ext", "funext", "congr", "norm_num", "ring",
   "private", "protected", "partial", "noncomputable", "unsafe", "macro_rules", "syntax", "macro",
   "tactic", "Type", "Prop", "Sort"]

/-- A lexical highlighter for Lean source excerpts: comments, doc comments, strings, numbers,
    keywords, attributes. Everything else is left as is. -/
partial def highlightLean (src : String) : String :=
  go src.toList "" 
where
  span (cls : String) (txt : String) : String := s!"<span class=\"{cls}\">{escapeHtml txt}</span>"
  isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '.' || c == '!' || c == '?' || c == '\'' || c == '#' || c.toNat > 127
  takeWhile (p : Char → Bool) : List Char → List Char × List Char
    | [] => ([], [])
    | c :: cs => if p c then let (a, b) := takeWhile p cs; (c :: a, b) else ([], c :: cs)
  blockComment : List Char → Nat → List Char × List Char
    | [], _ => ([], [])
    | '-' :: '/' :: cs, 1 => (['-', '/'], cs)
    | '-' :: '/' :: cs, d + 1 => let (a, b) := blockComment cs d; ('-' :: '/' :: a, b)
    | '/' :: '-' :: cs, d => let (a, b) := blockComment cs (d + 1); ('/' :: '-' :: a, b)
    | c :: cs, d => let (a, b) := blockComment cs d; (c :: a, b)
  go : List Char → String → String
    | [], acc => acc
    | '/' :: '-' :: cs, acc =>
      let (a, b) := blockComment cs 1
      let txt := String.ofList ('/' :: '-' :: a)
      go b (acc ++ span (if txt.startsWith "/--" || txt.startsWith "/-!" then "src-doc" else "src-comment") txt)
    | '-' :: '-' :: cs, acc =>
      let (a, b) := takeWhile (· != '\n') cs
      go b (acc ++ span "src-comment" (String.ofList ('-' :: '-' :: a)))
    | '"' :: cs, acc =>
      let (a, b) := takeWhile (· != '"') cs
      let b := b.drop 1
      go b (acc ++ span "src-string" (String.ofList ('"' :: a ++ ['"'])))
    | '@' :: '[' :: cs, acc =>
      let (a, b) := takeWhile (· != ']') cs
      let b := b.drop 1
      go b (acc ++ span "src-attr" (String.ofList ('@' :: '[' :: a ++ [']'])))
    | c :: cs, acc =>
      if c.isDigit then
        let (a, b) := takeWhile (fun d => d.isAlphanum || d == '.') (c :: cs)
        go b (acc ++ span "src-num" (String.ofList a))
      else if isIdChar c then
        let (a, b) := takeWhile isIdChar (c :: cs)
        let w := String.ofList a
        go b (acc ++ (if leanKeywords.contains w then span "src-kw" w else escapeHtml w))
      else go cs (acc ++ escapeHtml (String.singleton c))

/-- `{src Name}`: the source text of the declaration `Name`, as written in the library. -/
@[block_command]
meta def src : BlockCommandOf SrcConfig
  | ⟨decl⟩ => do
    let env ← getEnv
    let some ranges ← findDeclarationRanges? decl
      | throwError "No source range known for '{decl}'"
    let some modIdx := env.getModuleIdxFor? decl
      | throwError "'{decl}' is not from an imported module"
    let modName := env.header.moduleNames[modIdx.toNat]!
    let rel := modulePath modName
    let contents ← IO.FS.readFile ((".." : System.FilePath) / rel)
    let lines := contents.splitOn "\n"
    let first := ranges.range.pos.line
    let last := ranges.range.endPos.line
    let text := String.intercalate "\n" (lines.drop (first - 1) |>.take (last - first + 1))
    let url := s!"{repoUrl}{rel}#L{first}-L{last}"
    let html := s!"<pre class=\"src-code\"><code>{highlightLean text}</code></pre><p class=\"src-link\"><a href=\"{url}\">{rel}, lines {first}–{last}</a></p>"
    ``(Verso.Doc.Block.other (Block.rawHtml $(quote html)) #[])

structure RawArgs where
  html : String

meta instance : FromArgs RawArgs DocElabM :=
  ⟨RawArgs.mk <$> .positional `html .string⟩

/-- `{rawHtml "..."}`: a fragment of HTML, emitted as is. -/
@[block_command]
meta def rawHtml : BlockCommandOf RawArgs
  | ⟨html⟩ => ``(Verso.Doc.Block.other (Block.rawHtml $(quote html)) #[])

/-- The tweet that prompted this tutorial, as an embedded X post (the text is shown even without the
    embedding script). -/
def tweetHtml : String :=
  "<blockquote class=\"twitter-tweet\"><p lang=\"en\" dir=\"ltr\">Regarding doing stuff in \"just Lean,\" (which would be great IMO: less languages =&gt; less tooling/complexity =&gt; less headache), I could not really find any meaningful tutorials.<br><br>e.g., I'm thinking \"here's a sorting spec in Lean, a merge sort implemented in Lean that you can compile and run and a proof that it sorts according to the spec.\"</p>&mdash; alin.apt (@alinush) <a href=\"https://x.com/alinush/status/2097373587648725430\">September 8, 2026</a></blockquote><script async src=\"https://platform.twitter.com/widgets.js\" charset=\"utf-8\"></script>"

/-- `{tweet}`: the embedded post. -/
@[block_command]
meta def tweet : BlockCommandOf Unit
  | () => ``(Verso.Doc.Block.other (Block.rawHtml $(quote tweetHtml)) #[])

end JustLean
