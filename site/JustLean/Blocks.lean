import VersoManual
import Lean

/-! Two small extensions of the Verso manual genre used by this tutorial: `{rawHtml}` embeds a
fragment of HTML, and `{tweet}` embeds the post that prompted the tutorial. -/

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
