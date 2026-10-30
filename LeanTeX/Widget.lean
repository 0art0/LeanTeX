import LeanTeX.Basic
import ProofWidgets.Component.HtmlDisplay
import Lean.Server.GoTo

/-! # Widgets for displaying LaTeX

The `#texify` command and the `texify` tactic display expressions and goals in LaTeX form
in the infoview. The display is interactive: hovering over a subexpression shows its type and
docstring, and shift-clicking selects subexpressions. This uses the subexpression tracking of
`LeanTeX.run_latexPPTagged`, and the client side is the `LatexDisplay` component, whose source
is in `widget/src/latexDisplay.tsx`.
-/

namespace LeanTeX

open Lean Elab Tactic ProofWidgets ProofWidgets.Jsx

/-- Displays the markdown source in `md` in a widget when the cursor is placed at `stx`. -/
def displayMarkdown (md : String) (stx : Syntax) : CoreM Unit := do
  let html : Html := <MarkdownDisplay contents={md}/>
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
    stx

/-- A part of a line in a `LatexDisplay`. -/
structure LatexPart where
  /-- The LaTeX source, where tags give the subexpressions that parts of it come from.
  The leaves are LaTeX fragments, and they are concatenated to form the LaTeX source. -/
  latex : Widget.CodeWithInfos
  /-- What the part shows, which determines the goal locations of selected subexpressions:
  * `"text"`: nothing (for example a separator).
  * `"expr"`: an expression that is not part of a goal.
  * `"hyp"`, `"hypType"`, `"hypValue"`: the name, type or value of the hypothesis `fvarId`.
  * `"target"`: the target of the goal. -/
  kind : String := "text"
  /-- For hypothesis parts, the hypothesis. -/
  fvarId : Option FVarId := none
  /-- For hypothesis parts, the name of the hypothesis, for display purposes. -/
  name : Option String := none
  deriving Server.RpcEncodable

/-- Props for `LatexDisplay`. -/
structure LatexDisplay.Props where
  /-- The lines to display. Each line is displayed as a single LaTeX formula. -/
  lines : Array (Array LatexPart)
  /-- The goal being displayed, if any. -/
  mvarId : Option MVarId := none
  deriving Server.RpcEncodable

/-- Displays lines of LaTeX with interactive subexpressions: hovering over one shows its type and
docstring, and shift-clicking selects it. Selection is local to the widget. -/
@[widget_module]
def LatexDisplay : Component LatexDisplay.Props where
  javascript := include_str ".." / "widget" / "dist" / "latexDisplay.js"

/-- The declaration of the constant `c`, for go-to-definition. -/
def declLocation? (c : Name) : MetaM (Option DeclarationLocation) := do
  let some ranges ← findDeclarationRanges? c | return none
  let env ← getEnv
  let module := match env.getModuleIdxFor? c with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  return some { module, range := ranges.selectionRange }

/-- The infoview information for a tagged subexpression.

For applications of constants, the hover shows the constant's docstring. Go-to-definition works
as for applications in the goal view: for applications of type class projections such as `a + b`
it lists the instances, and otherwise it goes to the constant. Since LaTeX notation often does not
show the function separately (for example `\sqrt{x}`), the latter is done here: the server only
does it for `Info.ofTermInfo`. -/
def SubexprTag.toInfo (t : SubexprTag) : MetaM Elab.Info :=
  Meta.withLCtx t.lctx {} do
    let mut doc? := none
    let mut location? := none
    if let some c := t.expr.getAppFn.constName? then
      if t.expr.isApp then
        doc? ← findDocString? (← getEnv) c
        let isProj ← try pure (← Server.getInstanceProjectionArg? t.expr).isSome catch _ => pure false
        unless isProj do
          location? ← declLocation? c
    return .ofDelabTermInfo {
      elaborator := .anonymous
      stx := .missing
      lctx := t.lctx
      expectedType? := none
      expr := t.expr
      location?
      mkDocString? := doc?.map fun doc _ => pure doc
      explicit := false }

/-- Replace the tags (indices into `tags` and `infos`) in the output of `parseTaggedLatex`
by `SubexprInfo`s. -/
partial def tagLatexInfos (ctx : ContextInfo) (tags : Array SubexprTag) (infos : Array Elab.Info)
    (tt : Widget.TaggedText Nat) : BaseIO Widget.CodeWithInfos :=
  tt.rewriteM fun t sub => do
    match tags[t]?, infos[t]? with
    | some tag, some info =>
      let i : Widget.SubexprInfo := {
        info := ← Server.WithRpcRef.mk { ctx, info, children := .empty }
        subexprPos := tag.pos }
      return .tag i (← tagLatexInfos ctx tags infos sub)
    | _, _ => tagLatexInfos ctx tags infos sub

/-- Run the LaTeX pretty printer on `e`, returning the LaTeX with tagged subexpressions.
Removing the tags gives the same LaTeX as `run_latexPP`. -/
def latexWithInfos (e : Expr) (config : Config := {}) : MetaM Widget.CodeWithInfos := do
  let (latex, tags) ← run_latexPPTagged e config
  let ctx : ContextInfo := {
    env           := (← getEnv)
    mctx          := (← getMCtx)
    options       := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls     := (← getOpenDecls)
    fileMap       := default
    ngen          := (← getNGen)
  }
  let infos ← tags.mapM (·.toInfo)
  tagLatexInfos ctx tags infos (parseTaggedLatex latex)

/-- Displays `props` with `LatexDisplay` when the cursor is placed at `stx`. -/
def displayLatex (props : LatexDisplay.Props) (stx : Syntax) : CoreM Unit := do
  let html : Html := .ofComponent LatexDisplay props #[]
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← Server.RpcEncodable.rpcEncode html) })
    stx

/--
Command for displaying an expression in LaTeX form.
-/
elab tk:"#texify " e:term : command => do
  Elab.Command.runTermElabM fun _ => do
    let e ← Elab.Term.elabTerm e none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let latex ← latexWithInfos e
    displayLatex { lines := #[#[{ latex, kind := "expr" }]] } tk

/--
Tactic for displaying the goal in LaTeX form.
-/
elab tk:"texify" : tactic => withMainContext do
  let mvarId ← getMainGoal
  let text (s : String) : LatexPart := { latex := .text s }
  let mut lines : Array (Array LatexPart) := #[]
  -- State for variable merging.
  -- Example, to write `x, y : ℝ` rather than `x : ℝ` and `y : ℝ` independently.
  -- We record the names so far and the type, along with its LaTeX without tags for comparison.
  let mut currCDecl? : Option (Array LatexPart × String × LatexPart) := none
  let flush (lines : Array (Array LatexPart)) (currCDecl? : Option (Array LatexPart × String × LatexPart)) :
      Array (Array LatexPart) × Option (Array LatexPart × String × LatexPart) :=
    if let some (vars, _, type) := currCDecl? then
      (lines.push (vars.toList.intersperse (text ", ") ++ [text " : ", type]).toArray, none)
    else
      (lines, none)
  for decl in (← getLCtx) do
    unless decl.isImplementationDetail do
      let hyp (kind : String) (latex : Widget.CodeWithInfos) : LatexPart :=
        { latex, kind, fvarId := decl.fvarId, name := decl.userName.toString }
      let var := hyp "hyp" (← latexWithInfos decl.toExpr)
      let typeLatex ← latexWithInfos (← instantiateMVars decl.type)
      if let some value := decl.value? then
        (lines, currCDecl?) := flush lines currCDecl?
        let val ← latexWithInfos (← instantiateMVars value)
        lines := lines.push #[var, text " : ", hyp "hypType" typeLatex, text " := ", hyp "hypValue" val]
      else
        let type := typeLatex.stripTags
        if let some (vars, type', typePart) := currCDecl? then
          if type == type' then
            currCDecl? := some (vars.push var, type', typePart)
            continue
        (lines, currCDecl?) := flush lines currCDecl?
        currCDecl? := some (#[var], type, hyp "hypType" typeLatex)
  (lines, _) := flush lines currCDecl?
  let goal ← latexWithInfos (← instantiateMVars (← getMainTarget)).consumeMData
  lines := lines.push #[text "\\vdash ", { latex := goal, kind := "target" }]
  displayLatex { lines, mvarId := some mvarId } tk
