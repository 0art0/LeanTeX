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

register_option leantex.colorVariables : Bool := {
  defValue := true
  descr := "(LeanTeX) color the free and bound variables in the interactive LaTeX display of \
    `#texify` and `texify`, giving each variable its own color"
}

register_option leantex.variableColors : String := {
  defValue := ""
  descr := "(LeanTeX) the colors for variables in the interactive LaTeX display, as a \
    comma-separated list of CSS colors such as \"#e06c75, #61afef, tomato\". Variables are \
    colored in order of appearance, cycling through the list. If empty, a palette that adapts to \
    the editor's color theme is used."
}

/-- The tag of a subexpression in the LaTeX of a `LatexDisplay`. -/
structure LatexTag where
  /-- The infoview information for the subexpression, for hovers and go-to-definition. -/
  info : Server.WithRpcRef Elab.InfoWithCtx
  /-- The position of the subexpression in the expression being displayed. -/
  subexprPos : SubExpr.Pos
  /-- Whether this tags the name of a variable where it is bound (see `SubexprTag.binder`). -/
  binder : Bool := false
  /-- If the subexpression is a free variable that is not a proof, the variable. The display
  colors these. -/
  fvarId : Option FVarId := none
  /-- Identifies the subexpression up to structural equality (ignoring metadata). On hover, the
  display highlights the other subexpressions with the same key. -/
  key : String
  deriving Server.RpcEncodable

/-- LaTeX whose leaves are LaTeX fragments, with tagged subexpressions. -/
abbrev LatexCode := Widget.TaggedText LatexTag

/-- A part of a line in a `LatexDisplay`. -/
structure LatexPart where
  /-- The LaTeX source, where tags give the subexpressions that parts of it come from.
  The leaves are LaTeX fragments, and they are concatenated to form the LaTeX source. -/
  latex : LatexCode
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
  /-- Whether to color variables (the option `leantex.colorVariables`). -/
  colorVariables : Bool := true
  /-- The colors for variables (the option `leantex.variableColors`); if empty, the default. -/
  variableColors : Array String := #[]
  deriving Server.RpcEncodable

/-- `LatexDisplay.Props` for `lines`, with the coloring options from `opts`. -/
def LatexDisplay.Props.ofLines (lines : Array (Array LatexPart)) (mvarId : Option MVarId := none)
    (opts : Options) : LatexDisplay.Props where
  lines
  mvarId
  colorVariables := leantex.colorVariables.get opts
  variableColors :=
    ((leantex.variableColors.get opts).splitOn ",").toArray.map (·.trimAscii.toString)
      |>.filter (!·.isEmpty)

/-- Displays lines of LaTeX with interactive subexpressions: hovering over one shows its type and
docstring (also in LaTeX), and shift-clicking selects it. Selection is local to the widget. -/
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

/-- `e` without metadata. -/
partial def eraseMData (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ b => some (eraseMData b)
    | _ => none

/-- The `LatexTag` for a tagged subexpression. -/
def SubexprTag.toLatexTag (ctx : ContextInfo) (t : SubexprTag) : MetaM LatexTag := do
  let info ← t.toInfo
  let fvarId ← Meta.withLCtx t.lctx {} do
    let .fvar fvarId := t.expr | return none
    let isProof ← try Meta.isProof t.expr catch _ => pure true
    return if isProof then none else some fvarId
  return {
    info := ← Server.WithRpcRef.mk { ctx, info, children := .empty }
    subexprPos := t.pos
    binder := t.binder
    fvarId
    key := toString (eraseMData t.expr).hash }

/-- Replace the tags (indices into `tags`) in the output of `parseTaggedLatex` by `LatexTag`s. -/
partial def tagLatexInfos (tags : Array LatexTag) (tt : Widget.TaggedText Nat) : LatexCode :=
  tt.rewrite fun t sub =>
    match tags[t]? with
    | some tag => .tag tag (tagLatexInfos tags sub)
    | none => tagLatexInfos tags sub

/-- Run the LaTeX pretty printer on `e`, returning the LaTeX with tagged subexpressions.
Removing the tags gives the same LaTeX as `run_latexPP`. -/
def latexWithInfos (e : Expr) (config : Config := {}) : MetaM LatexCode := do
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
  let tags ← tags.mapM (·.toLatexTag ctx)
  return tagLatexInfos tags (parseTaggedLatex latex)

/-- The contents of the hover for a subexpression in a `LatexDisplay`, like `Lean.Widget.InfoPopup`
but with the expression and its type in LaTeX. -/
structure LatexPopup where
  /-- The subexpression. -/
  expr : LatexCode
  /-- Its type, if it could be printed. -/
  type : Option LatexCode := none
  /-- The docstring, in Markdown. -/
  doc : Option String := none
  deriving Server.RpcEncodable

/-- The hover for the subexpression with the information `i`. Tags in the result make the hover
interactive too, so hovers can be nested. -/
def LatexPopup.ofInfo (i : Elab.InfoWithCtx) : IO LatexPopup :=
  i.ctx.runMetaM i.info.lctx do
    let e ← match i.info with
      | .ofTermInfo ti => pure ti.expr
      | .ofDelabTermInfo ti => pure ti.expr
      | _ => throwError "LeanTeX: no expression to display"
    let e ← instantiateMVars e
    let type ← try
        some <$> latexWithInfos (← instantiateMVars (← Meta.inferType e))
      catch _ => pure none
    return { expr := ← latexWithInfos e, type, doc := ← i.info.docString? }

/-- The hover for a subexpression in a `LatexDisplay` (see `LatexTag.info`). -/
@[server_rpc_method]
def LatexDisplay.popup (i : Server.WithRpcRef Elab.InfoWithCtx) :
    Server.RequestM (Server.RequestTask LatexPopup) :=
  Server.RequestM.pureTask do LatexPopup.ofInfo i.val

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
    displayLatex (.ofLines #[#[{ latex, kind := "expr" }]] (opts := ← getOptions)) tk

/-- The lines of a `LatexDisplay` for the goal `mvarId`: the hypotheses (merging consecutive
variables of the same type), then the target. -/
def goalLatexLines (mvarId : MVarId) : MetaM (Array (Array LatexPart)) := mvarId.withContext do
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
      let hyp (kind : String) (latex : LatexCode) : LatexPart :=
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
  let goal ← latexWithInfos (← instantiateMVars (← mvarId.getType)).consumeMData
  return lines.push #[text "\\vdash ", { latex := goal, kind := "target" }]

/--
Tactic for displaying the goal in LaTeX form.
-/
elab tk:"texify" : tactic => withMainContext do
  let mvarId ← getMainGoal
  displayLatex (.ofLines (← goalLatexLines mvarId) (some mvarId) (← getOptions)) tk
