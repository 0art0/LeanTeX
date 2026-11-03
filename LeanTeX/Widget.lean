import LeanTeX.Basic
import ProofWidgets.Component.HtmlDisplay
import Lean.Server.GoTo
import Lean.Widget.Diff

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
  display highlights the other subexpressions with the same key, also in other formulas. -/
  key : String
  /-- If the subexpression should be folded (shown as `⋯`) initially, why. As in the usual pretty
  printer, this follows the options `pp.proofs` and `pp.deepTerms`. See `omissionReason?`. -/
  omitted : Option String := none
  /-- How the subexpression changed in the last tactic, for goals (see `LatexDisplay.diff`). -/
  diff : Option Widget.DiffTag := none
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

/-- Why the subexpression `e`, nested `depth` tags deep in the LaTeX, should be folded initially,
if it should. Like `Lean.PrettyPrinter.Delaborator.shouldOmitProof` and `shouldOmitExpr`, this
folds proofs unless `pp.proofs` is set, and deep terms unless `pp.deepTerms` is set, except for
shallow expressions. The depth of the LaTeX stands in for the delaborator's depth.
The expression being displayed (at depth 0) is never folded. -/
def omissionReason? (opts : Options) (e : Expr) (isProof : Bool) (depth : Nat) : Option String :=
  open PrettyPrinter.Delaborator in
  if depth == 0 || e.isAtomic then
    none
  else if isProof && !getPPProofs opts && !isShallowExpression (getPPProofsThreshold opts) e then
    some "Proof folded (see option `pp.proofs`)."
  else
    let threshold := getPPDeepTermsThreshold opts
    let excess := depth - threshold
    if !getPPDeepTerms opts && excess > 0 && !isShallowExpression (threshold / 4 - excess) e then
      some "Term folded due to its depth (see option `pp.deepTerms`)."
    else
      none

/-- The `LatexTag` for a tagged subexpression, which is nested `depth` tags deep. -/
def SubexprTag.toLatexTag (ctx : ContextInfo) (t : SubexprTag) (depth : Nat) : MetaM LatexTag := do
  let info ← t.toInfo
  let isProof ← Meta.withLCtx t.lctx {} do
    try Meta.isProof t.expr catch _ => pure false
  let opts ← getOptions
  return {
    info := ← Server.WithRpcRef.mk { ctx, info, children := .empty }
    subexprPos := t.pos
    binder := t.binder
    fvarId := if let .fvar fvarId := t.expr then if isProof then none else some fvarId else none
    key := toString (eraseMData t.expr).hash
    omitted := if t.binder then none else omissionReason? opts t.expr isProof depth }

/-- The least depth at which each tag (an index below `n`) occurs in `tt`. -/
partial def tagDepths (n : Nat) (tt : Widget.TaggedText Nat) : Array Nat :=
  go tt 0 (.replicate n 0) (.replicate n false) |>.1
where
  go (tt : Widget.TaggedText Nat) (depth : Nat) (ds : Array Nat) (seen : Array Bool) :
      Array Nat × Array Bool :=
    match tt with
    | .text _ => (ds, seen)
    | .append as => as.foldl (fun (ds, seen) a => go a depth ds seen) (ds, seen)
    | .tag t a =>
      let (ds, seen) :=
        if seen[t]?.getD true then (ds, seen) else (ds.set! t depth, seen.set! t true)
      go a (depth + 1) ds seen

/-- Replace the tags (indices into `tags`) in the output of `parseTaggedLatex` by `LatexTag`s. -/
partial def tagLatexInfos (tags : Array LatexTag) (tt : Widget.TaggedText Nat) : LatexCode :=
  tt.rewrite fun t sub =>
    match tags[t]? with
    | some tag => .tag tag (tagLatexInfos tags sub)
    | none => tagLatexInfos tags sub

/-- Applies `f` to the tags of `code`. -/
partial def LatexCode.mapTags (f : LatexTag → LatexTag) : LatexCode → LatexCode
  | .text s => .text s
  | .append as => .append (as.map (mapTags f))
  | .tag t a => .tag (f t) (mapTags f a)

/-- Folds `f` over the tags of `code`. -/
partial def LatexCode.foldTags (f : α → LatexTag → α) (init : α) : LatexCode → α
  | .text _ => init
  | .append as => as.foldl (fun acc a => foldTags f acc a) init
  | .tag t a => foldTags f (f init t) a

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
  let tt := parseTaggedLatex latex
  let depths := tagDepths tags.size tt
  let tags ← tags.mapIdxM fun i t => t.toLatexTag ctx depths[i]!
  return tagLatexInfos tags tt

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
elab (name := texifyTac) tk:"texify" : tactic => withMainContext do
  let mvarId ← getMainGoal
  displayLatex (.ofLines (← goalLatexLines mvarId) (some mvarId) (← getOptions)) tk

/-! ## Goal diffs

Like the goal view, the display of `texify` shows how the goal changed in the last tactic.
Since the info trees of earlier tactics are not available while `texify` runs, the client asks for
the diff with the RPC method `LatexDisplay.diff`, which runs once the proof has been elaborated:
it finds `texify` in the info tree and the last tactic before it that changed the goals, and
takes the changes that the goal view shows (`Lean.Widget.diffInteractiveGoals`). -/

/-- The changes marked in `code`, a goal's hypothesis type or target from
`Lean.Widget.diffInteractiveGoals`, at positions in the expression that `code` shows. -/
partial def diffPositions (code : Widget.CodeWithInfos) : Array (SubExpr.Pos × Widget.DiffTag) :=
  go code #[]
where
  go (code : Widget.CodeWithInfos) (acc : Array (SubExpr.Pos × Widget.DiffTag)) :
      Array (SubExpr.Pos × Widget.DiffTag) :=
    match code with
    | .text _ => acc
    | .append as => as.foldl (fun acc a => go a acc) acc
    | .tag info a =>
      go a (if let some d := info.diffStatus? then acc.push (info.subexprPos, d) else acc)

/-- Marks the tags of `code` with `changes`, which are at positions in the expression that `code`
shows. A change at a position without a tag is shown on its nearest tagged ancestor. -/
def LatexCode.withDiff (changes : Array (SubExpr.Pos × Widget.DiffTag)) (code : LatexCode) :
    LatexCode := Id.run do
  if changes.isEmpty then return code
  let tagged : Std.HashSet Nat :=
    code.foldTags (fun s t => if t.binder then s else s.insert t.subexprPos.asNat) {}
  let mut marks : Std.HashMap Nat Widget.DiffTag := {}
  for (p, d) in changes do
    let ps := p.toArray
    let ancestor? := (List.range (ps.size + 1)).reverse.find? fun k =>
      tagged.contains (SubExpr.Pos.ofArray (ps.extract 0 k)).asNat
    if let some k := ancestor? then
      marks := marks.insert (SubExpr.Pos.ofArray (ps.extract 0 k)).asNat d
  return code.mapTags fun t =>
    if t.binder then t else
      match marks[t.subexprPos.asNat]? with
      | some d => { t with diff := some d }
      | none => t

/-- Marks the tags at the root of `code` with `d`, for hypotheses that were added or removed. -/
def LatexCode.withRootDiff (d : Widget.DiffTag) (code : LatexCode) : LatexCode :=
  code.mapTags fun t => if !t.binder && t.subexprPos == .root then { t with diff := some d } else t

/-- How the hypotheses of a goal changed: for each changed hypothesis, either the changes in its
type, or `none` if it was added (or, before the tactic, if it will be removed). -/
abbrev HypDiffs := Std.HashMap FVarId (Option (Array (SubExpr.Pos × Widget.DiffTag)))

/-- Marks the changes in lines for a goal made by `goalLatexLines`, taking them from the same
goal decorated by `Lean.Widget.diffInteractiveGoals`. -/
def diffLines (useAfter : Bool) (ig : Widget.InteractiveGoal) (lines : Array (Array LatexPart)) :
    Array (Array LatexPart) := Id.run do
  let mut hyps : HypDiffs := {}
  for h in ig.hyps do
    let whole := if useAfter then h.isInserted? == some true else h.isRemoved? == some true
    let changes := diffPositions h.type
    for fvarId in h.fvarIds do
      if whole then hyps := hyps.insert fvarId none
      else if !changes.isEmpty then hyps := hyps.insert fvarId (some changes)
  let target := diffPositions ig.type
  let wholeTag : Widget.DiffTag := if useAfter then .wasInserted else .willDelete
  return lines.map (·.map fun part =>
    match part.kind, part.fvarId.bind (hyps[·]?) with
    | "target", _ => { part with latex := part.latex.withDiff target }
    | "hypType", some (some δ) => { part with latex := part.latex.withDiff δ }
    | "hyp", some none | "hypType", some none | "hypValue", some none =>
      { part with latex := part.latex.withRootDiff wholeTag }
    | _, _ => part)

/-- The goal before and after the last tactic, with their changes marked. -/
structure LatexDiff where
  /-- The goal before the tactic, marking what the tactic changes. -/
  before : Array (Array LatexPart)
  /-- The goal after the tactic (the goal shown by `texify`), marking what the tactic changed. -/
  after : Array (Array LatexPart)
  /-- The tactic, as written. -/
  tactic : String
  deriving Server.RpcEncodable

/-- The diff for the goal `g₁` after the tactic `prev`, if `prev` changed it. The changes are those
that the goal view shows (`Lean.Widget.diffInteractiveGoals`). -/
def goalDiff (ci : ContextInfo) (prev : TacticInfo) (g₁ : MVarId) : IO (Option LatexDiff) :=
  { ci with mctx := prev.mctxAfter }.runMetaM {} do
    if prev.goalsBefore.contains g₁ || !prev.goalsAfter.contains g₁ then return none
    let after ← Widget.diffInteractiveGoals true prev { goals := #[← Widget.goalToInteractive g₁] }
    -- `isInserted? = some false` means that the goal was compared with a goal before the tactic.
    let some (ig₁ : Widget.InteractiveGoal) := after.goals[0]? | return none
    unless ig₁.isInserted? == some false do return none
    let some g₀ ← prev.goalsBefore.findM? fun g₀ => return (← Meta.getMVars (.mvar g₀)).contains g₁
      | return none
    let before ← Widget.diffInteractiveGoals false prev { goals := #[← Widget.goalToInteractive g₀] }
    let some (ig₀ : Widget.InteractiveGoal) := before.goals[0]? | return none
    return some {
      before := diffLines false ig₀ (← goalLatexLines g₀)
      after := diffLines true ig₁ (← goalLatexLines g₁)
      tactic := (prev.stx.reprint.getD (toString prev.stx.prettyPrint)).trimAscii.toString }

/-- Finds `texify` for the goal `mvarId` in `t`, and the last tactic before it that changed the
goals, looking at earlier siblings of `texify` and then of its ancestors. -/
partial def findPrevTactic (mvarId : MVarId) (t : InfoTree) : Option (ContextInfo × TacticInfo) :=
  (go none t).bind id
where
  isTexify : Info → Bool
    | .ofTacticInfo ti => ti.stx.getKind == ``texifyTac && ti.goalsBefore.contains mvarId
    | _ => false
  /-- A tactic that changed the goals. -/
  changingTactic? (ctx? : Option ContextInfo) : InfoTree → Option (ContextInfo × TacticInfo)
    | .context i t => changingTactic? (i.mergeIntoOuter? ctx?) t
    | .node (.ofTacticInfo ti) _ =>
      if ti.goalsBefore != ti.goalsAfter then ctx?.map (·, ti) else none
    | _ => none
  /-- `none` if `texify` is not in the tree, `some none` if it is but no tactic before it was
  found yet. -/
  go (ctx? : Option ContextInfo) : InfoTree → Option (Option (ContextInfo × TacticInfo))
    | .context i t => go (i.mergeIntoOuter? ctx?) t
    | .hole _ => none
    | .node i cs =>
      if isTexify i then some none else
      let cs := cs.toArray
      match (List.range cs.size).findSome? fun j => (go ctx? cs[j]!).map (j, ·) with
      | none => none
      | some (_, some r) => some (some r)
      | some (j, none) =>
        some <| (List.range j).reverse.findSome? fun k => changingTactic? ctx? cs[k]!

/-- Parameters for `LatexDisplay.diff`. -/
structure LatexDiff.Params where
  /-- A position in the proof (where the display is shown). -/
  pos : Lsp.Position
  /-- The goal shown by `texify`. -/
  mvarId : MVarId
  deriving Server.RpcEncodable

/-- The diff for the goal shown by `texify`: the goal before and after the last tactic that
changed it, with the changes marked. Returns `none` if there is no such tactic. -/
@[server_rpc_method]
def LatexDisplay.diff (p : LatexDiff.Params) : Server.RequestM (Server.RequestTask (Option LatexDiff)) :=
  Server.RequestM.withWaitFindSnapAtPos p.pos fun snap => do
    let some (ci, prev) := findPrevTactic p.mvarId snap.infoTree | return none
    goalDiff ci prev p.mvarId
