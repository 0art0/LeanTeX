import Lean.Data
import Lean.KeyedDeclsAttribute
import Lean.PrettyPrinter
import Lean.Parser
import Lean.Elab.Command
import Lean.Elab.AuxDef
import LeanTeX.Defs

/-! # LaTeX pretty printer for math expressions

This module sets up the basic system for transforming a given `Lean.Expr` into
a human-readable LaTeX expression. Unlike the usual Lean pretty printer, we do not aim for
total computer-interpretable accuracy -- the resulting LaTeX expressions should be at a
similar level of detail to human-written mathematics, where a human's mental elaboratation
process could fill in the missing details (that is, the output is permitted to be ambiguous
in ways that mathematicians are accustomed to).

The function `LeanTeX.latex` is the main entry point for the pretty printer.

The specific pretty printers are in the `LeanTeX.Builtins` module. We use the attributes
system to record the pretty printers, and one can't apply an attribute in the same module in
which it was defined.

There are two kinds of pretty printers that can be registered: the generic one uses the attribute
`latex_pp` and there is a specialized one `latex_pp_app` for function applications. Those attributes
are keyed by "kind" which is a `Lean.Name`. When pretty-printing an `Expr`, those kinds are compared to
one computed from the expression by `LeanTeX.getExprKind`. The hierarchical nature of names is used here
to first try the most specific pretty-printer, matching the full kind, and then, in case of failure,
try to remove the last name part and iterate, see `LeanTeX.latexPPFor`.

The fact that function applications use pretty-printers registered using the attribute `latex_pp_app`
cannot be seen in this file, this happens in the function application builtin pretty-printer
from the `Builtins` file.

One complexity in the design is that human-written mathematics is a 2D notation. A simple
precedence-level-based system does not work. For example, in `(a/b)^c` as
`(\tfrac{a}{b})^c`, we have the parentheses there *not* because exponentiation has higher
precedence than division, but instead because in the 2D layout exponentiation would be
otherwise indistinguishable from being an exponent on `a`. Pieces of LaTeX code are stored in
objects with type `LeanTeX.LatexData`. This type is has two constructors: `Atom` for pieces that
can be decorated with subscripts or superscripts without parentheses and `Row` for pieces that
require parentheses. In the `Row` case, the `LatexData` has binding powers on both sides, left and right.
Those represent how resistant an expression is to be broken up if it is inserted into another expression.
This resistance is used when deciding whether parentheses should be used.
-/

open Lean

namespace LeanTeX

/-- A `LatexPrinter` is the type of a function that pretty prints expressions.
These are registered using the `latex_pp` attribute. -/
abbrev LatexPrinter := Expr → LatexPrinterM LatexData

/-- `latex_pp` attribute registration function. -/
unsafe def mkLatexPPAttribute : IO (KeyedDeclsAttribute LatexPrinter) :=
  KeyedDeclsAttribute.init {
    name  := `latex_pp
    descr := "Register a LaTeX pretty printer for a kind of an expression.
See `LeanTeX.getExprKind` for the possible kinds.

[latex_pp k] registers a `TeXPP.TeXPrinter` for kind `k`.",
    valueTypeName := `LeanTeX.LatexPrinter
    evalKey := fun _ stx => do
      let id := (← Attribute.Builtin.getIdent stx).getId
      if id.isAnonymous then
        throwError "Anonymous name"
      return id
  } `LatexPrinter.latexPPAttribute

@[init mkLatexPPAttribute] opaque latexPPAttribute : KeyedDeclsAttribute LatexPrinter

/-- Structure representing the data for a parameter. Used, for example, in getting the list
of the types of arguments to a function. -/
structure ParamKind where
  name        : Name
  type        : Expr
  bInfo       : BinderInfo
  defVal      : Option Expr := none
  isAutoParam : Bool := false
  deriving Repr, Inhabited

/-- Checks whether the given parameter is explicit, not autoparam and has no default value. -/
def ParamKind.isRegularExplicit (param : ParamKind) : Bool :=
  param.bInfo.isExplicit && !param.isAutoParam && param.defVal.isNone

/-- Return array whose elements correspond to parameters of `e`. -/
partial def getParamKinds (e : Expr) : MetaM (Array ParamKind) := do
  try
    Meta.withTransparency Meta.TransparencyMode.all <|
      forallTelescopeArgs e.getAppFn e.getAppArgs fun params _ => do
        params.mapM fun param => do
          let l ← param.fvarId!.getDecl
          pure { name := l.userName, type := l.type,
                 bInfo := l.binderInfo, defVal := l.type.getOptParamDefault?, isAutoParam := l.type.isAutoParam }
  catch _ => pure #[] -- expr might be nonsensical
where
  forallTelescopeArgs f args k := do
    Meta.forallBoundedTelescope (← Meta.inferType f) args.size fun xs b =>
      if xs.isEmpty || xs.size == args.size then
        -- we still want to consider optParams
        Meta.forallTelescopeReducing b fun ys b => k (xs ++ ys) b
      else
        forallTelescopeArgs (mkAppN f $ args.shrink xs.size) (args.extract xs.size args.size) fun ys b =>
          k (xs ++ ys) b

/-- Latex printers specifically for applications. Takes the function, its arguments, and
an array describing the corresponding function parameters. -/
abbrev LatexAppPrinter := Expr → Array Expr → Array ParamKind → LatexPrinterM LatexData

/-- `latex_pp_app` attribute registration function. -/
unsafe def mkLatexPPAppAttribute : IO (KeyedDeclsAttribute LatexAppPrinter) :=
  KeyedDeclsAttribute.init {
    name  := `latex_pp_app
    descr := "Register a LaTeX pretty printer for applications of a given constant.

[latex_pp_app const.c] registers a `LatexAppPrinter` for applications of the constant `c`.
[latex_pp_app app] registers a `LatexAppPrinter` for non-specific applications.",
    valueTypeName := `LeanTeX.LatexAppPrinter
    evalKey := fun _ stx => do
      let id := (← Attribute.Builtin.getIdent stx).getId
      if id.isAnonymous then
        throwError "Anonymous name"
      return id
  } `LatexPrinter.latexPPAppAttribute

@[init mkLatexPPAppAttribute] opaque latexPPAppAttribute : KeyedDeclsAttribute LatexAppPrinter

/-- Adds primes or indices to a name. -/
private def appendIndexOrPrimeAfter (n : Name) (idx : Nat) : Name :=
  n.modifyBase fun
    | .str p s => Name.mkStr p <| if h : idx < alts.size then s ++ alts[idx] else s ++ "_" ++ toString (idx + 1)
    | n       => Name.mkStr n ("_" ++ toString idx)
  where alts : Array String := #["'", "''", "'''"]

/-- Get a fresh name based on the suggested name that doesn't shadow anything in `body`.
(Stolen from the Lean pretty printer.) Also makes sure the name is not in the `avoidNames` list. -/
partial def getUnusedName (suggestion : Name) (body : Expr) : LatexPrinterM Name := do
  -- Use a nicer binder name than `[anonymous]`.
  let suggestion := if suggestion.isAnonymous then `a else suggestion
  let suggestion := dropNum suggestion.simpMacroScopes
  let lctx ← getLCtx
  let avoidNames := (← read).avoidNames
  if (← read).allowShadowing && !avoidNames.contains suggestion && !bodyUsesSuggestion lctx suggestion then -- safe shadowing
    return suggestion
  let rec loop (i : Nat) : Name :=
    let curr := appendIndexOrPrimeAfter suggestion i
    if lctx.usesUserName curr || avoidNames.contains curr then loop (i + 1)
    else curr
  return if lctx.usesUserName suggestion then loop 0
         else suggestion
where
  bodyUsesSuggestion (lctx : LocalContext) (suggestion' : Name) : Bool :=
    Option.isSome <| body.find? fun
      | Expr.fvar fvarId =>
        match lctx.find? fvarId with
        | none      => false
        | some decl => decl.userName == suggestion'
      | _ => false
  dropNum : Name → Name
    | .num base _ => base
    | name => name

/-! ### Subexpression tracking

When `Config.tagSubexprs` is set, `latexPP` tries to work out where the expression it is given
sits inside the root expression, so that the output can be made interactive. This is done
implicitly, so that pretty printers do not need to know about it: `latexPP e` searches for `e` in
`Config.expr?` (the nearest enclosing expression that was located), first by pointer equality
and then structurally. Expressions that pretty printers build themselves (for example `Ne a b`
from `¬(a = b)`) are not found, but their subexpressions still are, since the search scope
stays at the nearest located ancestor. If an expression occurs more than once, we use
the leftmost occurrence that was not already used.

Binder bodies are instantiated with free variables before being printed (see
`withBindingBodyUnusedName`), so the search also substitutes these free variables when comparing
against the bodies of binders that are being printed. -/

/-- Implementation of `exprPtrEq`. -/
private unsafe def exprPtrEqUnsafe (a b : Expr) : Bool := ptrEq a b

/-- Pointer equality of expressions. (As usual with pointer equality, a `false` result means
nothing.) -/
@[implemented_by exprPtrEqUnsafe]
private opaque exprPtrEq (a b : Expr) : Bool

/-- Pre-order (so, leftmost-first) search of `t`, which is at position `p`, for a subexpression
satisfying `isMatch`, which is also passed the free variables substituted for the loose bound
variables of the subexpression (innermost last), where known.
Positions are as in `Lean.SubExpr.Pos`; in particular, `mdata` does not count as a step. -/
private partial def findPosAux (binders : Array (SubExpr.Pos × Expr)) (ok : SubExpr.Pos → Bool)
    (isMatch : Expr → Array (Option Expr) → Bool) (t : Expr) (p : SubExpr.Pos)
    (fvars : Array (Option Expr)) : Option SubExpr.Pos :=
  if !t.isMData && ok p && isMatch t fvars then
    some p
  else
    match t with
    | .app f a => go f p.pushAppFn fvars <|> go a p.pushAppArg fvars
    | .lam _ d b _ | .forallE _ d b _ =>
      go d p.pushBindingDomain fvars
        <|> go b p.pushBindingBody (fvars.push <| binders.find? (·.1 == p) |>.map (·.2))
    | .letE _ ty v b _ =>
      go ty p.pushLetVarType fvars <|> go v p.pushLetValue fvars
        <|> go b p.pushLetBody (fvars.push none)
    | .mdata _ e => go e p fvars
    | .proj _ _ e => go e p.pushProj fvars
    | _ => none
where
  go := findPosAux binders ok isMatch

/-- Whether `t`, whose loose bound variables are to be replaced by `fvars` (innermost last),
is structurally equal to `e`. -/
private def matchesInstantiated (e t : Expr) (fvars : Array (Option Expr)) : Bool :=
  if !t.hasLooseBVars then
    t == e
  else if t.approxDepth != e.approxDepth then
    false
  else
    -- Only the innermost binders with known free variables can be substituted.
    let known := (fvars.toList.reverse.takeWhile Option.isSome).reverse.filterMap id
    if t.looseBVarRange > known.length then
      false
    else
      t.instantiateRev known.toArray == e

/-- Find the position of `e` in the current search scope (see `Config.expr?`).
Unless `allowUsed` is set, positions that were already used by `latexPP` are skipped. -/
def findSubexprPos (e : Expr) (allowUsed : Bool := false) : LatexPrinterM (Option SubExpr.Pos) := do
  let cfg ← read
  let some root := cfg.expr? | return none
  let used := (← get).usedPos
  let ok (p : SubExpr.Pos) : Bool := allowUsed || !used.contains p.asNat
  if let some (_, p) := cfg.knownPos.find? (fun (e', p) => exprPtrEq e e' && ok p) then
    return p
  let find := findPosAux cfg.binderFVars ok (t := root) (p := cfg.pos) (fvars := #[])
  return find (fun t _ => exprPtrEq t e) <|> find (matchesInstantiated e)

/-- Run `m` with `e` (found at `pos`) as the scope for subexpression searches. -/
def withSubexprScope (e : Expr) (pos : SubExpr.Pos) (m : LatexPrinterM α) : LatexPrinterM α :=
  withReader (fun cfg => { cfg with pos, expr? := e, binderFVars := #[] }) m

/-- If subexpression tracking is enabled and `e` can be located, run `m` with `e` as
the search scope and tag its result. Otherwise just run `m`. -/
def withSubexprTag (e : Expr) (m : LatexPrinterM LatexData) : LatexPrinterM LatexData := do
  -- `mdata` has no position of its own, so we let the expression inside it be tagged instead.
  unless (← read).tagSubexprs && !e.isMData do return ← m
  let some pos ← findSubexprPos e | m
  let tag := (← get).tags.size
  let lctx ← getLCtx
  modify fun s => { s with
    tags := s.tags.push { expr := e, pos, lctx }
    usedPos := s.usedPos.insert pos.asNat }
  return .Tagged tag (← withSubexprScope e pos m)

/-- Runs `x`, and if it fails, restores the printer state and runs `y`.
Used when trying pretty printers, so that subexpressions used by a failed printer are not
considered used. -/
def tryOrElse (x : LatexPrinterM α) (y : Unit → LatexPrinterM α) : LatexPrinterM α := do
  let s ← get
  try x catch _ => set s; y ()

/-- Run `d` for the body `body` of the binder `e`, where `fvar` was substituted for the bound
variable, recording the position of `body` for subexpression tracking. -/
private def withBindingBodyPos (e fvar body : Expr) (d : LatexPrinterM α) : LatexPrinterM α := do
  unless (← read).tagSubexprs do return ← d
  let some pos ← findSubexprPos e (allowUsed := true) | d
  withReader (fun cfg => { cfg with
    binderFVars := cfg.binderFVars.push (pos, fvar)
    knownPos := cfg.knownPos.push (body, pos.pushBindingBody) }) d

/-- Given an `Expr` that is a `.forallE` or `.lam`, execute the given `d` in the context of a
local declaration. The function `d` is provided the name of the new local and its type.  -/
def withBindingBodyUnusedName (e : Expr) (d : Name → Expr → LatexPrinterM α) : LatexPrinterM α := do
  let n ← getUnusedName e.bindingName! e.bindingBody!
  Meta.withLocalDecl n e.binderInfo e.bindingDomain! fun fvar => do
    let body := e.bindingBody!.instantiate1 fvar
    withBindingBodyPos e fvar body (d n body)

/-- Given an expression that is a function, ensure it is an `Expr.lam` by doing 1-variable
eta expansion as needed.
If provided, the `suggestion?` argument gives the name for the new argument to the lambda, and otherwise
the name comes from the function's pi type. -/
def ensureLam (e : Expr) (suggestion? : Option Name) : MetaM Expr := do
  if e.isLambda then
    return e
  else
    let ty ← Meta.whnf (← Meta.inferType e)
    guard ty.isForall
    Meta.withLocalDeclD (suggestion?.getD ty.bindingName!) ty.bindingDomain! fun fvar =>
      Meta.mkLambdaFVars #[fvar] (.app e fvar)

/-- Given an `Expr` that is a function, use `ensureLam` to ensure it is a lambda expression
and then execute the given `d` using `withBindingBodyUnusedName`. -/
def withBindingBodyUnusedName' (e : Expr) (suggestion? : Option Name) (d : Name → Expr → LatexPrinterM α) : LatexPrinterM α := do
  let e ← ensureLam e suggestion?
  withBindingBodyUnusedName e d

/-- Get a description of the constructor of the expression as a `Name`.
Used as a key for the `latex_pp` attribute. -/
def getExprKind : Expr → Name
  | Expr.bvar _          => `bvar
  | Expr.fvar _          => `fvar
  | Expr.mvar _          => `mvar
  | Expr.sort _          => `sort
  | Expr.const c _       => `const ++ c
  | Expr.app fn _        =>
    match fn.getAppFn with
      | Expr.const c _   => `app ++ c
      | _                => `app
  | Expr.lam _ _ _ _     => `lam
  | Expr.forallE _ _ _ _ => `forallE
  | Expr.letE _ _ _ _ _  => `letE
  | Expr.lit _           => `lit
  | Expr.mdata m _       =>
    match m.entries with
    | [(key, _)] => `mdata ++ key
    | _   => `mdata
  | Expr.proj _ _ _      => `proj

/-- The failsafe Latex pretty printer, which just runs the usual Lean pretty printer and wraps it
in some LaTeX to make it clear this was not handled. Mainly used for debugging purposes. -/
def defaultLatexPP (e : Expr) : LatexPrinterM LatexData := do
  let f ← PrettyPrinter.ppExpr e
  -- TODO try to do `Format` -> reasonable latex.
  return LatexData.ofString <| s!"\\operatorname\{Lean}\\left[\\text\{{f}}\\right]"

/-- For the given kind (as in `getExprKind`), run the associated pretty printer.

The general algorithm for the specified `kind`:
1. Find the first handler (with respect to reverse-definition order) with
   attribute `latex_pp kind` that does not fail. If one exists, we're done.
2. If it's different, use `Name.getRoot kind` as the new `kind` and try again.
3. Otherwise fail. -/
partial def latexPPFor (e : Expr) (kind : Name) : LatexPrinterM LatexData := do
  if kind.isAnonymous then
    failure
  for pp in latexPPAttribute.getValues (← getEnv) kind do
    let s ← get
    try
      return ← pp e
    catch _ => set s
  if kind.getRoot != kind then
    latexPPFor e kind.getRoot
  else
    failure

/-- Runs the pretty printer for `e` using the `latexPPFor` algorithm with kind `getExprKind e`,
and if this fails it runs `defaultLatexPP`.

If `Config.tagSubexprs` is set, the result is tagged with the position of `e`
(see `withSubexprTag`). -/
def latexPP (e : Expr) : LatexPrinterM LatexData :=
  withSubexprTag e <| tryOrElse (latexPPFor e (getExprKind e)) fun _ => defaultLatexPP e

/-- Run the LaTeX pretty printer for the expression `e`, using the given configuration. -/
def run_latexPP (e : Expr) (config : Config) : MetaM String := do
  let pp : LatexPrinterM LatexData := latexPP e
  let data : LatexData ← (pp.run config).run' {}
  return data.latex.1

/-- Like `run_latexPP`, but with subexpression tracking. The LaTeX marks the output for each
located subexpression with `tagLatex`, and the returned array gives the subexpression for each tag.
Use `parseTaggedLatex` to turn the LaTeX into `TaggedText`. -/
def run_latexPPTagged (e : Expr) (config : Config) : MetaM (String × Array SubexprTag) := do
  let pp : LatexPrinterM LatexData := latexPP e
  let config := { config with tagSubexprs := true, expr? := e, pos := .root }
  let (data, s) ← (pp.run config).run {}
  return (data.latex.1, s.tags)

/-- Parse LaTeX produced by `run_latexPPTagged`, turning the `tagLatex` markers into tags.
Leaves are LaTeX fragments. Removing the tags (with `TaggedText.stripTags`) gives the same LaTeX
as `run_latexPP`. -/
partial def parseTaggedLatex (s : String) : Widget.TaggedText Nat :=
  let cs := s.toList.toArray
  (go cs 0 #[] "").1
where
  /-- The `tagLatex` prefix. -/
  marker : List Char := "\\class{lean-se-".toList
  /-- Whether `marker` occurs at position `i`. -/
  isMarkerAt (cs : Array Char) (i : Nat) : Bool :=
    marker.length + i ≤ cs.size && (List.range marker.length).all fun j => cs[i + j]! == marker[j]!
  /-- Collect the current text into `acc`. -/
  flush (acc : Array (Widget.TaggedText Nat)) (text : String) : Array (Widget.TaggedText Nat) :=
    if text.isEmpty then acc else acc.push (.text text)
  /-- Combine the parts of a group. -/
  mk (acc : Array (Widget.TaggedText Nat)) : Widget.TaggedText Nat :=
    if h : acc.size = 1 then acc[0] else .append acc
  /-- Parse from position `i` until the end of the current tag, given by an unmatched `}`.
  Returns the parsed text and the position after the `}`. `depth` counts open braces. -/
  go (cs : Array Char) (i : Nat) (acc : Array (Widget.TaggedText Nat)) (text : String)
      (depth : Nat := 0) : Widget.TaggedText Nat × Nat :=
    if h : i < cs.size then
      let c := cs[i]
      if isMarkerAt cs i then
        -- `\class{lean-se-N}{`
        let digits := (cs.extract (i + marker.length) cs.size).toList.takeWhile Char.isDigit
        let tag := String.ofList digits |>.toNat!
        let (inner, j) := go cs (i + marker.length + digits.length + 2) #[] ""
        go cs j ((flush acc text).push (.tag tag inner)) "" depth
      else if c == '\\' && i + 1 < cs.size then
        go cs (i + 2) acc (text.push c |>.push cs[i + 1]!) depth
      else if c == '{' then
        go cs (i + 1) acc (text.push c) (depth + 1)
      else if c == '}' then
        if depth == 0 then
          (mk (flush acc text), i + 1)
        else
          go cs (i + 1) acc (text.push c) (depth - 1)
      else
        go cs (i + 1) acc (text.push c) depth
    else
      (mk (flush acc text), i)

/-- Pretty prints an expression that is a function application using the printers tagged with the
`latex_pp_app` attribute for the specified kind. If they fail, tries using `kind.getRoot` and
then `any`. -/
partial def latexPPAppFor (kind : Name) (f : Expr) (args : Array Expr) (pkinds : Array ParamKind) : LatexPrinterM LatexData := do
  if kind.isAnonymous then
    failure
  for pp in latexPPAppAttribute.getValues (← getEnv) kind do
    let s ← get
    try
      return ← pp f args pkinds
    catch _ => set s
  if kind.getRoot != kind then
    latexPPAppFor kind.getRoot f args pkinds
  else if kind != `any then
    latexPPAppFor `any f args pkinds
  else
    failure

end LeanTeX
