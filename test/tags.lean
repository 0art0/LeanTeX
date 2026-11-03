import LeanTeX
import Lean.Elab.Tactic.Guard

/-! Tests for subexpression tracking (`LeanTeX.run_latexPPTagged`). -/

set_option linter.unusedVariables false

open Lean LeanTeX

/-- The subterm of `e` at `p`, without instantiating bound variables. -/
partial def rawSubexpr? (e : Expr) (p : SubExpr.Pos) : Option Expr :=
  p.toArray.foldlM (init := e) fun e i => go e i
where
  go : Expr → Nat → Option Expr
    | .mdata _ e, i => go e i
    | .app f _, 0 | .lam _ f _ _, 0 | .forallE _ f _ _, 0 | .letE _ f _ _ _, 0 | .proj _ _ f, 0 => some f
    | .app _ a, 1 | .lam _ _ a _, 1 | .forallE _ _ a _, 1 | .letE _ _ a _ _, 1 => some a
    | .letE _ _ _ b _, 2 => some b
    | _, _ => none

/-- Prints the tagged LaTeX, checks that removing the tags gives the `#latex` output,
and checks each tag's expression against the subterm at its position. A tag's expression may
differ from the raw subterm by having free variables in place of bound variables,
which is shown as `(inst)`. -/
elab tk:"#latex_tags " e:term : command => do
  Elab.Command.runTermElabM fun _ => do
    let e ← Elab.Term.elabTerm e none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let plain ← run_latexPP e {}
    let (tagged, tags) ← run_latexPPTagged e {}
    let tt := parseTaggedLatex tagged
    unless tt.stripTags == plain do
      throwError "tags change the output:\n{tt.stripTags}\nvs\n{plain}"
    let mut used : Array Nat := #[]
    let rec collect (tt : Widget.TaggedText Nat) (acc : Array Nat) : Array Nat :=
      match tt with
      | .text _ => acc
      | .append as => as.foldl (fun acc t => collect t acc) acc
      | .tag t a => collect a (acc.push t)
    used := collect tt #[]
    let mut lines := #[]
    for t in used do
      let some tag := tags[t]? | throwError "unknown tag {t}"
      let some raw := rawSubexpr? e tag.pos | throwError "bad position {tag.pos}"
      let status ←
        if tag.binder then
          -- The name of a bound variable: `pos` is the binder, and `expr` the variable.
          unless raw.consumeMData.isBinding && tag.expr.isFVar do
            throwError "binder tag {t} at {tag.pos}: {tag.expr} is not a variable bound by {raw}"
          let some decl := tag.lctx.find? tag.expr.fvarId! | throwError "unknown variable"
          lines := lines.push s!"{tag.pos} binder {decl.userName}"
          continue
        else if raw == tag.expr then pure ""
        else if raw.hasLooseBVars && raw.approxDepth == tag.expr.approxDepth then pure " (inst)"
        else throwError "tag {t} at {tag.pos}: {tag.expr} is not {raw}"
      let s ← Meta.withLCtx tag.lctx {} do pure s!"{tag.pos} {← Meta.ppExpr tag.expr}{status}"
      lines := lines.push s
    logInfoAt tk m!"{tagged}\n{"\n".intercalate lines.toList}"

def a : Nat := 22
def f : Nat → Nat → Nat := λ x y => x + y
variable (b : Nat) (x : Nat)

/--
info: \class{lean-se-0}{\class{lean-se-1}{\class{lean-se-2}{1} + \class{lean-se-3}{2}} + \class{lean-se-4}{3}}
/ 1 + 2 + 3
/0/1 1 + 2
/0/1/0/1 1
/0/1/1 2
/1 3
-/
#guard_msgs in
#latex_tags 1 + 2 + 3
/--
info: \class{lean-se-0}{\class{lean-se-1}{b} + \class{lean-se-2}{\class{lean-se-3}{b} \cdot \class{lean-se-4}{b}}}
/ b + b * b
/0/1 b
/1 b * b
/1/0/1 b
/1/1 b
-/
#guard_msgs in
#latex_tags b + b * b
/--
info: \class{lean-se-0}{\class{lean-se-1}{(\class{lean-se-2}{b} + \class{lean-se-3}{1})}^{\class{lean-se-4}{2}}}
/ (b + 1) ^ 2
/0/1 b + 1
/0/1/0/1 b
/0/1/1 1
/1 2
-/
#guard_msgs in
#latex_tags (b + 1)^2
/--
info: \class{lean-se-0}{\class{lean-se-1}{(\class{lean-se-2}{(\class{lean-se-3}{b} + \class{lean-se-4}{1})}^{\class{lean-se-5}{2}})}^{\class{lean-se-6}{3}}}
/ ((b + 1) ^ 2) ^ 3
/0/1 (b + 1) ^ 2
/0/1/0/1 b + 1
/0/1/0/1/0/1 b
/0/1/0/1/1 1
/0/1/1 2
/1 3
-/
#guard_msgs in
#latex_tags ((b + 1)^2)^3
/--
info: \class{lean-se-0}{\class{lean-se-1}{\text{f}}(\class{lean-se-2}{\class{lean-se-3}{\text{a}} + \class{lean-se-4}{b}}, \class{lean-se-5}{2})}
/ f (a + b) 2
/0/0 f
/0/1 a + b
/0/1/0/1 a
/0/1/1 b
/1 2
-/
#guard_msgs in
#latex_tags f (a + b) 2
/--
info: \class{lean-se-0}{\forall \class{lean-se-9}{y} : \class{lean-se-1}{\mathbb{N}},\ \class{lean-se-2}{\class{lean-se-3}{\class{lean-se-4}{y} + \class{lean-se-5}{b}} = \class{lean-se-6}{\class{lean-se-7}{b} + \class{lean-se-8}{y}}}}
/ ∀ (y : Nat), y + b = b + y
/ binder y
/0 Nat
/1 y + b = b + y (inst)
/1/0/1 y + b (inst)
/1/0/1/0/1 y (inst)
/1/0/1/1 b
/1/1 b + y (inst)
/1/1/0/1 b
/1/1/1 y (inst)
-/
#guard_msgs in
#latex_tags ∀ y : Nat, y + b = b + y
/--
info: \class{lean-se-0}{\forall \class{lean-se-17}{y} : \class{lean-se-1}{\mathbb{N}},\ \class{lean-se-2}{\forall \class{lean-se-16}{z} : \class{lean-se-3}{\mathbb{N}},\ \class{lean-se-4}{\class{lean-se-5}{\class{lean-se-6}{y} \leq \class{lean-se-7}{z}} \implies \class{lean-se-8}{\exists \class{lean-se-15}{w} : \class{lean-se-9}{\mathbb{N}},\ \class{lean-se-10}{\class{lean-se-11}{\class{lean-se-12}{y} + \class{lean-se-13}{w}} = \class{lean-se-14}{z}}}}}}
/ ∀ (y z : Nat), y ≤ z → ∃ w, y + w = z
/ binder y
/0 Nat
/1 ∀ (z : Nat), y ≤ z → ∃ w, y + w = z (inst)
/1 binder z
/1/0 Nat
/1/1 y ≤ z → ∃ w, y + w = z (inst)
/1/1/0 y ≤ z (inst)
/1/1/0/0/1 y (inst)
/1/1/0/1 z (inst)
/1/1/1 ∃ w, y + w = z (inst)
/1/1/1/1 binder w
/1/1/1/1/0 Nat
/1/1/1/1/1 y + w = z (inst)
/1/1/1/1/1/0/1 y + w (inst)
/1/1/1/1/1/0/1/0/1 y (inst)
/1/1/1/1/1/0/1/1 w (inst)
/1/1/1/1/1/1 z (inst)
-/
#guard_msgs in
#latex_tags ∀ y z : Nat, y ≤ z → ∃ w, y + w = z
/--
info: \class{lean-se-0}{(\class{lean-se-1}{y} : \class{lean-se-2}{\mathbb{N}}, \class{lean-se-3}{z} : \class{lean-se-4}{\mathbb{N}}) \mapsto \class{lean-se-5}{\class{lean-se-6}{\class{lean-se-7}{y} + \class{lean-se-8}{z}} + \class{lean-se-9}{b}}}
/ fun y z => y + z + b
/ binder y
/0 Nat
/1 binder z
/1/0 Nat
/1/1 y + z + b (inst)
/1/1/0/1 y + z (inst)
/1/1/0/1/0/1 y (inst)
/1/1/0/1/1 z (inst)
/1/1/1 b
-/
#guard_msgs in
#latex_tags (λ (y z : Nat) => y + z + b)
/--
info: \class{lean-se-0}{\class{lean-se-1}{b} \neq \class{lean-se-2}{2}}
/ ¬b = 2
/1/0/1 b
/1/1 2
-/
#guard_msgs in
#latex_tags ¬ (b = 2)
/--
info: \class{lean-se-0}{\frac{\class{lean-se-1}{\class{lean-se-2}{b} + \class{lean-se-3}{1}}}{\class{lean-se-4}{\class{lean-se-5}{b} - \class{lean-se-6}{1}}}}
/ (b + 1) / (b - 1)
/0/1 b + 1
/0/1/0/1 b
/0/1/1 1
/1 b - 1
/1/0/1 b
/1/1 1
-/
#guard_msgs in
#latex_tags (b + 1) / (b - 1)
/--
info: \class{lean-se-0}{\class{lean-se-1}{\mathbb{N}} \times \class{lean-se-2}{(\class{lean-se-4}{n} : \class{lean-se-3}{\mathbb{N}}) \times \class{lean-se-5}{\class{lean-se-6}{\mathbb{N}_{< \class{lean-se-7}{n}}} \times \class{lean-se-8}{\mathbb{N}}}}}
/ Nat × (n : Nat) × Fin n × Nat
/0/1 Nat
/1 (n : Nat) × Fin n × Nat
/1/1 binder n
/1/1/0 Nat
/1/1/1 Fin n × Nat (inst)
/1/1/1/0/1 Fin n (inst)
/1/1/1/0/1/1 n (inst)
/1/1/1/1 Nat
-/
#guard_msgs in
#latex_tags Nat × (n : Nat) × Fin n × Nat
/--
info: \class{lean-se-0}{\exists \class{lean-se-9}{p} : \class{lean-se-1}{\class{lean-se-2}{\mathbb{N}} \times \class{lean-se-3}{\mathbb{N}}},\ \class{lean-se-4}{\class{lean-se-5}{\class{lean-se-6}{\text{Prod.fst}}(\class{lean-se-7}{p})} = \class{lean-se-8}{b}}}
/ ∃ p, p.fst = b
/1 binder p
/1/0 Nat × Nat
/1/0/0/1 Nat
/1/0/1 Nat
/1/1 p.fst = b (inst)
/1/1/0/1 p.fst (inst)
/1/1/0/1/0/0/0 @Prod.fst
/1/1/0/1/1 p (inst)
/1/1/1 b
-/
#guard_msgs in
#latex_tags ∃ p : Nat × Nat, p.1 = b
