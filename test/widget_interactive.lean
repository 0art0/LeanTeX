import LeanTeX

/-! Manual test for the interactive LaTeX display. Put the cursor on `#texify` or `texify`,
then hover over parts of the formula in the infoview to see their types and docstrings,
and shift-click to select subexpressions. -/

set_option linter.unusedVariables false

#texify ∀ n : Nat, (n + 1)^2 = n^2 + 2 * n + 1

example (x y : Nat) (h : x < y) : (x + 1)^2 / (y - 1) ≤ 2 * x + y := by
  texify
  sorry

example {α β : Type} (f : α → β) (s : α → Prop) : ∀ b, ∃ a, s a ∧ f a = b := by
  texify
  sorry

-- Diffs: `texify` highlights what `rw` changed, and the history button in its toolbar shows the
-- goal before `rw`.
example (x y : Nat) (h : x < y) : 2 * x ≤ x + y + x := by
  rw [Nat.two_mul]
  texify
  sorry

-- Folding: the proof in `⟨2, _⟩` starts out folded as `⋯` (see `pp.proofs`); click it to unfold,
-- and Alt-click any subexpression to fold it.
#texify (⟨2, by decide⟩ : Fin 3)
