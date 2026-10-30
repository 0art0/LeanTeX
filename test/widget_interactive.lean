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
