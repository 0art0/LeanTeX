# LeanTeX

This is a Lean 4 library for pretty printing expressions as LaTeX.

For Mathlib LaTeX pretty printers, see https://github.com/kmill/LeanTeX-mathlib

## Interactive display

`#texify e` displays the expression `e` in LaTeX in the infoview, and the `texify` tactic displays
the current goal. Subexpressions in the display behave like those in the goal view:

* hovering highlights a subexpression and every other occurrence of it, also in the other
  formulas shown (hovers, the goal before the last tactic), and after a moment shows its type and
  docstring; clicking pins the tooltip, and clicking elsewhere closes it;
* in spotlight mode (the lightbulb in the toolbar, on by default) everything else is dimmed while
  hovering;
* the hover shows the subexpression and its type in LaTeX, and is itself interactive, so hovers
  can be nested. The TeX/Lean switch in a hover shows them in Lean syntax instead (remembered);
* for `texify`, the colors follow the goal view: hypothesis names use its hypothesis-name color
  (dimmed for inaccessible hypotheses, which are shown as `x^\dagger` for the goal view's `x✝`) and
  `⊢` its turnstile color;
* variables (including bound variables, also where they are bound) are colored, each with its own
  color, consistently across the display and its hovers. The colors adapt to the editor theme;
  `set_option leantex.colorVariables false` turns this off, and
  `set_option leantex.variableColors "#e06c75, #61afef, #98c379"` sets the colors
  (any CSS colors, used in order of appearance). The palette button in the toolbar shows a legend
  of the variables: hovering a variable there highlights it, and clicking it picks its color
  (remembered by name);
* Alt-clicking a subexpression folds it to `⋯` (as does the fold button in its hover), and clicking
  `⋯` unfolds it, together with the terms folded automatically inside it. As in the goal view,
  proofs and very deep terms start out folded, following
  `pp.proofs` and `pp.deepTerms`;
* for `texify`, what the last tactic changed is highlighted, as in the goal view (following
  `showTacticDiff`), and the history button shows the goal before that tactic, with what it
  changes highlighted;
* Ctrl/⌘-hovering underlines subexpressions with a definition, and Ctrl/⌘-clicking goes to it;
* shift-clicking (un)selects subexpressions, which are then listed below the formula.
  For `texify`, each selection is a goal location (a hypothesis, part of a hypothesis
  type or value, or part of the target). As in the goal view, the selection is cleared when the
  cursor moves. It is local to the widget and is not shared with the goal view;
* the context menu has "Go to Definition", "Select", "Unselect" and "Unselect All";
* the copy button at the top right copies the LaTeX source.

This works with any `latex_pp` rules: `latexPP` locates the expressions it is given inside the
expression being printed (see "Subexpression tracking" in `LeanTeX/Basic.lean`).
Expressions that a rule constructs itself are not interactive, but their subexpressions are.
Rules for binders should print the bound variable's name with `binderLatex name` (where `name` is
given by `withBindingBodyUnusedName`), so that it is colored and highlighted like the variable's
occurrences.

The client side of the widget is in `widget/` (TypeScript). The built file
`widget/dist/latexDisplay.js` is checked in, so building LeanTeX does not need npm.
After changing `widget/src`, rebuild it with
```
cd widget
npm install
npm run build
```
