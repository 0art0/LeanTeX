# LeanTeX

This is a Lean 4 library for pretty printing expressions as LaTeX.

For Mathlib LaTeX pretty printers, see https://github.com/kmill/LeanTeX-mathlib

## Interactive display

`#texify e` displays the expression `e` in LaTeX in the infoview, and the `texify` tactic displays
the current goal. Subexpressions in the display behave like those in the goal view:

* hovering highlights a subexpression and every other occurrence of it (in the whole goal),
  and after a moment shows its type and docstring;
  clicking pins the tooltip, and clicking elsewhere closes it;
* the hover shows the subexpression and its type in LaTeX, and is itself interactive, so hovers
  can be nested. The TeX/Lean switch in a hover shows them in Lean syntax instead (remembered);
* variables (including bound variables, also where they are bound) are colored, each with its own
  color, consistently across the display and its hovers. The colors adapt to the editor theme;
  `set_option leantex.colorVariables false` turns this off, and
  `set_option leantex.variableColors "#e06c75, #61afef, #98c379"` sets the colors
  (any CSS colors, used in order of appearance);
* Ctrl/⌘-hovering underlines subexpressions with a definition, and Ctrl/⌘-clicking goes to it;
* shift-clicking (un)selects subexpressions, which are then listed in Lean syntax below the
  formula. For `texify`, each selection is a goal location (a hypothesis, part of a hypothesis
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
