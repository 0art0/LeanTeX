import Lake
open Lake DSL

require "leanprover-community" / "proofwidgets4" @ git "v0.0.111"

package LeanTeX { }

/-- The bundled JavaScript for the `LeanTeX.LatexDisplay` widget, built from `widget/src`
with `npm run build` in `widget/`. It is checked in, so building LeanTeX does not need npm.
Declaring it here makes Lake rebuild `LeanTeX.Widget` (which uses `include_str`) when it changes. -/
input_file latexDisplayJs where
  path := "widget" / "dist" / "latexDisplay.js"
  text := true

@[default_target]
lean_lib LeanTeX where
  needs := #[latexDisplayJs]
