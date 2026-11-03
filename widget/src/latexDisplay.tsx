/**
 * Client side of `LeanTeX.LatexDisplay`: lines of LaTeX, rendered with the infoview's MathJax,
 * whose subexpressions can be interacted with like those of expressions in the goal view.
 *
 * The server sends each part of a line as `TaggedText<LatexTag>` whose leaves are LaTeX fragments.
 * We give each tagged subexpression an id `N` and wrap its LaTeX in `\class{lean-se-N}{...}`.
 * MathJax (SVG output) puts the class on the `<g>` element for the subexpression, which is how we
 * find subexpressions on the page. Since in SVG only glyphs receive pointer events, we find the
 * subexpression under the pointer using bounding boxes, and since `<g>` elements have no
 * background, highlights are boxes drawn behind the formula.
 *
 * Variables (free variables that are not proofs, including bound variables, which the server
 * instantiates) are colored: we wrap them in `\class{lean-var-K}{...}` and set `fill` for that class.
 * The colors are assigned in order of first appearance and shared with nested formulas
 * (`VarColorsContext`), so a variable has the same color in the display and in its hovers.
 *
 * The interactions follow the infoview's `InteractiveCode` (see `interactiveCode.tsx`,
 * `tooltips.tsx`, `hoverHighlight.tsx` and `goalLocation.tsx` in vscode-lean4):
 * - hovering highlights the innermost subexpression and every other occurrence of it, and shows
 *   its type and docstring after a delay. The type is rendered in LaTeX by the server
 *   (`LeanTeX.LatexDisplay.popup`) and is itself interactive, so hovers nest;
 * - clicking pins that tooltip, and clicking elsewhere closes it;
 * - Ctrl/⌘-hovering underlines subexpressions that have a definition to go to,
 *   and Ctrl/⌘-clicking goes there;
 * - Shift-clicking (un)selects a subexpression; the selection is cleared when the cursor moves;
 * - the context menu has "Go to Definition", "Select", "Unselect" and "Unselect All".
 *
 * Selection is local to this widget: panel widgets are rendered outside the infoview's
 * `LocationsContext`, so they cannot share the goal view's selection.
 */
import * as React from 'react'
import * as ReactDOM from 'react-dom'
import {
  DocumentPosition,
  EditorContext,
  GoalLocation,
  GoalsLocation,
  InfoPopup,
  InteractiveCode,
  InteractiveDiagnostics_infoToInteractive,
  Markdown,
  SubexprInfo,
  TaggedText,
  getGoToLocation,
  mapRpcError,
  useAsync,
  useRpcSession,
} from '@leanprover/infoview'

/** A reference to the server's information about a subexpression. */
type InfoRef = SubexprInfo['info']

/** Mirrors `LeanTeX.LatexTag`. */
interface LatexTag {
  info: InfoRef
  subexprPos?: string | null
  binder?: boolean
  fvarId?: string | null
  key: string
}

/** Mirrors `LeanTeX.LatexCode`. */
type LatexCode = TaggedText<LatexTag>

/** Mirrors `LeanTeX.LatexPart`. */
interface LatexPart {
  latex: LatexCode
  kind: 'text' | 'expr' | 'hyp' | 'hypType' | 'hypValue' | 'target'
  fvarId?: string | null
  name?: string | null
}

/** Mirrors `LeanTeX.LatexDisplay.Props`. `pos` is added by ProofWidgets. */
interface LatexDisplayProps {
  lines: LatexPart[][]
  mvarId?: string
  colorVariables?: boolean
  variableColors?: string[]
  pos: DocumentPosition
}

/** Mirrors `LeanTeX.LatexPopup`. */
interface LatexPopup {
  expr: LatexCode
  type?: LatexCode | null
  doc?: string | null
}

// ---------------------------------------------------------------------------------------------
// Variable colors

/** The default colors for variables: VS Code's chart colors, which are chosen to be legible in
 * the current color theme, with fallbacks for other editors. */
const DEFAULT_PALETTE = [
  'var(--vscode-charts-blue, #3794ff)',
  'var(--vscode-charts-orange, #d18616)',
  'var(--vscode-charts-purple, #b180d7)',
  'var(--vscode-charts-green, #4fb36b)',
  'var(--vscode-charts-red, #f14c4c)',
  'var(--vscode-terminal-ansiCyan, #11a8cd)',
  'var(--vscode-charts-yellow, #cca700)',
  'var(--vscode-terminal-ansiMagenta, #bc3fbc)',
]

/** At most this many colors are used, since there is a CSS rule for each. */
const MAX_COLORS = 64

/** The colors of variables: `index` maps free variables to indices into `palette`, in order of
 * first appearance (modulo the length of the palette). Nested formulas add their own variables. */
interface VarColors {
  palette: string[]
  index: Map<string, number>
}

const VarColorsContext = React.createContext<VarColors>({ palette: [], index: new Map() })

function makeVarColors(enabled: boolean, custom: string[]): VarColors {
  const palette = enabled ? (custom.length > 0 ? custom : DEFAULT_PALETTE).slice(0, MAX_COLORS) : []
  return { palette, index: new Map() }
}

function varColorIndex(vc: VarColors, fvarId: string): number | undefined {
  if (vc.palette.length === 0) return undefined
  let i = vc.index.get(fvarId)
  if (i === undefined) {
    i = vc.index.size
    vc.index.set(fvarId, i)
  }
  return i % vc.palette.length
}

/** CSS variables for the palette, to set on the root of each formula. */
function paletteStyle(vc: VarColors): React.CSSProperties {
  const style: Record<string, string> = {}
  vc.palette.forEach((c, i) => (style[`--lean-var-${i}`] = c))
  return style as React.CSSProperties
}

// ---------------------------------------------------------------------------------------------
// Styles

const STYLE = `
.lean-tex {
  --lt-fg: var(--vscode-editor-foreground, currentColor);
  --lt-accent: var(--vscode-focusBorder, #3b82f6);
  --lt-link: var(--vscode-textLink-foreground, var(--lt-accent));
  --lt-hairline: color-mix(in srgb, var(--lt-fg) 12%, transparent);
  --lt-ease: cubic-bezier(.2, .8, .2, 1);
  position: relative;
  /* Keep the z-indices below local, so that tooltips (appended to the body) are painted above. */
  isolation: isolate;
}
.lean-tex-math { position: relative; z-index: 1; }
.lean-tex-line { padding: 2px 0; }
.lean-tex-line p { margin: 0; }
.lean-tex-line.lean-tex-target-line {
  margin-top: 4px;
  padding-top: 6px;
  border-top: 1px solid var(--lt-hairline);
}

/* Highlights, drawn behind the formula. */
.lean-tex-box { position: absolute; pointer-events: none; z-index: 0; border-radius: 5px; }
.lean-tex-hover {
  --lt-hl: var(--lt-fg);
  background: color-mix(in srgb, var(--lt-hl) 9%, transparent);
  box-shadow: inset 0 0 0 1px color-mix(in srgb, var(--lt-hl) 24%, transparent);
  transition: left .16s var(--lt-ease), top .16s var(--lt-ease), width .16s var(--lt-ease),
    height .16s var(--lt-ease), opacity .14s ease, background-color .14s ease, box-shadow .14s ease;
}
.lean-tex-hover.lean-tex-colored {
  background: color-mix(in srgb, var(--lt-hl) 15%, transparent);
  box-shadow: inset 0 0 0 1px color-mix(in srgb, var(--lt-hl) 50%, transparent);
}
.lean-tex-hover[data-instant] { transition: opacity .14s ease; }
.lean-tex-occurrence {
  --lt-hl: var(--lt-accent);
  border-radius: 4px 4px 2px 2px;
  background: color-mix(in srgb, var(--lt-hl) 11%, transparent);
  box-shadow: inset 0 -2px 0 color-mix(in srgb, var(--lt-hl) 70%, transparent);
  animation: lean-tex-fade .16s ease;
}
.lean-tex-selected {
  background: color-mix(in srgb, var(--lt-accent) 20%, transparent);
  box-shadow: inset 0 0 0 1.5px color-mix(in srgb, var(--lt-accent) 80%, transparent);
}
.lean-tex-underline { background: var(--lt-link); border-radius: 1px; }
${Array.from({ length: MAX_COLORS }, (_, i) => `.lean-var-${i} { fill: var(--lean-var-${i}); color: var(--lean-var-${i}); }`).join('\n')}

/* Toolbar */
.lean-tex-toolbar {
  position: absolute; top: 0; right: 0; z-index: 2;
  display: flex; gap: 2px;
  opacity: 0; transition: opacity .15s ease;
}
.lean-tex-display:hover > .lean-tex > .lean-tex-toolbar,
.lean-tex-toolbar:focus-within { opacity: 1; }
.lean-tex-icon-button {
  all: unset; box-sizing: border-box; cursor: pointer;
  display: inline-flex; align-items: center; justify-content: center;
  width: 22px; height: 22px; border-radius: 5px;
  color: var(--lt-fg); opacity: .6;
  transition: opacity .12s ease, background-color .12s ease;
}
.lean-tex-icon-button:hover { opacity: 1; background: color-mix(in srgb, var(--lt-fg) 10%, transparent); }
.lean-tex-icon-button:focus-visible { outline: 1px solid var(--lt-accent); }

/* Tooltips */
.lean-tex-tooltip {
  --lt-fg: var(--vscode-editorHoverWidget-foreground, var(--vscode-editor-foreground, currentColor));
  --lt-tip-bg: var(--vscode-editorHoverWidget-background, var(--vscode-editor-background, Canvas));
  --lt-tip-border: var(--vscode-editorHoverWidget-border, color-mix(in srgb, var(--lt-fg) 20%, transparent));
  --lt-ease: cubic-bezier(.2, .8, .2, 1);
  position: absolute; box-sizing: border-box;
  display: flex; flex-direction: column;
  width: max-content; max-width: min(34rem, calc(100vw - 20px));
  color: var(--lt-fg);
  /* Opaque even if the theme's hover background is translucent. */
  background: linear-gradient(var(--lt-tip-bg), var(--lt-tip-bg)), var(--vscode-editor-background, Canvas);
  border: 1px solid var(--lt-tip-border);
  border-radius: 8px;
  box-shadow: 0 12px 32px -8px rgba(0, 0, 0, .45), 0 3px 8px -2px rgba(0, 0, 0, .25);
  animation: lean-tex-pop .16s var(--lt-ease);
}
.lean-tex-tooltip[data-placement="top"] { --lt-dy: 4px; }
.lean-tex-tooltip[data-placement="bottom"] { --lt-dy: -4px; }
.lean-tex-tooltip-arrow {
  position: absolute; width: 9px; height: 9px;
  background: linear-gradient(var(--lt-tip-bg), var(--lt-tip-bg)), var(--vscode-editor-background, Canvas);
  border: 1px solid var(--lt-tip-border);
  transform: rotate(45deg);
}
.lean-tex-tooltip[data-placement="top"] > .lean-tex-tooltip-arrow { bottom: -6px; border-top: none; border-left: none; }
.lean-tex-tooltip[data-placement="bottom"] > .lean-tex-tooltip-arrow { top: -6px; border-bottom: none; border-right: none; }
.lean-tex-tooltip-content {
  position: relative; min-height: 0;
  padding: 6px 10px; overflow-y: auto; overscroll-behavior: contain;
}
.lean-tex-popup-head { display: flex; align-items: flex-start; gap: 10px; }
.lean-tex-popup-main { flex: 1; min-width: 0; overflow-x: auto; }
.lean-tex-popup-tools {
  flex: none; display: flex; align-items: center; gap: 2px; margin-top: 2px;
  opacity: .45; transition: opacity .15s ease;
}
.lean-tex-tooltip-content:hover > * > .lean-tex-popup-head > .lean-tex-popup-tools,
.lean-tex-popup-tools:focus-within { opacity: 1; }
.lean-tex-popup-doc {
  margin-top: 6px; padding-top: 6px;
  border-top: 1px solid color-mix(in srgb, var(--lt-fg) 14%, transparent);
}
.lean-tex-popup-doc p:first-child { margin-top: 0; }
.lean-tex-popup-doc p:last-child { margin-bottom: 0; }
.lean-tex-muted { opacity: .6; }
.lean-tex-segmented {
  display: inline-flex; padding: 1px; border-radius: 6px;
  background: color-mix(in srgb, var(--lt-fg) 9%, transparent);
  font-size: 10px; line-height: 16px; letter-spacing: .03em;
}
.lean-tex-segmented button {
  all: unset; cursor: pointer; padding: 0 6px; border-radius: 5px; opacity: .6;
  transition: opacity .12s ease, background-color .12s ease;
}
.lean-tex-segmented button:hover { opacity: .9; }
.lean-tex-segmented button[aria-pressed="true"] {
  opacity: 1;
  background: var(--lt-tip-bg, var(--vscode-editor-background, Canvas));
  box-shadow: 0 1px 2px rgba(0, 0, 0, .25);
}

/* Selection list */
.lean-tex-selection { margin-top: 8px; padding-top: 6px; border-top: 1px solid var(--lt-hairline); }
.lean-tex-selection-head {
  display: flex; align-items: center; gap: 8px;
  font-size: 0.85em; letter-spacing: .04em; text-transform: uppercase;
}
.lean-tex-selection-head a { text-transform: none; letter-spacing: normal; }
.lean-tex-selection-item {
  display: flex; align-items: baseline; gap: 10px;
  margin-top: 4px; padding: 2px 8px; border-radius: 6px;
  border-left: 2px solid var(--lt-accent);
  background: color-mix(in srgb, var(--lt-accent) 7%, transparent);
}
.lean-tex-selection-label { flex: none; font-size: 0.85em; opacity: .65; }

@keyframes lean-tex-fade { from { opacity: 0; } }
@keyframes lean-tex-pop { from { opacity: 0; transform: translateY(var(--lt-dy, 0)) scale(.985); } }
@media (prefers-reduced-motion: reduce) {
  .lean-tex-hover, .lean-tex-occurrence, .lean-tex-tooltip { transition: none; animation: none; }
}
`

/** Adds the styles to the document. They are global, since tooltips are appended to the body. */
function ensureStyles() {
  const id = 'leantex-latex-display-styles'
  let el = document.getElementById(id)
  if (!el) {
    el = document.createElement('style')
    el.id = id
    document.head.appendChild(el)
  }
  if (el.textContent !== STYLE) el.textContent = STYLE
}

// ---------------------------------------------------------------------------------------------
// Preferences

/** Whether hovers show the expression and its type in LaTeX or in Lean syntax. Shared by all
 * hovers and remembered across sessions when possible. */
type PopupMode = 'tex' | 'lean'
const MODE_KEY = 'leantex.popupMode'
let popupMode: PopupMode = (() => {
  try {
    return window.localStorage.getItem(MODE_KEY) === 'lean' ? 'lean' : 'tex'
  } catch {
    return 'tex'
  }
})()
const popupModeListeners = new Set<(m: PopupMode) => void>()

function usePopupMode(): [PopupMode, (m: PopupMode) => void] {
  const [mode, setModeState] = React.useState(popupMode)
  React.useEffect(() => {
    popupModeListeners.add(setModeState)
    return () => {
      popupModeListeners.delete(setModeState)
    }
  }, [])
  const setMode = React.useCallback((m: PopupMode) => {
    popupMode = m
    try {
      window.localStorage.setItem(MODE_KEY, m)
    } catch {
      // Storage may be unavailable; the preference then lasts for this session.
    }
    popupModeListeners.forEach(l => l(m))
  }, [])
  return [mode, setMode]
}

// ---------------------------------------------------------------------------------------------
// Building the LaTeX

/** A tagged subexpression. */
interface Tag {
  id: number
  info: LatexTag
  part: LatexPart
  /** The goal location, if the subexpression is part of a goal. */
  loc?: GoalsLocation
  /** Identifies the subexpression for selection. Like the goal view, we identify subexpressions
   * of goals by their location, so that the selection survives updates of the display. */
  key: string
  /** For variables, the index of the color in the palette. */
  color?: number
}

/** The LaTeX for a formula, with its tags. */
interface Built {
  /** The MathJax source of each line. */
  sources: string[]
  /** Whether each line shows the target of a goal. */
  targetLines: boolean[]
  /** The LaTeX without tags. */
  plain: string
  tags: Tag[]
}

/** The location of a subexpression at `pos` in the given part, if the part is in a goal. */
function partLocation(part: LatexPart, pos: string, mvarId: string | undefined): GoalsLocation | undefined {
  if (mvarId === undefined) return undefined
  let loc: GoalLocation
  switch (part.kind) {
    case 'hyp':
      if (part.fvarId == null) return undefined
      loc = { hyp: part.fvarId }
      break
    case 'hypType':
      if (part.fvarId == null) return undefined
      loc = { hypType: [part.fvarId, pos] }
      break
    case 'hypValue':
      if (part.fvarId == null) return undefined
      loc = { hypValue: [part.fvarId, pos] }
      break
    case 'target':
      loc = { target: pos }
      break
    default:
      return undefined
  }
  return { mvarId, loc }
}

/** The LaTeX without tags. */
function stripTags(tt: LatexCode): string {
  if ('text' in tt) return tt.text
  if ('append' in tt) return tt.append.map(stripTags).join('')
  return stripTags(tt.tag[1])
}

/** Builds the MathJax source for each line, assigning ids to tagged subexpressions.
 * Subexpressions are identified by their part and position, since the server may tag
 * several pieces of LaTeX with the same subexpression (for example the base and subscript of
 * `x_i` when a superscript is added). Variables are assigned colors from `vc`. */
function buildLatex(lines: LatexPart[][], mvarId: string | undefined, vc: VarColors): Built {
  const tags: Tag[] = []
  const plainLines: string[] = []
  const sources = lines.map((line, li) => {
    let plainLine = ''
    const tex = line
      .map((part, pi) => {
        const ids = new Map<string, number>()
        const go = (tt: LatexCode): string => {
          if ('text' in tt) {
            plainLine += tt.text
            return tt.text
          }
          if ('append' in tt) return tt.append.map(go).join('')
          const [info, sub] = tt.tag
          const pos = info.subexprPos ?? '/'
          // A binder's name is tagged with the binder's position, like the binder itself.
          const idKey = (info.binder ? 'b' : '') + pos
          let id = ids.get(idKey)
          if (id === undefined) {
            id = tags.length
            ids.set(idKey, id)
            const loc = info.binder ? undefined : partLocation(part, pos, mvarId)
            const key = loc ? JSON.stringify(loc) : `${li}/${pi}/${idKey}`
            const color = info.fvarId != null ? varColorIndex(vc, info.fvarId) : undefined
            tags.push({ id, info, part, loc, key, color })
          }
          const color = tags[id].color
          const inner = color !== undefined ? `\\class{lean-var-${color}}{${go(sub)}}` : go(sub)
          return `\\class{lean-se-${id}}{${inner}}`
        }
        return go(part.latex)
      })
      .join('')
    plainLines.push(plainLine)
    return `$\\displaystyle ${tex}$`
  })
  return {
    sources,
    targetLines: lines.map((line, i) => i > 0 && line.some(p => p.kind === 'target')),
    plain: plainLines.join('\n'),
    tags,
  }
}

/** A short human-readable description of where a subexpression is. */
function tagLabel(tag: Tag): string {
  const { part } = tag
  const pos = tag.info.subexprPos ?? '/'
  if (tag.info.binder) return 'bound variable'
  switch (part.kind) {
    case 'hyp':
      return 'hypothesis'
    case 'hypType':
      return `${part.name} : ${pos}`
    case 'hypValue':
      return `${part.name} := ${pos}`
    case 'target':
      return `⊢ ${pos}`
    default:
      return pos
  }
}

// ---------------------------------------------------------------------------------------------
// Geometry

function samePosition(p: DocumentPosition, q: DocumentPosition): boolean {
  return p.uri === q.uri && p.line === q.line && p.character === q.character
}

function isAnyTextSelected(): boolean {
  const s = window.getSelection()
  return s !== null && !s.isCollapsed
}

function isModifierHeld(e: React.MouseEvent): boolean {
  return e.altKey || e.ctrlKey || e.shiftKey || e.metaKey
}

/** The elements showing the subexpression with the given id. We only look inside the SVG, in case
 * MathJax also outputs (hidden) assistive MathML with the same classes. */
function tagElements(root: Element | null, id: number): Element[] {
  return root ? [...root.querySelectorAll(`svg .lean-se-${id}`)] : []
}

/** Finds the id of the innermost tagged subexpression at the given point.
 *
 * We use bounding boxes rather than the event target: in SVG only the glyphs themselves receive
 * pointer events, so the target is often the `<svg>` when the pointer is between glyphs.
 * The innermost subexpression is the one with the smallest box; for equal boxes, the later
 * element in document order (a descendant comes after its ancestors). */
function tagIdAt(x: number, y: number, root: Element | null): number | undefined {
  if (!root) return undefined
  let best: number | undefined
  let bestArea = Infinity
  root.querySelectorAll('svg [class*="lean-se-"]').forEach(el => {
    const r = el.getBoundingClientRect()
    if (x < r.left || x > r.right || y < r.top || y > r.bottom) return
    const area = r.width * r.height
    if (area <= bestArea) {
      const m = /(?:^|\s)lean-se-(\d+)(?:\s|$)/.exec(el.getAttribute('class') ?? '')
      if (m) {
        best = parseInt(m[1])
        bestArea = area
      }
    }
  })
  return best
}

/** Whether the subexpression `outer` contains the subexpression `inner` (or is it). */
function tagContains(root: Element | null, outer: number, inner: number): boolean {
  if (outer === inner) return true
  const inners = tagElements(root, inner)
  return tagElements(root, outer).some(o => inners.some(i => o.contains(i)))
}

interface Rect {
  left: number
  top: number
  right: number
  bottom: number
}

/** The bounding box of the subexpression with the given id, in viewport coordinates. */
function tagRect(root: Element | null, id: number): Rect | undefined {
  const els = tagElements(root, id)
  if (els.length === 0) return undefined
  const rs = els.map(el => el.getBoundingClientRect())
  return {
    left: Math.min(...rs.map(r => r.left)),
    top: Math.min(...rs.map(r => r.top)),
    right: Math.max(...rs.map(r => r.right)),
    bottom: Math.max(...rs.map(r => r.bottom)),
  }
}

/** A box relative to an element. */
interface Box {
  left: number
  top: number
  width: number
  height: number
}

/** The box of the subexpression with the given id relative to `origin`, padded a little. */
function tagBox(origin: Element, math: Element | null, id: number, padX = 2, padY = 1): Box | undefined {
  const r = tagRect(math, id)
  if (!r) return undefined
  const o = origin.getBoundingClientRect()
  return {
    left: r.left - o.left - padX,
    top: r.top - o.top - padY,
    width: r.right - r.left + 2 * padX,
    height: r.bottom - r.top + 2 * padY,
  }
}

// ---------------------------------------------------------------------------------------------
// Tooltips

/** Marks pointer events inside tooltips with the formulas owning the tooltips, so that a formula's
 * click-outside handler can ignore clicks inside its own tooltips. React events propagate along the
 * React tree, so a click in a nested tooltip is marked with the owners of all enclosing tooltips,
 * and also tooltips that the infoview opens from within ours (which are portals) are covered. */
function markInsideTooltip(e: React.PointerEvent, owner: string) {
  const ev = e.nativeEvent as any
  ;(ev._leanTexTooltipOwners ??= []).push(owner)
}

function tooltipOwners(e: PointerEvent): string[] {
  return (e as any)._leanTexTooltipOwners ?? []
}

interface TooltipLayout {
  left: number
  top: number
  maxHeight: number
  placement: 'top' | 'bottom'
  arrowX: number
}

/** A tooltip like the infoview's: appended to the document body, placed above or below the anchor
 * (whichever has more space), with an arrow and a maximum height of 300px. Tooltips are painted in
 * the order they are opened, so nested tooltips are above their parents. */
function Tooltip(props: {
  owner: string
  anchor: () => Rect | undefined
  children: React.ReactNode
  onPointerEnter?: () => void
  onPointerLeave?: () => void
  onClick?: () => void
}) {
  const ref = React.useRef<HTMLDivElement>(null)
  const contentRef = React.useRef<HTMLDivElement>(null)
  const anchorRef = React.useRef(props.anchor)
  anchorRef.current = props.anchor
  const [layout, setLayout] = React.useState<TooltipLayout>()

  const update = React.useCallback(() => {
    const a = anchorRef.current()
    const t = ref.current
    if (!a || !t || !contentRef.current) return
    const offset = 9
    const padding = 10
    const vw = document.documentElement.clientWidth
    const vh = window.innerHeight
    const spaceAbove = a.top - offset - padding
    const spaceBelow = vh - a.bottom - offset - padding
    const placement = spaceAbove > spaceBelow ? 'top' : 'bottom'
    const maxHeight = Math.max(0, Math.min(300, placement === 'top' ? spaceAbove : spaceBelow))
    const height = Math.min(contentRef.current.scrollHeight + 2, maxHeight)
    const width = t.offsetWidth
    const center = (a.left + a.right) / 2
    const left = Math.max(padding, Math.min(center - width / 2, vw - padding - width))
    const top = placement === 'top' ? a.top - offset - height : a.bottom + offset
    const arrowX = Math.max(12, Math.min(center - left, width - 12))
    const newLayout = { left: left + window.scrollX, top: top + window.scrollY, maxHeight, placement, arrowX } as const
    setLayout(old => (JSON.stringify(old) === JSON.stringify(newLayout) ? old : newLayout))
  }, [])

  React.useLayoutEffect(update)
  React.useEffect(() => {
    window.addEventListener('scroll', update, true)
    window.addEventListener('resize', update)
    const obs = typeof ResizeObserver !== 'undefined' ? new ResizeObserver(update) : undefined
    if (contentRef.current) obs?.observe(contentRef.current)
    return () => {
      window.removeEventListener('scroll', update, true)
      window.removeEventListener('resize', update)
      obs?.disconnect()
    }
  }, [update])

  const tooltip = (
    <div
      ref={ref}
      className="lean-tex-tooltip"
      data-placement={layout?.placement}
      style={{
        left: layout?.left ?? 0,
        top: layout?.top ?? 0,
        maxHeight: layout?.maxHeight,
        visibility: layout ? 'visible' : 'hidden',
      }}
      onPointerDownCapture={e => markInsideTooltip(e, props.owner)}
      onPointerEnter={props.onPointerEnter}
      onPointerLeave={props.onPointerLeave}
      onClick={props.onClick}
    >
      {layout && <div className="lean-tex-tooltip-arrow" style={{ left: layout.arrowX - 5 }} />}
      <div ref={contentRef} className="lean-tex-tooltip-content">
        {props.children}
      </div>
    </div>
  )
  return ReactDOM.createPortal(tooltip, document.body)
}

/** Like the infoview's `TypePopupContents`: the subexpression and its type, then its docstring. */
function LeanPopupContents({ info, withDoc }: { info: InfoRef; withDoc?: boolean }) {
  const rs = useRpcSession()
  const popup = useAsync<InfoPopup>(() => InteractiveDiagnostics_infoToInteractive(rs, info), [rs, info])
  return popup.state === 'resolved' ? (
    <>
      <div className="font-code tl pre-wrap">
        {popup.value.exprExplicit && <InteractiveCode fmt={popup.value.exprExplicit} />} :{' '}
        {popup.value.type && <InteractiveCode fmt={popup.value.type} />}
      </div>
      {withDoc && popup.value.doc && (
        <div className="lean-tex-popup-doc">
          <Markdown contents={popup.value.doc} />
        </div>
      )}
    </>
  ) : popup.state === 'rejected' ? (
    <span className="lean-tex-muted">Error: {mapRpcError(popup.error).message}</span>
  ) : (
    <span className="lean-tex-muted">Loading…</span>
  )
}

/** Fetches the hover contents for a subexpression, with the expression and its type in LaTeX. */
function useLatexPopup(info: InfoRef) {
  const rs = useRpcSession()
  return useAsync<LatexPopup>(() => rs.call<InfoRef, LatexPopup>('LeanTeX.LatexDisplay.popup', info), [rs, info])
}

/** A formula built from LaTeX code from the server, using the variable colors in context. */
function useBuiltFormula(lines: LatexPart[][] | undefined): Built | undefined {
  const vc = React.useContext(VarColorsContext)
  return React.useMemo(() => (lines ? buildLatex(lines, undefined, vc) : undefined), [lines, vc])
}

/** The hover for a subexpression: the subexpression and its type, rendered in LaTeX and
 * interactive (so that hovers nest), or in Lean syntax; then its docstring. */
function PopupContents({ info, depth }: { info: InfoRef; depth: number }) {
  const [mode, setMode] = usePopupMode()
  const popup = useLatexPopup(info)
  const value = popup.state === 'resolved' ? popup.value : undefined
  const lines = React.useMemo<LatexPart[][] | undefined>(
    () =>
      value && [
        [
          { latex: value.expr, kind: 'expr' },
          ...(value.type
            ? ([
                { latex: { text: ' : ' }, kind: 'text' },
                { latex: value.type, kind: 'expr' },
              ] as LatexPart[])
            : []),
        ],
      ],
    [value],
  )
  const built = useBuiltFormula(lines)
  const ec = React.useContext(EditorContext)
  // If the server cannot render LaTeX (for example an older LeanTeX), show Lean syntax.
  const showLean = mode === 'lean' || popup.state === 'rejected'

  return (
    <div className="tooltip-code-content">
      <div className="lean-tex-popup-head">
        <div className="lean-tex-popup-main">
          {showLean ? (
            <LeanPopupContents info={info} withDoc={popup.state === 'rejected'} />
          ) : built ? (
            <InteractiveLatex built={built} depth={depth} />
          ) : (
            <span className="lean-tex-muted">Loading…</span>
          )}
        </div>
        <div className="lean-tex-popup-tools">
          {value && !showLean && (
            <button
              className="lean-tex-icon-button codicon codicon-copy"
              title="Copy LaTeX"
              onClick={e => {
                e.stopPropagation()
                void ec.api.copyToClipboard(stripTags(value.expr))
              }}
            />
          )}
          <div className="lean-tex-segmented" role="group" aria-label="Notation">
            <button aria-pressed={mode === 'tex'} title="Show in LaTeX" onClick={() => setMode('tex')}>
              TeX
            </button>
            <button aria-pressed={mode === 'lean'} title="Show in Lean syntax" onClick={() => setMode('lean')}>
              Lean
            </button>
          </div>
        </div>
      </div>
      {value?.doc && (
        <div className="lean-tex-popup-doc">
          <Markdown contents={value.doc} />
        </div>
      )}
    </div>
  )
}

// ---------------------------------------------------------------------------------------------
// The interactive formula

/** One rendered line. Memoized so that MathJax does not re-render when the highlight changes. */
const MathLine = React.memo(function MathLine({ source, target }: { source: string; target: boolean }) {
  return (
    <div className={target ? 'lean-tex-line lean-tex-target-line' : 'lean-tex-line'}>
      <Markdown contents={source} />
    </div>
  )
})

const SHOW_DELAY = 500
const HIDE_DELAY = 300

/** Selection state, owned by `LatexDisplay`. */
interface Selection {
  selected: string[]
  setKeySelected: (key: string, act: boolean | ((wasSelected: boolean) => boolean)) => void
}

/** A location in a document, as returned by go-to-definition. */
interface DocLocation {
  uri: string
  range: { start: { line: number; character: number } }
}

interface HoverBox extends Box {
  color?: string
  visible: boolean
  /** Whether to move without animation (when appearing). */
  instant: boolean
}

/** A formula with interactive subexpressions. Used for the display itself and, recursively,
 * for the hovers of its subexpressions (`depth > 0`), which have no selection or context menu. */
function InteractiveLatex(props: {
  built: Built
  depth: number
  selection?: Selection
  /** Prefix for context menu ids; enables the context menu. */
  contextMenuId?: string
  toolbar?: React.ReactNode
}) {
  const { built, depth, selection, contextMenuId, toolbar } = props
  const { sources, targetLines, tags } = built
  const ec = React.useContext(EditorContext)
  const rs = useRpcSession()
  const vc = React.useContext(VarColorsContext)
  const rootRef = React.useRef<HTMLDivElement>(null)
  const mathRef = React.useRef<HTMLDivElement>(null)
  const owner = React.useId()
  const selected = selection?.selected ?? []

  // The hovered subexpression, and whether Ctrl/⌘ is held.
  const [hover, setHover] = React.useState<{ id: number; ctrl: boolean } | undefined>()
  // Open tooltips. At most one is unpinned (shown because of hovering).
  const [tips, setTips] = React.useState<{ id: number; pinned: boolean }[]>([])
  // The subexpression for which to show "No definition found".
  const [noDefTip, setNoDefTip] = React.useState<number | undefined>()
  // Go-to-definition targets (`null` if there is none).
  const goTo = React.useRef(new Map<number, DocLocation | null>())
  const [, setGoToVersion] = React.useState(0)

  // Ids refer to different subexpressions when the contents change.
  React.useEffect(() => {
    setHover(undefined)
    setTips([])
    setNoDefTip(undefined)
    goTo.current = new Map()
  }, [tags])

  // Latest values, for callbacks registered with event emitters and timers.
  const latest = React.useRef({ tags, rs, ec })
  latest.current = { tags, rs, ec }

  const fetchGoTo = React.useCallback(async (id: number): Promise<DocLocation | undefined> => {
    const cached = goTo.current.get(id)
    if (cached !== undefined) return cached ?? undefined
    const { tags, rs } = latest.current
    const tag = tags[id]
    if (!tag) return undefined
    let loc: DocLocation | null = null
    try {
      const links = await getGoToLocation(rs, 'definition', tag.info.info)
      if (links.length > 0) loc = { uri: links[0].targetUri, range: links[0].targetSelectionRange }
    } catch (e) {
      console.error('Error in go-to-definition: ', JSON.stringify(e))
    }
    goTo.current.set(id, loc)
    setGoToVersion(v => v + 1)
    return loc ?? undefined
  }, [])

  const execGoTo = React.useCallback(
    async (id: number, withError: boolean) => {
      const loc = await fetchGoTo(id)
      if (loc === undefined) {
        if (withError) setNoDefTip(id)
        return
      }
      await latest.current.ec.revealPosition({ uri: loc.uri, ...loc.range.start })
    },
    [fetchGoTo],
  )

  // Fetch the go-to-definition target eagerly on Ctrl-hover, so that we can underline.
  React.useEffect(() => {
    if (hover?.ctrl) void fetchGoTo(hover.id)
  }, [hover, fetchGoTo])

  // Track Ctrl/⌘ while hovering.
  const hovering = hover !== undefined
  React.useEffect(() => {
    if (!hovering) return
    const onKey = (ctrl: boolean) => (e: KeyboardEvent) => {
      if (e.key === 'Control' || e.key === 'Meta') setHover(h => h && { ...h, ctrl })
    }
    const down = onKey(true)
    const up = onKey(false)
    document.addEventListener('keydown', down)
    document.addEventListener('keyup', up)
    return () => {
      document.removeEventListener('keydown', down)
      document.removeEventListener('keyup', up)
    }
  }, [hovering])

  // Tooltip timers, as in the infoview's `useHoverTooltip`.
  const showTimer = React.useRef<number>()
  const hideTimer = React.useRef<number>()
  const pointerOverTooltip = React.useRef(false)
  React.useEffect(
    () => () => {
      window.clearTimeout(showTimer.current)
      window.clearTimeout(hideTimer.current)
    },
    [],
  )
  const startShowTimeout = (id: number) => {
    window.clearTimeout(showTimer.current)
    showTimer.current = window.setTimeout(() => {
      if (isAnyTextSelected()) return
      setTips(ts => (ts.some(t => t.id === id) ? ts : [...ts.filter(t => t.pinned), { id, pinned: false }]))
    }, SHOW_DELAY)
  }
  const startHideTimeout = () => {
    window.clearTimeout(hideTimer.current)
    hideTimer.current = window.setTimeout(() => {
      if (!pointerOverTooltip.current) setTips(ts => ts.filter(t => t.pinned))
    }, HIDE_DELAY)
  }

  const onPointerMove = (e: React.PointerEvent) => {
    const id = tagIdAt(e.clientX, e.clientY, mathRef.current)
    const ctrl = e.ctrlKey || e.metaKey
    if (id === hover?.id) {
      if (hover && ctrl !== hover.ctrl) setHover({ id: hover.id, ctrl })
      return
    }
    setHover(id === undefined ? undefined : { id, ctrl })
    window.clearTimeout(showTimer.current)
    startHideTimeout()
    if (id !== undefined && !isModifierHeld(e)) startShowTimeout(id)
  }
  const onPointerLeave = () => {
    setHover(undefined)
    window.clearTimeout(showTimer.current)
    startHideTimeout()
  }
  const onPointerDown = (e: React.PointerEvent) => {
    // We have special handling for modifier+click, so prevent the browser's (e.g. text selection).
    if (isModifierHeld(e) && tagIdAt(e.clientX, e.clientY, mathRef.current) !== undefined) e.preventDefault()
  }
  const onMouseDown = (e: React.MouseEvent) => {
    // Prevent double-click text selection.
    if (e.detail > 1) e.preventDefault()
  }
  const onClick = (e: React.MouseEvent) => {
    const id = tagIdAt(e.clientX, e.clientY, mathRef.current)
    if (id === undefined) return
    if (e.ctrlKey || e.metaKey) {
      setHover({ id, ctrl: true })
      void execGoTo(id, false)
      return
    }
    if (e.shiftKey) {
      selection?.setKeySelected(tags[id].key, on => !on)
      e.preventDefault()
      return
    }
    if (isAnyTextSelected()) return
    window.clearTimeout(showTimer.current)
    window.clearTimeout(hideTimer.current)
    setTips(ts => {
      const t = ts.find(t => t.id === id)
      if (t?.pinned) return ts.filter(t => t.id !== id)
      return [...ts.filter(t => t.id !== id && t.pinned), { id, pinned: true }]
    })
  }

  // Clicking outside a subexpression closes its tooltips.
  const anyTooltip = tips.length > 0 || noDefTip !== undefined
  React.useEffect(() => {
    if (!anyTooltip) return
    const onPointerDownAnywhere = (e: PointerEvent) => {
      if (tooltipOwners(e).includes(owner)) return
      // The user might be clicking a scrollbar.
      if (e.target instanceof Element && e.target.tagName === 'HTML') return
      setNoDefTip(undefined)
      const math = mathRef.current
      const id =
        math && e.target instanceof Node && math.contains(e.target) ? tagIdAt(e.clientX, e.clientY, math) : undefined
      setTips(ts => ts.filter(t => id !== undefined && tagContains(math, t.id, id)))
    }
    document.addEventListener('pointerdown', onPointerDownAnywhere)
    return () => document.removeEventListener('pointerdown', onPointerDownAnywhere)
  }, [anyTooltip, owner])

  // Context menu: VS Code reads `data-vscode-context` from the clicked element and its ancestors,
  // so we set it on the formula for the subexpression under the pointer.
  const onContextMenu = (e: React.MouseEvent<HTMLDivElement>) => {
    if (contextMenuId === undefined) return
    const id = tagIdAt(e.clientX, e.clientY, mathRef.current)
    const context: Record<string, string> = { interactiveCodeTagId: '', selectableLocationId: '', unselectableLocationId: '' }
    if (id !== undefined) {
      const key = tags[id].key
      context.interactiveCodeTagId = `${contextMenuId}|${id}`
      if (selection) {
        if (selected.includes(key)) context.unselectableLocationId = `${contextMenuId}|${key}`
        else context.selectableLocationId = `${contextMenuId}|${key}`
      }
    }
    e.currentTarget.setAttribute('data-vscode-context', JSON.stringify(context))
    setTips([])
  }
  const setKeySelected = selection?.setKeySelected
  React.useEffect(() => {
    if (contextMenuId === undefined) return
    const h = ec.events.clickedContextMenu.on(action => {
      const sep = action.id.indexOf('|')
      if (sep < 0 || action.id.slice(0, sep) !== contextMenuId) return
      const arg = action.id.slice(sep + 1)
      if (action.entry === 'goToDefinition') void execGoTo(parseInt(arg), true)
      else if (action.entry === 'select') setKeySelected?.(arg, true)
      else if (action.entry === 'unselect') setKeySelected?.(arg, false)
    })
    return () => h.dispose()
  }, [ec, contextMenuId, execGoTo, setKeySelected])

  // Highlights, recomputed when the highlighted subexpressions or the layout change.
  const selectedIds = tags.filter(t => selected.includes(t.key)).map(t => t.id)
  const underline = hover !== undefined && hover.ctrl && !!goTo.current.get(hover.id)
  const [hoverBox, setHoverBox] = React.useState<HoverBox>()
  const [boxes, setBoxes] = React.useState<{ key: string; className: string; box: Box; color?: string }[]>([])
  const [layoutVersion, setLayoutVersion] = React.useState(0)
  React.useEffect(() => {
    const root = rootRef.current
    if (!root || typeof ResizeObserver === 'undefined') return
    const obs = new ResizeObserver(() => setLayoutVersion(v => v + 1))
    obs.observe(root)
    return () => obs.disconnect()
  }, [])
  const colorOf = (tag: Tag | undefined) => (tag?.color !== undefined ? vc.palette[tag.color] : undefined)
  const highlightKey = JSON.stringify([selectedIds, hover?.id, underline])
  React.useLayoutEffect(() => {
    const root = rootRef.current
    const math = mathRef.current
    if (!root) return
    const newBoxes: typeof boxes = []
    for (const id of selectedIds) {
      const box = tagBox(root, math, id)
      if (box) newBoxes.push({ key: `sel-${id}`, className: 'lean-tex-selected', box })
    }
    const hovered = hover !== undefined ? tags[hover.id] : undefined
    if (hovered) {
      // The other occurrences of the hovered subexpression.
      const color = colorOf(hovered)
      for (const t of tags) {
        if (t.id === hovered.id || t.info.key !== hovered.info.key) continue
        const box = tagBox(root, math, t.id)
        if (box) newBoxes.push({ key: `occ-${t.id}`, className: 'lean-tex-occurrence', box, color })
      }
      if (underline) {
        const r = tagBox(root, math, hovered.id, 0, 0)
        if (r) {
          newBoxes.push({
            key: `ul-${hovered.id}`,
            className: 'lean-tex-underline',
            box: { left: r.left, top: r.top + r.height - 1, width: r.width, height: 1.5 },
          })
        }
      }
      const box = tagBox(root, math, hovered.id)
      if (box) setHoverBox(prev => ({ ...box, color, visible: true, instant: !prev?.visible }))
    } else {
      setHoverBox(prev => prev && { ...prev, visible: false, instant: false })
    }
    setBoxes(newBoxes)
  }, [highlightKey, sources, layoutVersion])

  return (
    <div ref={rootRef} className="lean-tex" style={paletteStyle(vc)}>
      {hoverBox && (
        <div
          className={'lean-tex-box lean-tex-hover' + (hoverBox.color ? ' lean-tex-colored' : '')}
          data-instant={hoverBox.instant ? '' : undefined}
          style={{
            left: hoverBox.left,
            top: hoverBox.top,
            width: hoverBox.width,
            height: hoverBox.height,
            opacity: hoverBox.visible ? 1 : 0,
            ...(hoverBox.color ? ({ '--lt-hl': hoverBox.color } as React.CSSProperties) : {}),
          }}
        />
      )}
      {boxes.map(b => (
        <div
          key={b.key}
          className={'lean-tex-box ' + b.className}
          style={{
            ...b.box,
            ...(b.color ? ({ '--lt-hl': b.color } as React.CSSProperties) : {}),
          }}
        />
      ))}
      <div
        ref={mathRef}
        className="lean-tex-math"
        style={{ cursor: hover !== undefined ? 'pointer' : undefined }}
        onPointerMove={onPointerMove}
        onPointerLeave={onPointerLeave}
        onPointerDown={onPointerDown}
        onMouseDown={onMouseDown}
        onClick={onClick}
        onContextMenu={onContextMenu}
      >
        {sources.map((source, i) => (
          <MathLine key={i} source={source} target={targetLines[i]} />
        ))}
      </div>
      {toolbar && <div className="lean-tex-toolbar">{toolbar}</div>}
      {tips.map(
        t =>
          tags[t.id] && (
            <Tooltip
              key={t.id}
              owner={owner}
              anchor={() => tagRect(mathRef.current, t.id)}
              onPointerEnter={() => {
                pointerOverTooltip.current = true
                window.clearTimeout(hideTimer.current)
              }}
              onPointerLeave={() => {
                pointerOverTooltip.current = false
                startHideTimeout()
              }}
              // Interacting with a tooltip (e.g. pinning a tooltip inside it) pins it.
              onClick={() => setTips(ts => ts.map(u => (u.id === t.id ? { ...u, pinned: true } : u)))}
            >
              <PopupContents info={tags[t.id].info.info} depth={depth + 1} />
            </Tooltip>
          ),
      )}
      {noDefTip !== undefined && (
        <Tooltip owner={owner} anchor={() => tagRect(mathRef.current, noDefTip)} onClick={() => setNoDefTip(undefined)}>
          No definition found for this subexpression
        </Tooltip>
      )}
    </div>
  )
}

// ---------------------------------------------------------------------------------------------
// The display

/** A button that copies `text`, confirming with a check mark. */
function CopyButton({ text, title }: { text: string; title: string }) {
  const ec = React.useContext(EditorContext)
  const [copied, setCopied] = React.useState(false)
  React.useEffect(() => {
    if (!copied) return
    const t = window.setTimeout(() => setCopied(false), 1500)
    return () => window.clearTimeout(t)
  }, [copied])
  return (
    <button
      className={'lean-tex-icon-button codicon ' + (copied ? 'codicon-check' : 'codicon-copy')}
      title={copied ? 'Copied' : title}
      onClick={() => {
        void ec.api.copyToClipboard(text)
        setCopied(true)
      }}
    />
  )
}

/** A selected subexpression, in LaTeX (or Lean syntax, following the hover preference). */
function SelectedExpr({ tag }: { tag: Tag }) {
  const [mode] = usePopupMode()
  const popup = useLatexPopup(tag.info.info)
  const value = popup.state === 'resolved' ? popup.value : undefined
  const lines = React.useMemo<LatexPart[][] | undefined>(() => value && [[{ latex: value.expr, kind: 'expr' }]], [value])
  const built = useBuiltFormula(lines)
  return (
    <div className="lean-tex-selection-item" data-location={tag.loc ? JSON.stringify(tag.loc) : undefined}>
      <span className="lean-tex-selection-label font-code" title={tag.loc ? JSON.stringify(tag.loc) : undefined}>
        {tagLabel(tag)}
      </span>
      <div style={{ minWidth: 0, flex: 1 }}>
        {mode === 'lean' || popup.state === 'rejected' ? (
          <LeanExpr info={tag.info.info} />
        ) : built ? (
          <InteractiveLatex built={built} depth={1} />
        ) : (
          <span className="lean-tex-muted">…</span>
        )}
      </div>
    </div>
  )
}

/** A subexpression in Lean syntax. */
function LeanExpr({ info }: { info: InfoRef }) {
  const rs = useRpcSession()
  const popup = useAsync<InfoPopup>(() => InteractiveDiagnostics_infoToInteractive(rs, info), [rs, info])
  return (
    <span className="font-code pre-wrap">
      {popup.state === 'resolved' && popup.value.exprExplicit ? (
        <InteractiveCode fmt={popup.value.exprExplicit} />
      ) : popup.state === 'rejected' ? (
        `Error: ${mapRpcError(popup.error).message}`
      ) : (
        '…'
      )}
    </span>
  )
}

export default function LatexDisplay({ lines, mvarId, pos, colorVariables, variableColors }: LatexDisplayProps) {
  const ec = React.useContext(EditorContext)
  const colorsKey = JSON.stringify([colorVariables ?? true, variableColors ?? []])
  // New colors for new contents, so that variables are colored in order of appearance.
  const vc = React.useMemo(() => makeVarColors(colorVariables ?? true, variableColors ?? []), [colorsKey, lines])
  const built = React.useMemo(() => buildLatex(lines, mvarId, vc), [lines, mvarId, vc])
  const { plain, tags } = built
  // Prefix for the ids used in context menu actions.
  const uid = 'leantex' + React.useId().replace(/[^a-zA-Z0-9]/g, '')

  React.useLayoutEffect(ensureStyles, [])

  // Selection: keys of selected subexpressions. Like the goal view, the selection is cleared when
  // the cursor moves, and otherwise survives updates of the display.
  const [selected, setSelected] = React.useState<string[]>([])
  const [prevPos, setPrevPos] = React.useState(pos)
  if (!samePosition(pos, prevPos)) {
    setPrevPos(pos)
    setSelected([])
  }
  const setKeySelected = React.useCallback((key: string, act: boolean | ((wasSelected: boolean) => boolean)) => {
    setSelected(sel => {
      const wasSelected = sel.includes(key)
      const isSelected = typeof act === 'function' ? act(wasSelected) : act
      if (wasSelected === isSelected) return sel
      return isSelected ? [...sel, key] : sel.filter(k => k !== key)
    })
  }, [])
  const selection = React.useMemo(() => ({ selected, setKeySelected }), [selected, setKeySelected])

  React.useEffect(() => {
    const h = ec.events.clickedContextMenu.on(action => {
      if (action.entry === 'unselectAll' && action.id === uid) setSelected([])
    })
    return () => h.dispose()
  }, [ec, uid])

  const selectedTags = selected
    .map(key => tags.find(t => t.key === key))
    .filter((t): t is Tag => t !== undefined)

  return (
    <VarColorsContext.Provider value={vc}>
      <div
        className="lean-tex-display"
        data-vscode-context={JSON.stringify(selected.length > 0 ? { selectedLocationsId: uid } : {})}
        data-selected-locations={JSON.stringify(selectedTags.flatMap(t => (t.loc ? [t.loc] : [])))}
      >
        <InteractiveLatex
          built={built}
          depth={0}
          selection={selection}
          contextMenuId={uid}
          toolbar={<CopyButton text={plain} title="Copy LaTeX" />}
        />
        {selectedTags.length > 0 && (
          <div className="lean-tex-selection lean-tex">
            <div className="lean-tex-selection-head lean-tex-muted">
              <span>Selected</span>
              <span>·</span>
              <a className="link pointer" onClick={() => setSelected([])}>
                clear
              </a>
              <span style={{ textTransform: 'none', letterSpacing: 'normal' }}>(shift-click to toggle)</span>
            </div>
            {selectedTags.map(tag => (
              <SelectedExpr key={tag.key} tag={tag} />
            ))}
          </div>
        )}
      </div>
    </VarColorsContext.Provider>
  )
}
