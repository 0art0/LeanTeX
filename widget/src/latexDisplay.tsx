/**
 * Client side of `LeanTeX.LatexDisplay`: lines of LaTeX, rendered with the infoview's MathJax,
 * whose subexpressions can be interacted with like those of expressions in the goal view.
 *
 * The server sends each part of a line as `CodeWithInfos` whose leaves are LaTeX fragments.
 * We give each tagged subexpression an id `N` and wrap its LaTeX in `\class{lean-se-N}{...}`.
 * MathJax (SVG output) puts the class on the `<g>` element for the subexpression, which is how we
 * find subexpressions on the page. Since in SVG only glyphs receive pointer events, we find the
 * subexpression under the pointer using bounding boxes, and since `<g>` elements have no
 * background, highlights are boxes drawn behind the formula.
 *
 * The interactions follow the infoview's `InteractiveCode` (see `interactiveCode.tsx`,
 * `tooltips.tsx`, `hoverHighlight.tsx` and `goalLocation.tsx` in vscode-lean4):
 * - hovering highlights the innermost subexpression and shows its type and docstring after a delay;
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
  CodeWithInfos,
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

/** Mirrors `LeanTeX.LatexPart`. */
interface LatexPart {
  latex: CodeWithInfos
  kind: 'text' | 'expr' | 'hyp' | 'hypType' | 'hypValue' | 'target'
  fvarId?: string
  name?: string
}

/** Mirrors `LeanTeX.LatexDisplay.Props`. `pos` is added by ProofWidgets. */
interface LatexDisplayProps {
  lines: LatexPart[][]
  mvarId?: string
  pos: DocumentPosition
}

/** A tagged subexpression. */
interface Tag {
  id: number
  info: SubexprInfo
  part: LatexPart
  /** The goal location, if the subexpression is part of a goal. */
  loc?: GoalsLocation
  /** Identifies the subexpression for selection. Like the goal view, we identify subexpressions
   * of goals by their location, so that the selection survives updates of the display. */
  key: string
}

/** A location in a document, as returned by go-to-definition. */
interface DocLocation {
  uri: string
  range: { start: { line: number; character: number } }
}

/** The location of a subexpression at `pos` in the given part, if the part is in a goal. */
function partLocation(part: LatexPart, pos: string, mvarId: string | undefined): GoalsLocation | undefined {
  if (mvarId === undefined) return undefined
  let loc: GoalLocation
  switch (part.kind) {
    case 'hyp':
      if (part.fvarId === undefined) return undefined
      loc = { hyp: part.fvarId }
      break
    case 'hypType':
      if (part.fvarId === undefined) return undefined
      loc = { hypType: [part.fvarId, pos] }
      break
    case 'hypValue':
      if (part.fvarId === undefined) return undefined
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

/** Builds the MathJax source for each line, assigning ids to tagged subexpressions.
 * Subexpressions are identified by their part and position, since the server may tag
 * several pieces of LaTeX with the same subexpression (for example the base and subscript of
 * `x_i` when a superscript is added). Also returns the LaTeX without tags. */
function buildLatex(
  lines: LatexPart[][],
  mvarId: string | undefined,
): { sources: string[]; plain: string; tags: Tag[] } {
  const tags: Tag[] = []
  const plainLines: string[] = []
  const sources = lines.map((line, li) => {
    let plainLine = ''
    const tex = line
      .map((part, pi) => {
        const ids = new Map<string, number>()
        const go = (tt: TaggedText<SubexprInfo>): string => {
          if ('text' in tt) {
            plainLine += tt.text
            return tt.text
          }
          if ('append' in tt) return tt.append.map(go).join('')
          const [info, sub] = tt.tag
          const pos = info.subexprPos ?? '/'
          let id = ids.get(pos)
          if (id === undefined) {
            id = tags.length
            ids.set(pos, id)
            const loc = partLocation(part, pos, mvarId)
            const key = loc ? JSON.stringify(loc) : `${li}/${pi}/${pos}`
            tags.push({ id, info, part, loc, key })
          }
          return `\\class{lean-se-${id}}{${go(sub)}}`
        }
        return go(part.latex)
      })
      .join('')
    plainLines.push(plainLine)
    return `$\\displaystyle ${tex}$`
  })
  return { sources, plain: plainLines.join('\n'), tags }
}

/** A short human-readable description of where a subexpression is. */
function tagLabel(tag: Tag): string {
  const { part } = tag
  const pos = tag.info.subexprPos ?? '/'
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

/** The elements showing the subexpression with the given id. */
function tagElements(root: Element | null, id: number): Element[] {
  return root ? [...root.querySelectorAll(`.lean-se-${id}`)] : []
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
  root.querySelectorAll('[class*="lean-se-"]').forEach(el => {
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

interface Box {
  key: string
  left: number
  top: number
  width: number
  height: number
  className?: string
  underline?: boolean
}

/** Computes highlight boxes, relative to `root`, for the subexpressions with the given ids. */
function computeBoxes(root: HTMLElement, highlights: { id: number; className?: string; underline?: boolean }[]): Box[] {
  const rootRect = root.getBoundingClientRect()
  const boxes: Box[] = []
  for (const { id, className, underline } of highlights) {
    tagElements(root, id).forEach((el, i) => {
      const r = el.getBoundingClientRect()
      boxes.push({
        key: `${className}-${underline}-${id}-${i}`,
        left: r.left - rootRect.left,
        top: r.top - rootRect.top,
        width: r.width,
        height: r.height,
        className,
        underline,
      })
    })
  }
  return boxes
}

/** Marks pointer events inside tooltips, so that the click-outside handler can ignore them.
 * React events propagate along the React tree, so this also covers tooltips that the infoview
 * opens from within our tooltips (which are portals, so not DOM descendants). */
function markInsideTooltip(e: React.PointerEvent) {
  ;(e.nativeEvent as any)._leanTexInTooltip = true
}

interface TooltipLayout {
  left: number
  top: number
  maxHeight: number
  placement: 'top' | 'bottom'
  arrowX: number
}

/** A tooltip like the infoview's: appended to the document body, placed above or below the anchor
 * (whichever has more space), with an arrow and a maximum height of 300px. */
function Tooltip(props: {
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
    const offset = 8
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
    const arrowX = Math.max(10, Math.min(center - left, width - 10))
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
      className="tooltip"
      style={{
        position: 'absolute',
        left: layout?.left ?? 0,
        top: layout?.top ?? 0,
        maxHeight: layout?.maxHeight,
        visibility: layout ? 'visible' : 'hidden',
      }}
      onPointerDownCapture={markInsideTooltip}
      onPointerEnter={props.onPointerEnter}
      onPointerLeave={props.onPointerLeave}
      onClick={props.onClick}
    >
      {layout && (
        <svg
          width={14}
          height={7}
          style={{
            position: 'absolute',
            left: layout.arrowX - 7,
            ...(layout.placement === 'top' ? { bottom: -7 } : { top: -7, transform: 'rotate(180deg)' }),
          }}
        >
          <path
            d="M0,0 L7,7 L14,0"
            fill="var(--vscode-editorHoverWidget-background)"
            stroke="var(--vscode-editorHoverWidget-border)"
          />
        </svg>
      )}
      <div ref={contentRef} className="tooltip-content">
        {props.children}
      </div>
    </div>
  )
  return ReactDOM.createPortal(tooltip, document.body)
}

/** Like the infoview's `TypePopupContents`: the subexpression and its type, then its docstring. */
function TypePopupContents({ info }: { info: SubexprInfo }) {
  const rs = useRpcSession()
  const popup = useAsync<InfoPopup>(() => InteractiveDiagnostics_infoToInteractive(rs, info.info), [rs, info.info])
  return (
    <div className="tooltip-code-content">
      {popup.state === 'resolved' ? (
        <>
          <div className="font-code tl pre-wrap">
            {popup.value.exprExplicit && <InteractiveCode fmt={popup.value.exprExplicit} />} :{' '}
            {popup.value.type && <InteractiveCode fmt={popup.value.type} />}
          </div>
          {popup.value.doc && (
            <>
              <hr />
              <Markdown contents={popup.value.doc} />
            </>
          )}
        </>
      ) : popup.state === 'rejected' ? (
        <>Error: {mapRpcError(popup.error).message}</>
      ) : (
        <>Loading..</>
      )}
    </div>
  )
}

/** A selected subexpression, shown in Lean syntax. */
function SelectedExpr({ tag }: { tag: Tag }) {
  const rs = useRpcSession()
  const popup = useAsync<InfoPopup>(() => InteractiveDiagnostics_infoToInteractive(rs, tag.info.info), [rs, tag.info.info])
  return (
    <div className="font-code pre-wrap" data-location={tag.loc ? JSON.stringify(tag.loc) : undefined}>
      <span style={{ opacity: 0.7 }} title={tag.loc ? JSON.stringify(tag.loc) : undefined}>
        {tagLabel(tag)}
      </span>
      {': '}
      {popup.state === 'resolved' && popup.value.exprExplicit ? (
        <InteractiveCode fmt={popup.value.exprExplicit} />
      ) : popup.state === 'rejected' ? (
        `Error: ${mapRpcError(popup.error).message}`
      ) : (
        '...'
      )}
    </div>
  )
}

/** One rendered line. Memoized so that MathJax does not re-render when the highlight changes. */
const MathLine = React.memo(function MathLine({ source }: { source: string }) {
  return <Markdown contents={source} />
})

const SHOW_DELAY = 500
const HIDE_DELAY = 300

/** Styles that cannot be given inline. */
const STYLE = `
.lean-tex-display .lean-tex-copy { opacity: 0; transition: opacity 0.1s; }
.lean-tex-display:hover .lean-tex-copy { opacity: 0.6; }
.lean-tex-display .lean-tex-copy:hover { opacity: 1; }
`

export default function LatexDisplay({ lines, mvarId, pos }: LatexDisplayProps) {
  const ec = React.useContext(EditorContext)
  const rs = useRpcSession()
  const { sources, plain, tags } = React.useMemo(() => buildLatex(lines, mvarId), [lines, mvarId])
  const rootRef = React.useRef<HTMLDivElement>(null)
  const mathRef = React.useRef<HTMLDivElement>(null)
  // Prefix for the ids used in context menu actions.
  const uid = 'leantex' + React.useId().replace(/[^a-zA-Z0-9]/g, '')

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
  const latest = React.useRef({ tags, rs, ec, selected })
  latest.current = { tags, rs, ec, selected }

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
      setKeySelected(tags[id].key, on => !on)
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
      if ((e as any)._leanTexInTooltip) return
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
  }, [anyTooltip])

  // Context menu: VS Code reads `data-vscode-context` from the clicked element and its ancestors,
  // so we set it on the formula for the subexpression under the pointer.
  const onContextMenu = (e: React.MouseEvent<HTMLDivElement>) => {
    const id = tagIdAt(e.clientX, e.clientY, mathRef.current)
    const context: Record<string, string> = { interactiveCodeTagId: '', selectableLocationId: '', unselectableLocationId: '' }
    if (id !== undefined) {
      const key = tags[id].key
      context.interactiveCodeTagId = `${uid}|${id}`
      if (selected.includes(key)) context.unselectableLocationId = `${uid}|${key}`
      else context.selectableLocationId = `${uid}|${key}`
    }
    e.currentTarget.setAttribute('data-vscode-context', JSON.stringify(context))
    setTips([])
  }
  React.useEffect(() => {
    const h = ec.events.clickedContextMenu.on(action => {
      if (action.entry === 'unselectAll' && action.id === uid) {
        setSelected([])
        return
      }
      const sep = action.id.indexOf('|')
      if (sep < 0 || action.id.slice(0, sep) !== uid) return
      const arg = action.id.slice(sep + 1)
      if (action.entry === 'goToDefinition') void execGoTo(parseInt(arg), true)
      else if (action.entry === 'select') setKeySelected(arg, true)
      else if (action.entry === 'unselect') setKeySelected(arg, false)
    })
    return () => h.dispose()
  }, [ec, uid, execGoTo, setKeySelected])

  // Highlight boxes, recomputed when the highlighted subexpressions or the layout change.
  const selectedIds = tags.filter(t => selected.includes(t.key)).map(t => t.id)
  const underline = hover !== undefined && hover.ctrl && !!goTo.current.get(hover.id)
  const [boxes, setBoxes] = React.useState<Box[]>([])
  const [layoutVersion, setLayoutVersion] = React.useState(0)
  React.useEffect(() => {
    const root = rootRef.current
    if (!root || typeof ResizeObserver === 'undefined') return
    const obs = new ResizeObserver(() => setLayoutVersion(v => v + 1))
    obs.observe(root)
    return () => obs.disconnect()
  }, [])
  const highlightKey = JSON.stringify([selectedIds, hover?.id, underline])
  React.useLayoutEffect(() => {
    const root = rootRef.current
    if (!root) return
    const highlights: { id: number; className?: string; underline?: boolean }[] = selectedIds.map(id => ({
      id,
      className: 'highlight-selected',
    }))
    if (hover !== undefined) highlights.push({ id: hover.id, className: 'highlight' })
    if (underline && hover !== undefined) highlights.push({ id: hover.id, underline: true })
    setBoxes(computeBoxes(root, highlights))
  }, [highlightKey, sources, layoutVersion])

  const selectedTags = selected
    .map(key => tags.find(t => t.key === key))
    .filter((t): t is Tag => t !== undefined)

  return (
    <div
      ref={rootRef}
      className="lean-tex-display"
      style={{ position: 'relative' }}
      data-vscode-context={JSON.stringify(selected.length > 0 ? { selectedLocationsId: uid } : {})}
      data-selected-locations={JSON.stringify(selectedTags.flatMap(t => (t.loc ? [t.loc] : [])))}
    >
      <style>{STYLE}</style>
      {boxes.map(b => (
        <div
          key={b.key}
          className={b.className}
          style={{
            position: 'absolute',
            left: b.left,
            top: b.underline ? b.top + b.height - 1 : b.top,
            width: b.width,
            height: b.underline ? 1 : b.height,
            backgroundColor: b.underline ? 'var(--vscode-editor-foreground)' : undefined,
            pointerEvents: 'none',
            zIndex: 0,
          }}
        />
      ))}
      <div
        ref={mathRef}
        style={{ position: 'relative', zIndex: 1, cursor: hover !== undefined ? 'pointer' : undefined }}
        onPointerMove={onPointerMove}
        onPointerLeave={onPointerLeave}
        onPointerDown={onPointerDown}
        onMouseDown={onMouseDown}
        onClick={onClick}
        onContextMenu={onContextMenu}
      >
        {sources.map((source, i) => (
          <MathLine key={i} source={source} />
        ))}
      </div>
      <a
        className="lean-tex-copy link pointer codicon codicon-copy"
        title="Copy LaTeX"
        style={{ position: 'absolute', top: 0, right: 0, zIndex: 2 }}
        onClick={() => void ec.api.copyToClipboard(plain)}
      />
      {tips.map(
        t =>
          tags[t.id] && (
            <Tooltip
              key={t.id}
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
              <TypePopupContents info={tags[t.id].info} />
            </Tooltip>
          ),
      )}
      {noDefTip !== undefined && (
        <Tooltip anchor={() => tagRect(mathRef.current, noDefTip)} onClick={() => setNoDefTip(undefined)}>
          No definition found for this subexpression
        </Tooltip>
      )}
      {selectedTags.length > 0 && (
        <div className="mt2" style={{ position: 'relative', zIndex: 1 }}>
          <div style={{ opacity: 0.7 }}>
            Selected (shift-click to toggle){' '}
            <a className="link pointer" onClick={() => setSelected([])}>
              clear
            </a>
          </div>
          {selectedTags.map(tag => (
            <SelectedExpr key={tag.key} tag={tag} />
          ))}
        </div>
      )}
    </div>
  )
}
