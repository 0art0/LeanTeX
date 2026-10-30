/**
 * Client side of `LeanTeX.LatexDisplay`: lines of LaTeX, rendered with the infoview's MathJax,
 * where subexpressions show their type and docstring on hover and can be selected with shift-click.
 *
 * The server sends each part of a line as `CodeWithInfos` whose leaves are LaTeX fragments.
 * We give each tagged subexpression an id `N` and wrap its LaTeX in `\class{lean-se-N}{...}`.
 * MathJax (SVG output) puts the class on the `<g>` element for the subexpression, which is how we
 * find the subexpression under the pointer. Since `<g>` elements have no background, highlights
 * are boxes drawn behind the formula.
 *
 * Selection is local to this widget: panel widgets are rendered outside the infoview's
 * `LocationsContext`, so they cannot share the goal view's selection.
 */
import * as React from 'react'
import {
  CodeWithInfos,
  GoalLocation,
  GoalsLocation,
  InfoPopup,
  InteractiveCode,
  InteractiveDiagnostics_infoToInteractive,
  Markdown,
  SubexprInfo,
  TaggedText,
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

/** Mirrors `LeanTeX.LatexDisplay.Props`. */
interface LatexDisplayProps {
  lines: LatexPart[][]
  mvarId?: string
}

/** A tagged subexpression. */
interface Tag {
  id: number
  info: SubexprInfo
  part: LatexPart
}

/** Builds the MathJax source for each line, assigning ids to tagged subexpressions.
 * Subexpressions are identified by their part and position, since the server may tag
 * several pieces of LaTeX with the same subexpression (for example the base and subscript of
 * `x_i` when a superscript is added). */
function buildLatex(lines: LatexPart[][]): { sources: string[]; tags: Tag[] } {
  const tags: Tag[] = []
  const sources = lines.map(line => {
    const tex = line
      .map(part => {
        const ids = new Map<string, number>()
        const go = (tt: TaggedText<SubexprInfo>): string => {
          if ('text' in tt) return tt.text
          if ('append' in tt) return tt.append.map(go).join('')
          const [info, sub] = tt.tag
          const key = info.subexprPos ?? '/'
          let id = ids.get(key)
          if (id === undefined) {
            id = tags.length
            ids.set(key, id)
            tags.push({ id, info, part })
          }
          return `\\class{lean-se-${id}}{${go(sub)}}`
        }
        return go(part.latex)
      })
      .join('')
    return `$\\displaystyle ${tex}$`
  })
  return { sources, tags }
}

/** The location of a tagged subexpression within the goal, if there is a goal. */
function tagLocation(tag: Tag, mvarId: string | undefined): GoalsLocation | undefined {
  const { part } = tag
  const pos = tag.info.subexprPos ?? '/'
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

/** The tag id of an element, if it is a tagged subexpression. */
function tagIdOf(el: Element): number | undefined {
  const m = /(?:^|\s)lean-se-(\d+)(?:\s|$)/.exec(el.getAttribute('class') ?? '')
  return m ? parseInt(m[1]) : undefined
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
      const id = tagIdOf(el)
      if (id !== undefined) {
        best = id
        bestArea = area
      }
    }
  })
  return best
}

/** One rendered line. Memoized so that MathJax does not re-render when the highlight changes. */
const MathLine = React.memo(function MathLine({ source }: { source: string }) {
  return <Markdown contents={source} />
})

interface Box {
  key: string
  left: number
  top: number
  width: number
  height: number
  className: string
}

/** Computes highlight boxes, relative to `root`, for the subexpressions with the given ids. */
function computeBoxes(root: HTMLElement, highlights: [number, string][]): Box[] {
  const rootRect = root.getBoundingClientRect()
  const boxes: Box[] = []
  for (const [id, className] of highlights) {
    root.querySelectorAll(`.lean-se-${id}`).forEach((el, i) => {
      const r = el.getBoundingClientRect()
      boxes.push({
        key: `${className}-${id}-${i}`,
        left: r.left - rootRect.left,
        top: r.top - rootRect.top,
        width: r.width,
        height: r.height,
        className,
      })
    })
  }
  return boxes
}

/** Like the infoview's `TypePopupContents`: the subexpression and its type, then its docstring. */
function InfoPopupContents({ info }: { info: SubexprInfo }) {
  const rs = useRpcSession()
  const popup = useAsync<InfoPopup>(() => InteractiveDiagnostics_infoToInteractive(rs, info.info), [rs, info])
  if (popup.state === 'loading') return <div className="tooltip-code-content">Loading...</div>
  if (popup.state === 'rejected')
    return <div className="tooltip-code-content">Error: {mapRpcError(popup.error).message}</div>
  const { type, exprExplicit, doc } = popup.value
  return (
    <div className="tooltip-code-content">
      {type && (
        <div className="font-code tl pre-wrap">
          {exprExplicit && <InteractiveCode fmt={exprExplicit} />} : <InteractiveCode fmt={type} />
        </div>
      )}
      {doc && (
        <>
          {type && <hr />}
          <Markdown contents={doc} />
        </>
      )}
    </div>
  )
}

/** A selected subexpression, shown in Lean syntax. */
function SelectedExpr({ tag, mvarId }: { tag: Tag; mvarId?: string }) {
  const rs = useRpcSession()
  const popup = useAsync<InfoPopup>(() => InteractiveDiagnostics_infoToInteractive(rs, tag.info.info), [rs, tag])
  const loc = tagLocation(tag, mvarId)
  return (
    <div className="font-code pre-wrap" data-location={loc ? JSON.stringify(loc) : undefined}>
      <span style={{ opacity: 0.7 }} title={loc ? JSON.stringify(loc) : undefined}>
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

const POPUP_OPEN_DELAY = 300
const POPUP_CLOSE_DELAY = 200

export default function LatexDisplay({ lines, mvarId }: LatexDisplayProps) {
  const { sources, tags } = React.useMemo(() => buildLatex(lines), [lines])
  const rootRef = React.useRef<HTMLDivElement>(null)
  const mathRef = React.useRef<HTMLDivElement>(null)

  const [hovered, setHovered] = React.useState<number | undefined>()
  const [selected, setSelected] = React.useState<number[]>([])
  const [popup, setPopup] = React.useState<{ id: number; pinned: boolean } | undefined>()
  // Reset when the contents change, since ids then refer to different subexpressions.
  React.useEffect(() => {
    setHovered(undefined)
    setSelected([])
    setPopup(undefined)
  }, [tags])

  // Popup timers.
  const openTimer = React.useRef<number | undefined>()
  const closeTimer = React.useRef<number | undefined>()
  const clearTimers = () => {
    window.clearTimeout(openTimer.current)
    window.clearTimeout(closeTimer.current)
  }
  React.useEffect(() => clearTimers, [])
  const scheduleClose = () => {
    window.clearTimeout(closeTimer.current)
    closeTimer.current = window.setTimeout(
      () => setPopup(p => (p?.pinned ? p : undefined)),
      POPUP_CLOSE_DELAY,
    )
  }

  const hoveredRef = React.useRef<number | undefined>()
  const onPointerMove = (e: React.PointerEvent) => {
    const id = tagIdAt(e.clientX, e.clientY, mathRef.current)
    if (id === hoveredRef.current) return
    hoveredRef.current = id
    setHovered(id)
    clearTimers()
    if (id === undefined) {
      scheduleClose()
    } else {
      openTimer.current = window.setTimeout(
        () => setPopup(p => (p?.pinned ? p : { id, pinned: false })),
        POPUP_OPEN_DELAY,
      )
    }
  }
  const onPointerLeave = () => {
    hoveredRef.current = undefined
    setHovered(undefined)
    clearTimers()
    scheduleClose()
  }
  const onMouseDown = (e: React.MouseEvent) => {
    // Prevent shift-click from selecting text.
    if (e.shiftKey && tagIdAt(e.clientX, e.clientY, mathRef.current) !== undefined) e.preventDefault()
  }
  const onClick = (e: React.MouseEvent) => {
    const id = tagIdAt(e.clientX, e.clientY, mathRef.current)
    if (id === undefined) {
      setPopup(undefined)
      return
    }
    e.stopPropagation()
    if (e.shiftKey) {
      setSelected(sel => (sel.includes(id) ? sel.filter(i => i !== id) : [...sel, id]))
    } else {
      // Plain click pins the popup, like clicking in the goal view.
      clearTimers()
      setPopup(p => (p?.id === id && p.pinned ? undefined : { id, pinned: true }))
    }
  }

  // Highlight boxes, recomputed when the highlighted subexpressions or the layout change.
  const [boxes, setBoxes] = React.useState<Box[]>([])
  const [layoutVersion, setLayoutVersion] = React.useState(0)
  React.useEffect(() => {
    const root = rootRef.current
    if (!root || typeof ResizeObserver === 'undefined') return
    const obs = new ResizeObserver(() => setLayoutVersion(v => v + 1))
    obs.observe(root)
    return () => obs.disconnect()
  }, [])
  const hoverId = hovered ?? popup?.id
  React.useLayoutEffect(() => {
    const root = rootRef.current
    if (!root) return
    const highlights: [number, string][] = selected.map(id => [id, 'highlight-selected'])
    if (hoverId !== undefined) highlights.push([hoverId, 'highlight'])
    setBoxes(computeBoxes(root, highlights))
  }, [hoverId, selected, sources, layoutVersion])

  // Popup position: below the subexpression's first box.
  const popupTag = popup !== undefined ? tags[popup.id] : undefined
  let popupStyle: React.CSSProperties | undefined
  if (popup !== undefined && rootRef.current) {
    const el = rootRef.current.querySelector(`.lean-se-${popup.id}`)
    if (el) {
      const r = el.getBoundingClientRect()
      const rootRect = rootRef.current.getBoundingClientRect()
      popupStyle = {
        position: 'absolute',
        left: Math.max(0, r.left - rootRect.left),
        top: r.bottom - rootRect.top + 4,
        zIndex: 10,
        maxWidth: '40em',
        maxHeight: '20em',
        display: 'flex',
        flexDirection: 'column',
        minWidth: '10em',
      }
    }
  }

  const selectedTags = selected.map(id => tags[id]).filter((t): t is Tag => t !== undefined)
  const selectedLocations = selectedTags
    .map(t => tagLocation(t, mvarId))
    .filter((l): l is GoalsLocation => l !== undefined)

  return (
    <div
      ref={rootRef}
      className="lean-tex-display"
      style={{ position: 'relative' }}
      data-selected-locations={JSON.stringify(selectedLocations)}
    >
      {boxes.map(b => (
        <div
          key={b.key}
          className={b.className}
          style={{
            position: 'absolute',
            left: b.left,
            top: b.top,
            width: b.width,
            height: b.height,
            pointerEvents: 'none',
            borderRadius: 2,
            zIndex: 0,
          }}
        />
      ))}
      <div
        ref={mathRef}
        style={{ position: 'relative', zIndex: 1, cursor: hovered !== undefined ? 'pointer' : undefined }}
        onPointerMove={onPointerMove}
        onPointerLeave={onPointerLeave}
        onMouseDown={onMouseDown}
        onClick={onClick}
      >
        {sources.map((source, i) => (
          <MathLine key={i} source={source} />
        ))}
      </div>
      {popupTag && popupStyle && (
        <div
          className="tooltip"
          style={popupStyle}
          onPointerEnter={() => window.clearTimeout(closeTimer.current)}
          onPointerLeave={scheduleClose}
        >
          <div className="tooltip-content">
            <InfoPopupContents info={popupTag.info} />
          </div>
        </div>
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
            <SelectedExpr key={tag.id} tag={tag} mvarId={mvarId} />
          ))}
        </div>
      )}
    </div>
  )
}
