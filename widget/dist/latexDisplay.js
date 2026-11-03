// src/latexDisplay.tsx
import * as React from "react";
import * as ReactDOM from "react-dom";
import {
  EditorContext,
  InteractiveCode,
  InteractiveDiagnostics_infoToInteractive,
  Markdown,
  getGoToLocation,
  mapRpcError,
  useAsync,
  useRpcSession
} from "@leanprover/infoview";
var DEFAULT_PALETTE = [
  "var(--vscode-charts-blue, #3794ff)",
  "var(--vscode-charts-orange, #d18616)",
  "var(--vscode-charts-purple, #b180d7)",
  "var(--vscode-charts-green, #4fb36b)",
  "var(--vscode-charts-red, #f14c4c)",
  "var(--vscode-terminal-ansiCyan, #11a8cd)",
  "var(--vscode-charts-yellow, #cca700)",
  "var(--vscode-terminal-ansiMagenta, #bc3fbc)"
];
var MAX_COLORS = 64;
var VarColorsContext = React.createContext({ palette: [], index: /* @__PURE__ */ new Map() });
function makeVarColors(enabled, custom) {
  const palette = enabled ? (custom.length > 0 ? custom : DEFAULT_PALETTE).slice(0, MAX_COLORS) : [];
  return { palette, index: /* @__PURE__ */ new Map() };
}
function varColorIndex(vc, fvarId) {
  if (vc.palette.length === 0) return void 0;
  let i = vc.index.get(fvarId);
  if (i === void 0) {
    i = vc.index.size;
    vc.index.set(fvarId, i);
  }
  return i % vc.palette.length;
}
function paletteStyle(vc) {
  const style = {};
  vc.palette.forEach((c, i) => style[`--lean-var-${i}`] = c);
  return style;
}
var STYLE = `
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
${Array.from({ length: MAX_COLORS }, (_, i) => `.lean-var-${i} { fill: var(--lean-var-${i}); color: var(--lean-var-${i}); }`).join("\n")}

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
`;
function ensureStyles() {
  const id = "leantex-latex-display-styles";
  let el = document.getElementById(id);
  if (!el) {
    el = document.createElement("style");
    el.id = id;
    document.head.appendChild(el);
  }
  if (el.textContent !== STYLE) el.textContent = STYLE;
}
var MODE_KEY = "leantex.popupMode";
var popupMode = (() => {
  try {
    return window.localStorage.getItem(MODE_KEY) === "lean" ? "lean" : "tex";
  } catch {
    return "tex";
  }
})();
var popupModeListeners = /* @__PURE__ */ new Set();
function usePopupMode() {
  const [mode, setModeState] = React.useState(popupMode);
  React.useEffect(() => {
    popupModeListeners.add(setModeState);
    return () => {
      popupModeListeners.delete(setModeState);
    };
  }, []);
  const setMode = React.useCallback((m) => {
    popupMode = m;
    try {
      window.localStorage.setItem(MODE_KEY, m);
    } catch {
    }
    popupModeListeners.forEach((l) => l(m));
  }, []);
  return [mode, setMode];
}
function partLocation(part, pos, mvarId) {
  if (mvarId === void 0) return void 0;
  let loc;
  switch (part.kind) {
    case "hyp":
      if (part.fvarId == null) return void 0;
      loc = { hyp: part.fvarId };
      break;
    case "hypType":
      if (part.fvarId == null) return void 0;
      loc = { hypType: [part.fvarId, pos] };
      break;
    case "hypValue":
      if (part.fvarId == null) return void 0;
      loc = { hypValue: [part.fvarId, pos] };
      break;
    case "target":
      loc = { target: pos };
      break;
    default:
      return void 0;
  }
  return { mvarId, loc };
}
function stripTags(tt) {
  if ("text" in tt) return tt.text;
  if ("append" in tt) return tt.append.map(stripTags).join("");
  return stripTags(tt.tag[1]);
}
function buildLatex(lines, mvarId, vc) {
  const tags = [];
  const plainLines = [];
  const sources = lines.map((line, li) => {
    let plainLine = "";
    const tex = line.map((part, pi) => {
      const ids = /* @__PURE__ */ new Map();
      const go = (tt) => {
        if ("text" in tt) {
          plainLine += tt.text;
          return tt.text;
        }
        if ("append" in tt) return tt.append.map(go).join("");
        const [info, sub] = tt.tag;
        const pos = info.subexprPos ?? "/";
        const idKey = (info.binder ? "b" : "") + pos;
        let id = ids.get(idKey);
        if (id === void 0) {
          id = tags.length;
          ids.set(idKey, id);
          const loc = info.binder ? void 0 : partLocation(part, pos, mvarId);
          const key = loc ? JSON.stringify(loc) : `${li}/${pi}/${idKey}`;
          const color2 = info.fvarId != null ? varColorIndex(vc, info.fvarId) : void 0;
          tags.push({ id, info, part, loc, key, color: color2 });
        }
        const color = tags[id].color;
        const inner = color !== void 0 ? `\\class{lean-var-${color}}{${go(sub)}}` : go(sub);
        return `\\class{lean-se-${id}}{${inner}}`;
      };
      return go(part.latex);
    }).join("");
    plainLines.push(plainLine);
    return `$\\displaystyle ${tex}$`;
  });
  return {
    sources,
    targetLines: lines.map((line, i) => i > 0 && line.some((p) => p.kind === "target")),
    plain: plainLines.join("\n"),
    tags
  };
}
function tagLabel(tag) {
  const { part } = tag;
  const pos = tag.info.subexprPos ?? "/";
  if (tag.info.binder) return "bound variable";
  switch (part.kind) {
    case "hyp":
      return "hypothesis";
    case "hypType":
      return `${part.name} : ${pos}`;
    case "hypValue":
      return `${part.name} := ${pos}`;
    case "target":
      return `\u22A2 ${pos}`;
    default:
      return pos;
  }
}
function samePosition(p, q) {
  return p.uri === q.uri && p.line === q.line && p.character === q.character;
}
function isAnyTextSelected() {
  const s = window.getSelection();
  return s !== null && !s.isCollapsed;
}
function isModifierHeld(e) {
  return e.altKey || e.ctrlKey || e.shiftKey || e.metaKey;
}
function tagElements(root, id) {
  return root ? [...root.querySelectorAll(`svg .lean-se-${id}`)] : [];
}
function tagIdAt(x, y, root) {
  if (!root) return void 0;
  let best;
  let bestArea = Infinity;
  root.querySelectorAll('svg [class*="lean-se-"]').forEach((el) => {
    const r = el.getBoundingClientRect();
    if (x < r.left || x > r.right || y < r.top || y > r.bottom) return;
    const area = r.width * r.height;
    if (area <= bestArea) {
      const m = /(?:^|\s)lean-se-(\d+)(?:\s|$)/.exec(el.getAttribute("class") ?? "");
      if (m) {
        best = parseInt(m[1]);
        bestArea = area;
      }
    }
  });
  return best;
}
function tagContains(root, outer, inner) {
  if (outer === inner) return true;
  const inners = tagElements(root, inner);
  return tagElements(root, outer).some((o) => inners.some((i) => o.contains(i)));
}
function tagRect(root, id) {
  const els = tagElements(root, id);
  if (els.length === 0) return void 0;
  const rs = els.map((el) => el.getBoundingClientRect());
  return {
    left: Math.min(...rs.map((r) => r.left)),
    top: Math.min(...rs.map((r) => r.top)),
    right: Math.max(...rs.map((r) => r.right)),
    bottom: Math.max(...rs.map((r) => r.bottom))
  };
}
function tagBox(origin, math, id, padX = 2, padY = 1) {
  const r = tagRect(math, id);
  if (!r) return void 0;
  const o = origin.getBoundingClientRect();
  return {
    left: r.left - o.left - padX,
    top: r.top - o.top - padY,
    width: r.right - r.left + 2 * padX,
    height: r.bottom - r.top + 2 * padY
  };
}
function markInsideTooltip(e, owner) {
  const ev = e.nativeEvent;
  (ev._leanTexTooltipOwners ?? (ev._leanTexTooltipOwners = [])).push(owner);
}
function tooltipOwners(e) {
  return e._leanTexTooltipOwners ?? [];
}
function Tooltip(props) {
  const ref = React.useRef(null);
  const contentRef = React.useRef(null);
  const anchorRef = React.useRef(props.anchor);
  anchorRef.current = props.anchor;
  const [layout, setLayout] = React.useState();
  const update = React.useCallback(() => {
    const a = anchorRef.current();
    const t = ref.current;
    if (!a || !t || !contentRef.current) return;
    const offset = 9;
    const padding = 10;
    const vw = document.documentElement.clientWidth;
    const vh = window.innerHeight;
    const spaceAbove = a.top - offset - padding;
    const spaceBelow = vh - a.bottom - offset - padding;
    const placement = spaceAbove > spaceBelow ? "top" : "bottom";
    const maxHeight = Math.max(0, Math.min(300, placement === "top" ? spaceAbove : spaceBelow));
    const height = Math.min(contentRef.current.scrollHeight + 2, maxHeight);
    const width = t.offsetWidth;
    const center = (a.left + a.right) / 2;
    const left = Math.max(padding, Math.min(center - width / 2, vw - padding - width));
    const top = placement === "top" ? a.top - offset - height : a.bottom + offset;
    const arrowX = Math.max(12, Math.min(center - left, width - 12));
    const newLayout = { left: left + window.scrollX, top: top + window.scrollY, maxHeight, placement, arrowX };
    setLayout((old) => JSON.stringify(old) === JSON.stringify(newLayout) ? old : newLayout);
  }, []);
  React.useLayoutEffect(update);
  React.useEffect(() => {
    window.addEventListener("scroll", update, true);
    window.addEventListener("resize", update);
    const obs = typeof ResizeObserver !== "undefined" ? new ResizeObserver(update) : void 0;
    if (contentRef.current) obs?.observe(contentRef.current);
    return () => {
      window.removeEventListener("scroll", update, true);
      window.removeEventListener("resize", update);
      obs?.disconnect();
    };
  }, [update]);
  const tooltip = /* @__PURE__ */ React.createElement(
    "div",
    {
      ref,
      className: "lean-tex-tooltip",
      "data-placement": layout?.placement,
      style: {
        left: layout?.left ?? 0,
        top: layout?.top ?? 0,
        maxHeight: layout?.maxHeight,
        visibility: layout ? "visible" : "hidden"
      },
      onPointerDownCapture: (e) => markInsideTooltip(e, props.owner),
      onPointerEnter: props.onPointerEnter,
      onPointerLeave: props.onPointerLeave,
      onClick: props.onClick
    },
    layout && /* @__PURE__ */ React.createElement("div", { className: "lean-tex-tooltip-arrow", style: { left: layout.arrowX - 5 } }),
    /* @__PURE__ */ React.createElement("div", { ref: contentRef, className: "lean-tex-tooltip-content" }, props.children)
  );
  return ReactDOM.createPortal(tooltip, document.body);
}
function LeanPopupContents({ info, withDoc }) {
  const rs = useRpcSession();
  const popup = useAsync(() => InteractiveDiagnostics_infoToInteractive(rs, info), [rs, info]);
  return popup.state === "resolved" ? /* @__PURE__ */ React.createElement(React.Fragment, null, /* @__PURE__ */ React.createElement("div", { className: "font-code tl pre-wrap" }, popup.value.exprExplicit && /* @__PURE__ */ React.createElement(InteractiveCode, { fmt: popup.value.exprExplicit }), " :", " ", popup.value.type && /* @__PURE__ */ React.createElement(InteractiveCode, { fmt: popup.value.type })), withDoc && popup.value.doc && /* @__PURE__ */ React.createElement("div", { className: "lean-tex-popup-doc" }, /* @__PURE__ */ React.createElement(Markdown, { contents: popup.value.doc }))) : popup.state === "rejected" ? /* @__PURE__ */ React.createElement("span", { className: "lean-tex-muted" }, "Error: ", mapRpcError(popup.error).message) : /* @__PURE__ */ React.createElement("span", { className: "lean-tex-muted" }, "Loading\u2026");
}
function useLatexPopup(info) {
  const rs = useRpcSession();
  return useAsync(() => rs.call("LeanTeX.LatexDisplay.popup", info), [rs, info]);
}
function useBuiltFormula(lines) {
  const vc = React.useContext(VarColorsContext);
  return React.useMemo(() => lines ? buildLatex(lines, void 0, vc) : void 0, [lines, vc]);
}
function PopupContents({ info, depth }) {
  const [mode, setMode] = usePopupMode();
  const popup = useLatexPopup(info);
  const value = popup.state === "resolved" ? popup.value : void 0;
  const lines = React.useMemo(
    () => value && [
      [
        { latex: value.expr, kind: "expr" },
        ...value.type ? [
          { latex: { text: " : " }, kind: "text" },
          { latex: value.type, kind: "expr" }
        ] : []
      ]
    ],
    [value]
  );
  const built = useBuiltFormula(lines);
  const ec = React.useContext(EditorContext);
  const showLean = mode === "lean" || popup.state === "rejected";
  return /* @__PURE__ */ React.createElement("div", { className: "tooltip-code-content" }, /* @__PURE__ */ React.createElement("div", { className: "lean-tex-popup-head" }, /* @__PURE__ */ React.createElement("div", { className: "lean-tex-popup-main" }, showLean ? /* @__PURE__ */ React.createElement(LeanPopupContents, { info, withDoc: popup.state === "rejected" }) : built ? /* @__PURE__ */ React.createElement(InteractiveLatex, { built, depth }) : /* @__PURE__ */ React.createElement("span", { className: "lean-tex-muted" }, "Loading\u2026")), /* @__PURE__ */ React.createElement("div", { className: "lean-tex-popup-tools" }, value && !showLean && /* @__PURE__ */ React.createElement(
    "button",
    {
      className: "lean-tex-icon-button codicon codicon-copy",
      title: "Copy LaTeX",
      onClick: (e) => {
        e.stopPropagation();
        void ec.api.copyToClipboard(stripTags(value.expr));
      }
    }
  ), /* @__PURE__ */ React.createElement("div", { className: "lean-tex-segmented", role: "group", "aria-label": "Notation" }, /* @__PURE__ */ React.createElement("button", { "aria-pressed": mode === "tex", title: "Show in LaTeX", onClick: () => setMode("tex") }, "TeX"), /* @__PURE__ */ React.createElement("button", { "aria-pressed": mode === "lean", title: "Show in Lean syntax", onClick: () => setMode("lean") }, "Lean")))), value?.doc && /* @__PURE__ */ React.createElement("div", { className: "lean-tex-popup-doc" }, /* @__PURE__ */ React.createElement(Markdown, { contents: value.doc })));
}
var MathLine = React.memo(function MathLine2({ source, target }) {
  return /* @__PURE__ */ React.createElement("div", { className: target ? "lean-tex-line lean-tex-target-line" : "lean-tex-line" }, /* @__PURE__ */ React.createElement(Markdown, { contents: source }));
});
var SHOW_DELAY = 500;
var HIDE_DELAY = 300;
function InteractiveLatex(props) {
  const { built, depth, selection, contextMenuId, toolbar } = props;
  const { sources, targetLines, tags } = built;
  const ec = React.useContext(EditorContext);
  const rs = useRpcSession();
  const vc = React.useContext(VarColorsContext);
  const rootRef = React.useRef(null);
  const mathRef = React.useRef(null);
  const owner = React.useId();
  const selected = selection?.selected ?? [];
  const [hover, setHover] = React.useState();
  const [tips, setTips] = React.useState([]);
  const [noDefTip, setNoDefTip] = React.useState();
  const goTo = React.useRef(/* @__PURE__ */ new Map());
  const [, setGoToVersion] = React.useState(0);
  React.useEffect(() => {
    setHover(void 0);
    setTips([]);
    setNoDefTip(void 0);
    goTo.current = /* @__PURE__ */ new Map();
  }, [tags]);
  const latest = React.useRef({ tags, rs, ec });
  latest.current = { tags, rs, ec };
  const fetchGoTo = React.useCallback(async (id) => {
    const cached = goTo.current.get(id);
    if (cached !== void 0) return cached ?? void 0;
    const { tags: tags2, rs: rs2 } = latest.current;
    const tag = tags2[id];
    if (!tag) return void 0;
    let loc = null;
    try {
      const links = await getGoToLocation(rs2, "definition", tag.info.info);
      if (links.length > 0) loc = { uri: links[0].targetUri, range: links[0].targetSelectionRange };
    } catch (e) {
      console.error("Error in go-to-definition: ", JSON.stringify(e));
    }
    goTo.current.set(id, loc);
    setGoToVersion((v) => v + 1);
    return loc ?? void 0;
  }, []);
  const execGoTo = React.useCallback(
    async (id, withError) => {
      const loc = await fetchGoTo(id);
      if (loc === void 0) {
        if (withError) setNoDefTip(id);
        return;
      }
      await latest.current.ec.revealPosition({ uri: loc.uri, ...loc.range.start });
    },
    [fetchGoTo]
  );
  React.useEffect(() => {
    if (hover?.ctrl) void fetchGoTo(hover.id);
  }, [hover, fetchGoTo]);
  const hovering = hover !== void 0;
  React.useEffect(() => {
    if (!hovering) return;
    const onKey = (ctrl) => (e) => {
      if (e.key === "Control" || e.key === "Meta") setHover((h) => h && { ...h, ctrl });
    };
    const down = onKey(true);
    const up = onKey(false);
    document.addEventListener("keydown", down);
    document.addEventListener("keyup", up);
    return () => {
      document.removeEventListener("keydown", down);
      document.removeEventListener("keyup", up);
    };
  }, [hovering]);
  const showTimer = React.useRef();
  const hideTimer = React.useRef();
  const pointerOverTooltip = React.useRef(false);
  React.useEffect(
    () => () => {
      window.clearTimeout(showTimer.current);
      window.clearTimeout(hideTimer.current);
    },
    []
  );
  const startShowTimeout = (id) => {
    window.clearTimeout(showTimer.current);
    showTimer.current = window.setTimeout(() => {
      if (isAnyTextSelected()) return;
      setTips((ts) => ts.some((t) => t.id === id) ? ts : [...ts.filter((t) => t.pinned), { id, pinned: false }]);
    }, SHOW_DELAY);
  };
  const startHideTimeout = () => {
    window.clearTimeout(hideTimer.current);
    hideTimer.current = window.setTimeout(() => {
      if (!pointerOverTooltip.current) setTips((ts) => ts.filter((t) => t.pinned));
    }, HIDE_DELAY);
  };
  const onPointerMove = (e) => {
    const id = tagIdAt(e.clientX, e.clientY, mathRef.current);
    const ctrl = e.ctrlKey || e.metaKey;
    if (id === hover?.id) {
      if (hover && ctrl !== hover.ctrl) setHover({ id: hover.id, ctrl });
      return;
    }
    setHover(id === void 0 ? void 0 : { id, ctrl });
    window.clearTimeout(showTimer.current);
    startHideTimeout();
    if (id !== void 0 && !isModifierHeld(e)) startShowTimeout(id);
  };
  const onPointerLeave = () => {
    setHover(void 0);
    window.clearTimeout(showTimer.current);
    startHideTimeout();
  };
  const onPointerDown = (e) => {
    if (isModifierHeld(e) && tagIdAt(e.clientX, e.clientY, mathRef.current) !== void 0) e.preventDefault();
  };
  const onMouseDown = (e) => {
    if (e.detail > 1) e.preventDefault();
  };
  const onClick = (e) => {
    const id = tagIdAt(e.clientX, e.clientY, mathRef.current);
    if (id === void 0) return;
    if (e.ctrlKey || e.metaKey) {
      setHover({ id, ctrl: true });
      void execGoTo(id, false);
      return;
    }
    if (e.shiftKey) {
      selection?.setKeySelected(tags[id].key, (on) => !on);
      e.preventDefault();
      return;
    }
    if (isAnyTextSelected()) return;
    window.clearTimeout(showTimer.current);
    window.clearTimeout(hideTimer.current);
    setTips((ts) => {
      const t = ts.find((t2) => t2.id === id);
      if (t?.pinned) return ts.filter((t2) => t2.id !== id);
      return [...ts.filter((t2) => t2.id !== id && t2.pinned), { id, pinned: true }];
    });
  };
  const anyTooltip = tips.length > 0 || noDefTip !== void 0;
  React.useEffect(() => {
    if (!anyTooltip) return;
    const onPointerDownAnywhere = (e) => {
      if (tooltipOwners(e).includes(owner)) return;
      if (e.target instanceof Element && e.target.tagName === "HTML") return;
      setNoDefTip(void 0);
      const math = mathRef.current;
      const id = math && e.target instanceof Node && math.contains(e.target) ? tagIdAt(e.clientX, e.clientY, math) : void 0;
      setTips((ts) => ts.filter((t) => id !== void 0 && tagContains(math, t.id, id)));
    };
    document.addEventListener("pointerdown", onPointerDownAnywhere);
    return () => document.removeEventListener("pointerdown", onPointerDownAnywhere);
  }, [anyTooltip, owner]);
  const onContextMenu = (e) => {
    if (contextMenuId === void 0) return;
    const id = tagIdAt(e.clientX, e.clientY, mathRef.current);
    const context = { interactiveCodeTagId: "", selectableLocationId: "", unselectableLocationId: "" };
    if (id !== void 0) {
      const key = tags[id].key;
      context.interactiveCodeTagId = `${contextMenuId}|${id}`;
      if (selection) {
        if (selected.includes(key)) context.unselectableLocationId = `${contextMenuId}|${key}`;
        else context.selectableLocationId = `${contextMenuId}|${key}`;
      }
    }
    e.currentTarget.setAttribute("data-vscode-context", JSON.stringify(context));
    setTips([]);
  };
  const setKeySelected = selection?.setKeySelected;
  React.useEffect(() => {
    if (contextMenuId === void 0) return;
    const h = ec.events.clickedContextMenu.on((action) => {
      const sep = action.id.indexOf("|");
      if (sep < 0 || action.id.slice(0, sep) !== contextMenuId) return;
      const arg = action.id.slice(sep + 1);
      if (action.entry === "goToDefinition") void execGoTo(parseInt(arg), true);
      else if (action.entry === "select") setKeySelected?.(arg, true);
      else if (action.entry === "unselect") setKeySelected?.(arg, false);
    });
    return () => h.dispose();
  }, [ec, contextMenuId, execGoTo, setKeySelected]);
  const selectedIds = tags.filter((t) => selected.includes(t.key)).map((t) => t.id);
  const underline = hover !== void 0 && hover.ctrl && !!goTo.current.get(hover.id);
  const [hoverBox, setHoverBox] = React.useState();
  const [boxes, setBoxes] = React.useState([]);
  const [layoutVersion, setLayoutVersion] = React.useState(0);
  React.useEffect(() => {
    const root = rootRef.current;
    if (!root || typeof ResizeObserver === "undefined") return;
    const obs = new ResizeObserver(() => setLayoutVersion((v) => v + 1));
    obs.observe(root);
    return () => obs.disconnect();
  }, []);
  const colorOf = (tag) => tag?.color !== void 0 ? vc.palette[tag.color] : void 0;
  const highlightKey = JSON.stringify([selectedIds, hover?.id, underline]);
  React.useLayoutEffect(() => {
    const root = rootRef.current;
    const math = mathRef.current;
    if (!root) return;
    const newBoxes = [];
    for (const id of selectedIds) {
      const box = tagBox(root, math, id);
      if (box) newBoxes.push({ key: `sel-${id}`, className: "lean-tex-selected", box });
    }
    const hovered = hover !== void 0 ? tags[hover.id] : void 0;
    if (hovered) {
      const color = colorOf(hovered);
      for (const t of tags) {
        if (t.id === hovered.id || t.info.key !== hovered.info.key) continue;
        const box2 = tagBox(root, math, t.id);
        if (box2) newBoxes.push({ key: `occ-${t.id}`, className: "lean-tex-occurrence", box: box2, color });
      }
      if (underline) {
        const r = tagBox(root, math, hovered.id, 0, 0);
        if (r) {
          newBoxes.push({
            key: `ul-${hovered.id}`,
            className: "lean-tex-underline",
            box: { left: r.left, top: r.top + r.height - 1, width: r.width, height: 1.5 }
          });
        }
      }
      const box = tagBox(root, math, hovered.id);
      if (box) setHoverBox((prev) => ({ ...box, color, visible: true, instant: !prev?.visible }));
    } else {
      setHoverBox((prev) => prev && { ...prev, visible: false, instant: false });
    }
    setBoxes(newBoxes);
  }, [highlightKey, sources, layoutVersion]);
  return /* @__PURE__ */ React.createElement("div", { ref: rootRef, className: "lean-tex", style: paletteStyle(vc) }, hoverBox && /* @__PURE__ */ React.createElement(
    "div",
    {
      className: "lean-tex-box lean-tex-hover" + (hoverBox.color ? " lean-tex-colored" : ""),
      "data-instant": hoverBox.instant ? "" : void 0,
      style: {
        left: hoverBox.left,
        top: hoverBox.top,
        width: hoverBox.width,
        height: hoverBox.height,
        opacity: hoverBox.visible ? 1 : 0,
        ...hoverBox.color ? { "--lt-hl": hoverBox.color } : {}
      }
    }
  ), boxes.map((b) => /* @__PURE__ */ React.createElement(
    "div",
    {
      key: b.key,
      className: "lean-tex-box " + b.className,
      style: {
        ...b.box,
        ...b.color ? { "--lt-hl": b.color } : {}
      }
    }
  )), /* @__PURE__ */ React.createElement(
    "div",
    {
      ref: mathRef,
      className: "lean-tex-math",
      style: { cursor: hover !== void 0 ? "pointer" : void 0 },
      onPointerMove,
      onPointerLeave,
      onPointerDown,
      onMouseDown,
      onClick,
      onContextMenu
    },
    sources.map((source, i) => /* @__PURE__ */ React.createElement(MathLine, { key: i, source, target: targetLines[i] }))
  ), toolbar && /* @__PURE__ */ React.createElement("div", { className: "lean-tex-toolbar" }, toolbar), tips.map(
    (t) => tags[t.id] && /* @__PURE__ */ React.createElement(
      Tooltip,
      {
        key: t.id,
        owner,
        anchor: () => tagRect(mathRef.current, t.id),
        onPointerEnter: () => {
          pointerOverTooltip.current = true;
          window.clearTimeout(hideTimer.current);
        },
        onPointerLeave: () => {
          pointerOverTooltip.current = false;
          startHideTimeout();
        },
        onClick: () => setTips((ts) => ts.map((u) => u.id === t.id ? { ...u, pinned: true } : u))
      },
      /* @__PURE__ */ React.createElement(PopupContents, { info: tags[t.id].info.info, depth: depth + 1 })
    )
  ), noDefTip !== void 0 && /* @__PURE__ */ React.createElement(Tooltip, { owner, anchor: () => tagRect(mathRef.current, noDefTip), onClick: () => setNoDefTip(void 0) }, "No definition found for this subexpression"));
}
function CopyButton({ text, title }) {
  const ec = React.useContext(EditorContext);
  const [copied, setCopied] = React.useState(false);
  React.useEffect(() => {
    if (!copied) return;
    const t = window.setTimeout(() => setCopied(false), 1500);
    return () => window.clearTimeout(t);
  }, [copied]);
  return /* @__PURE__ */ React.createElement(
    "button",
    {
      className: "lean-tex-icon-button codicon " + (copied ? "codicon-check" : "codicon-copy"),
      title: copied ? "Copied" : title,
      onClick: () => {
        void ec.api.copyToClipboard(text);
        setCopied(true);
      }
    }
  );
}
function SelectedExpr({ tag }) {
  const [mode] = usePopupMode();
  const popup = useLatexPopup(tag.info.info);
  const value = popup.state === "resolved" ? popup.value : void 0;
  const lines = React.useMemo(() => value && [[{ latex: value.expr, kind: "expr" }]], [value]);
  const built = useBuiltFormula(lines);
  return /* @__PURE__ */ React.createElement("div", { className: "lean-tex-selection-item", "data-location": tag.loc ? JSON.stringify(tag.loc) : void 0 }, /* @__PURE__ */ React.createElement("span", { className: "lean-tex-selection-label font-code", title: tag.loc ? JSON.stringify(tag.loc) : void 0 }, tagLabel(tag)), /* @__PURE__ */ React.createElement("div", { style: { minWidth: 0, flex: 1 } }, mode === "lean" || popup.state === "rejected" ? /* @__PURE__ */ React.createElement(LeanExpr, { info: tag.info.info }) : built ? /* @__PURE__ */ React.createElement(InteractiveLatex, { built, depth: 1 }) : /* @__PURE__ */ React.createElement("span", { className: "lean-tex-muted" }, "\u2026")));
}
function LeanExpr({ info }) {
  const rs = useRpcSession();
  const popup = useAsync(() => InteractiveDiagnostics_infoToInteractive(rs, info), [rs, info]);
  return /* @__PURE__ */ React.createElement("span", { className: "font-code pre-wrap" }, popup.state === "resolved" && popup.value.exprExplicit ? /* @__PURE__ */ React.createElement(InteractiveCode, { fmt: popup.value.exprExplicit }) : popup.state === "rejected" ? `Error: ${mapRpcError(popup.error).message}` : "\u2026");
}
function LatexDisplay({ lines, mvarId, pos, colorVariables, variableColors }) {
  const ec = React.useContext(EditorContext);
  const colorsKey = JSON.stringify([colorVariables ?? true, variableColors ?? []]);
  const vc = React.useMemo(() => makeVarColors(colorVariables ?? true, variableColors ?? []), [colorsKey, lines]);
  const built = React.useMemo(() => buildLatex(lines, mvarId, vc), [lines, mvarId, vc]);
  const { plain, tags } = built;
  const uid = "leantex" + React.useId().replace(/[^a-zA-Z0-9]/g, "");
  React.useLayoutEffect(ensureStyles, []);
  const [selected, setSelected] = React.useState([]);
  const [prevPos, setPrevPos] = React.useState(pos);
  if (!samePosition(pos, prevPos)) {
    setPrevPos(pos);
    setSelected([]);
  }
  const setKeySelected = React.useCallback((key, act) => {
    setSelected((sel) => {
      const wasSelected = sel.includes(key);
      const isSelected = typeof act === "function" ? act(wasSelected) : act;
      if (wasSelected === isSelected) return sel;
      return isSelected ? [...sel, key] : sel.filter((k) => k !== key);
    });
  }, []);
  const selection = React.useMemo(() => ({ selected, setKeySelected }), [selected, setKeySelected]);
  React.useEffect(() => {
    const h = ec.events.clickedContextMenu.on((action) => {
      if (action.entry === "unselectAll" && action.id === uid) setSelected([]);
    });
    return () => h.dispose();
  }, [ec, uid]);
  const selectedTags = selected.map((key) => tags.find((t) => t.key === key)).filter((t) => t !== void 0);
  return /* @__PURE__ */ React.createElement(VarColorsContext.Provider, { value: vc }, /* @__PURE__ */ React.createElement(
    "div",
    {
      className: "lean-tex-display",
      "data-vscode-context": JSON.stringify(selected.length > 0 ? { selectedLocationsId: uid } : {}),
      "data-selected-locations": JSON.stringify(selectedTags.flatMap((t) => t.loc ? [t.loc] : []))
    },
    /* @__PURE__ */ React.createElement(
      InteractiveLatex,
      {
        built,
        depth: 0,
        selection,
        contextMenuId: uid,
        toolbar: /* @__PURE__ */ React.createElement(CopyButton, { text: plain, title: "Copy LaTeX" })
      }
    ),
    selectedTags.length > 0 && /* @__PURE__ */ React.createElement("div", { className: "lean-tex-selection lean-tex" }, /* @__PURE__ */ React.createElement("div", { className: "lean-tex-selection-head lean-tex-muted" }, /* @__PURE__ */ React.createElement("span", null, "Selected"), /* @__PURE__ */ React.createElement("span", null, "\xB7"), /* @__PURE__ */ React.createElement("a", { className: "link pointer", onClick: () => setSelected([]) }, "clear"), /* @__PURE__ */ React.createElement("span", { style: { textTransform: "none", letterSpacing: "normal" } }, "(shift-click to toggle)")), selectedTags.map((tag) => /* @__PURE__ */ React.createElement(SelectedExpr, { key: tag.key, tag })))
  ));
}
export {
  LatexDisplay as default
};
