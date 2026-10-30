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
function partLocation(part, pos, mvarId) {
  if (mvarId === void 0) return void 0;
  let loc;
  switch (part.kind) {
    case "hyp":
      if (part.fvarId === void 0) return void 0;
      loc = { hyp: part.fvarId };
      break;
    case "hypType":
      if (part.fvarId === void 0) return void 0;
      loc = { hypType: [part.fvarId, pos] };
      break;
    case "hypValue":
      if (part.fvarId === void 0) return void 0;
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
function buildLatex(lines, mvarId) {
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
        let id = ids.get(pos);
        if (id === void 0) {
          id = tags.length;
          ids.set(pos, id);
          const loc = partLocation(part, pos, mvarId);
          const key = loc ? JSON.stringify(loc) : `${li}/${pi}/${pos}`;
          tags.push({ id, info, part, loc, key });
        }
        return `\\class{lean-se-${id}}{${go(sub)}}`;
      };
      return go(part.latex);
    }).join("");
    plainLines.push(plainLine);
    return `$\\displaystyle ${tex}$`;
  });
  return { sources, plain: plainLines.join("\n"), tags };
}
function tagLabel(tag) {
  const { part } = tag;
  const pos = tag.info.subexprPos ?? "/";
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
  return root ? [...root.querySelectorAll(`.lean-se-${id}`)] : [];
}
function tagIdAt(x, y, root) {
  if (!root) return void 0;
  let best;
  let bestArea = Infinity;
  root.querySelectorAll('[class*="lean-se-"]').forEach((el) => {
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
function computeBoxes(root, highlights) {
  const rootRect = root.getBoundingClientRect();
  const boxes = [];
  for (const { id, className, underline } of highlights) {
    tagElements(root, id).forEach((el, i) => {
      const r = el.getBoundingClientRect();
      boxes.push({
        key: `${className}-${underline}-${id}-${i}`,
        left: r.left - rootRect.left,
        top: r.top - rootRect.top,
        width: r.width,
        height: r.height,
        className,
        underline
      });
    });
  }
  return boxes;
}
function markInsideTooltip(e) {
  ;
  e.nativeEvent._leanTexInTooltip = true;
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
    const offset = 8;
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
    const arrowX = Math.max(10, Math.min(center - left, width - 10));
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
      className: "tooltip",
      style: {
        position: "absolute",
        left: layout?.left ?? 0,
        top: layout?.top ?? 0,
        maxHeight: layout?.maxHeight,
        visibility: layout ? "visible" : "hidden"
      },
      onPointerDownCapture: markInsideTooltip,
      onPointerEnter: props.onPointerEnter,
      onPointerLeave: props.onPointerLeave,
      onClick: props.onClick
    },
    layout && /* @__PURE__ */ React.createElement(
      "svg",
      {
        width: 14,
        height: 7,
        style: {
          position: "absolute",
          left: layout.arrowX - 7,
          ...layout.placement === "top" ? { bottom: -7 } : { top: -7, transform: "rotate(180deg)" }
        }
      },
      /* @__PURE__ */ React.createElement(
        "path",
        {
          d: "M0,0 L7,7 L14,0",
          fill: "var(--vscode-editorHoverWidget-background)",
          stroke: "var(--vscode-editorHoverWidget-border)"
        }
      )
    ),
    /* @__PURE__ */ React.createElement("div", { ref: contentRef, className: "tooltip-content" }, props.children)
  );
  return ReactDOM.createPortal(tooltip, document.body);
}
function TypePopupContents({ info }) {
  const rs = useRpcSession();
  const popup = useAsync(() => InteractiveDiagnostics_infoToInteractive(rs, info.info), [rs, info.info]);
  return /* @__PURE__ */ React.createElement("div", { className: "tooltip-code-content" }, popup.state === "resolved" ? /* @__PURE__ */ React.createElement(React.Fragment, null, /* @__PURE__ */ React.createElement("div", { className: "font-code tl pre-wrap" }, popup.value.exprExplicit && /* @__PURE__ */ React.createElement(InteractiveCode, { fmt: popup.value.exprExplicit }), " :", " ", popup.value.type && /* @__PURE__ */ React.createElement(InteractiveCode, { fmt: popup.value.type })), popup.value.doc && /* @__PURE__ */ React.createElement(React.Fragment, null, /* @__PURE__ */ React.createElement("hr", null), /* @__PURE__ */ React.createElement(Markdown, { contents: popup.value.doc }))) : popup.state === "rejected" ? /* @__PURE__ */ React.createElement(React.Fragment, null, "Error: ", mapRpcError(popup.error).message) : /* @__PURE__ */ React.createElement(React.Fragment, null, "Loading.."));
}
function SelectedExpr({ tag }) {
  const rs = useRpcSession();
  const popup = useAsync(() => InteractiveDiagnostics_infoToInteractive(rs, tag.info.info), [rs, tag.info.info]);
  return /* @__PURE__ */ React.createElement("div", { className: "font-code pre-wrap", "data-location": tag.loc ? JSON.stringify(tag.loc) : void 0 }, /* @__PURE__ */ React.createElement("span", { style: { opacity: 0.7 }, title: tag.loc ? JSON.stringify(tag.loc) : void 0 }, tagLabel(tag)), ": ", popup.state === "resolved" && popup.value.exprExplicit ? /* @__PURE__ */ React.createElement(InteractiveCode, { fmt: popup.value.exprExplicit }) : popup.state === "rejected" ? `Error: ${mapRpcError(popup.error).message}` : "...");
}
var MathLine = React.memo(function MathLine2({ source }) {
  return /* @__PURE__ */ React.createElement(Markdown, { contents: source });
});
var SHOW_DELAY = 500;
var HIDE_DELAY = 300;
var STYLE = `
.lean-tex-display .lean-tex-copy { opacity: 0; transition: opacity 0.1s; }
.lean-tex-display:hover .lean-tex-copy { opacity: 0.6; }
.lean-tex-display .lean-tex-copy:hover { opacity: 1; }
`;
function LatexDisplay({ lines, mvarId, pos }) {
  const ec = React.useContext(EditorContext);
  const rs = useRpcSession();
  const { sources, plain, tags } = React.useMemo(() => buildLatex(lines, mvarId), [lines, mvarId]);
  const rootRef = React.useRef(null);
  const mathRef = React.useRef(null);
  const uid = "leantex" + React.useId().replace(/[^a-zA-Z0-9]/g, "");
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
  const latest = React.useRef({ tags, rs, ec, selected });
  latest.current = { tags, rs, ec, selected };
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
      setKeySelected(tags[id].key, (on) => !on);
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
      if (e._leanTexInTooltip) return;
      if (e.target instanceof Element && e.target.tagName === "HTML") return;
      setNoDefTip(void 0);
      const math = mathRef.current;
      const id = math && e.target instanceof Node && math.contains(e.target) ? tagIdAt(e.clientX, e.clientY, math) : void 0;
      setTips((ts) => ts.filter((t) => id !== void 0 && tagContains(math, t.id, id)));
    };
    document.addEventListener("pointerdown", onPointerDownAnywhere);
    return () => document.removeEventListener("pointerdown", onPointerDownAnywhere);
  }, [anyTooltip]);
  const onContextMenu = (e) => {
    const id = tagIdAt(e.clientX, e.clientY, mathRef.current);
    const context = { interactiveCodeTagId: "", selectableLocationId: "", unselectableLocationId: "" };
    if (id !== void 0) {
      const key = tags[id].key;
      context.interactiveCodeTagId = `${uid}|${id}`;
      if (selected.includes(key)) context.unselectableLocationId = `${uid}|${key}`;
      else context.selectableLocationId = `${uid}|${key}`;
    }
    e.currentTarget.setAttribute("data-vscode-context", JSON.stringify(context));
    setTips([]);
  };
  React.useEffect(() => {
    const h = ec.events.clickedContextMenu.on((action) => {
      if (action.entry === "unselectAll" && action.id === uid) {
        setSelected([]);
        return;
      }
      const sep = action.id.indexOf("|");
      if (sep < 0 || action.id.slice(0, sep) !== uid) return;
      const arg = action.id.slice(sep + 1);
      if (action.entry === "goToDefinition") void execGoTo(parseInt(arg), true);
      else if (action.entry === "select") setKeySelected(arg, true);
      else if (action.entry === "unselect") setKeySelected(arg, false);
    });
    return () => h.dispose();
  }, [ec, uid, execGoTo, setKeySelected]);
  const selectedIds = tags.filter((t) => selected.includes(t.key)).map((t) => t.id);
  const underline = hover !== void 0 && hover.ctrl && !!goTo.current.get(hover.id);
  const [boxes, setBoxes] = React.useState([]);
  const [layoutVersion, setLayoutVersion] = React.useState(0);
  React.useEffect(() => {
    const root = rootRef.current;
    if (!root || typeof ResizeObserver === "undefined") return;
    const obs = new ResizeObserver(() => setLayoutVersion((v) => v + 1));
    obs.observe(root);
    return () => obs.disconnect();
  }, []);
  const highlightKey = JSON.stringify([selectedIds, hover?.id, underline]);
  React.useLayoutEffect(() => {
    const root = rootRef.current;
    if (!root) return;
    const highlights = selectedIds.map((id) => ({
      id,
      className: "highlight-selected"
    }));
    if (hover !== void 0) highlights.push({ id: hover.id, className: "highlight" });
    if (underline && hover !== void 0) highlights.push({ id: hover.id, underline: true });
    setBoxes(computeBoxes(root, highlights));
  }, [highlightKey, sources, layoutVersion]);
  const selectedTags = selected.map((key) => tags.find((t) => t.key === key)).filter((t) => t !== void 0);
  return /* @__PURE__ */ React.createElement(
    "div",
    {
      ref: rootRef,
      className: "lean-tex-display",
      style: { position: "relative" },
      "data-vscode-context": JSON.stringify(selected.length > 0 ? { selectedLocationsId: uid } : {}),
      "data-selected-locations": JSON.stringify(selectedTags.flatMap((t) => t.loc ? [t.loc] : []))
    },
    /* @__PURE__ */ React.createElement("style", null, STYLE),
    boxes.map((b) => /* @__PURE__ */ React.createElement(
      "div",
      {
        key: b.key,
        className: b.className,
        style: {
          position: "absolute",
          left: b.left,
          top: b.underline ? b.top + b.height - 1 : b.top,
          width: b.width,
          height: b.underline ? 1 : b.height,
          backgroundColor: b.underline ? "var(--vscode-editor-foreground)" : void 0,
          pointerEvents: "none",
          zIndex: 0
        }
      }
    )),
    /* @__PURE__ */ React.createElement(
      "div",
      {
        ref: mathRef,
        style: { position: "relative", zIndex: 1, cursor: hover !== void 0 ? "pointer" : void 0 },
        onPointerMove,
        onPointerLeave,
        onPointerDown,
        onMouseDown,
        onClick,
        onContextMenu
      },
      sources.map((source, i) => /* @__PURE__ */ React.createElement(MathLine, { key: i, source }))
    ),
    /* @__PURE__ */ React.createElement(
      "a",
      {
        className: "lean-tex-copy link pointer codicon codicon-copy",
        title: "Copy LaTeX",
        style: { position: "absolute", top: 0, right: 0, zIndex: 2 },
        onClick: () => void ec.api.copyToClipboard(plain)
      }
    ),
    tips.map(
      (t) => tags[t.id] && /* @__PURE__ */ React.createElement(
        Tooltip,
        {
          key: t.id,
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
        /* @__PURE__ */ React.createElement(TypePopupContents, { info: tags[t.id].info })
      )
    ),
    noDefTip !== void 0 && /* @__PURE__ */ React.createElement(Tooltip, { anchor: () => tagRect(mathRef.current, noDefTip), onClick: () => setNoDefTip(void 0) }, "No definition found for this subexpression"),
    selectedTags.length > 0 && /* @__PURE__ */ React.createElement("div", { className: "mt2", style: { position: "relative", zIndex: 1 } }, /* @__PURE__ */ React.createElement("div", { style: { opacity: 0.7 } }, "Selected (shift-click to toggle)", " ", /* @__PURE__ */ React.createElement("a", { className: "link pointer", onClick: () => setSelected([]) }, "clear")), selectedTags.map((tag) => /* @__PURE__ */ React.createElement(SelectedExpr, { key: tag.key, tag })))
  );
}
export {
  LatexDisplay as default
};
