// src/latexDisplay.tsx
import * as React from "react";
import {
  InteractiveCode,
  InteractiveDiagnostics_infoToInteractive,
  Markdown,
  mapRpcError,
  useAsync,
  useRpcSession
} from "@leanprover/infoview";
function buildLatex(lines) {
  const tags = [];
  const sources = lines.map((line) => {
    const tex = line.map((part) => {
      const ids = /* @__PURE__ */ new Map();
      const go = (tt) => {
        if ("text" in tt) return tt.text;
        if ("append" in tt) return tt.append.map(go).join("");
        const [info, sub] = tt.tag;
        const key = info.subexprPos ?? "/";
        let id = ids.get(key);
        if (id === void 0) {
          id = tags.length;
          ids.set(key, id);
          tags.push({ id, info, part });
        }
        return `\\class{lean-se-${id}}{${go(sub)}}`;
      };
      return go(part.latex);
    }).join("");
    return `$\\displaystyle ${tex}$`;
  });
  return { sources, tags };
}
function tagLocation(tag, mvarId) {
  const { part } = tag;
  const pos = tag.info.subexprPos ?? "/";
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
function tagIdOf(el) {
  const m = /(?:^|\s)lean-se-(\d+)(?:\s|$)/.exec(el.getAttribute("class") ?? "");
  return m ? parseInt(m[1]) : void 0;
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
      const id = tagIdOf(el);
      if (id !== void 0) {
        best = id;
        bestArea = area;
      }
    }
  });
  return best;
}
var MathLine = React.memo(function MathLine2({ source }) {
  return /* @__PURE__ */ React.createElement(Markdown, { contents: source });
});
function computeBoxes(root, highlights) {
  const rootRect = root.getBoundingClientRect();
  const boxes = [];
  for (const [id, className] of highlights) {
    root.querySelectorAll(`.lean-se-${id}`).forEach((el, i) => {
      const r = el.getBoundingClientRect();
      boxes.push({
        key: `${className}-${id}-${i}`,
        left: r.left - rootRect.left,
        top: r.top - rootRect.top,
        width: r.width,
        height: r.height,
        className
      });
    });
  }
  return boxes;
}
function InfoPopupContents({ info }) {
  const rs = useRpcSession();
  const popup = useAsync(() => InteractiveDiagnostics_infoToInteractive(rs, info.info), [rs, info]);
  if (popup.state === "loading") return /* @__PURE__ */ React.createElement("div", { className: "tooltip-code-content" }, "Loading...");
  if (popup.state === "rejected")
    return /* @__PURE__ */ React.createElement("div", { className: "tooltip-code-content" }, "Error: ", mapRpcError(popup.error).message);
  const { type, exprExplicit, doc } = popup.value;
  return /* @__PURE__ */ React.createElement("div", { className: "tooltip-code-content" }, type && /* @__PURE__ */ React.createElement("div", { className: "font-code tl pre-wrap" }, exprExplicit && /* @__PURE__ */ React.createElement(InteractiveCode, { fmt: exprExplicit }), " : ", /* @__PURE__ */ React.createElement(InteractiveCode, { fmt: type })), doc && /* @__PURE__ */ React.createElement(React.Fragment, null, type && /* @__PURE__ */ React.createElement("hr", null), /* @__PURE__ */ React.createElement(Markdown, { contents: doc })));
}
function SelectedExpr({ tag, mvarId }) {
  const rs = useRpcSession();
  const popup = useAsync(() => InteractiveDiagnostics_infoToInteractive(rs, tag.info.info), [rs, tag]);
  const loc = tagLocation(tag, mvarId);
  return /* @__PURE__ */ React.createElement("div", { className: "font-code pre-wrap", "data-location": loc ? JSON.stringify(loc) : void 0 }, /* @__PURE__ */ React.createElement("span", { style: { opacity: 0.7 }, title: loc ? JSON.stringify(loc) : void 0 }, tagLabel(tag)), ": ", popup.state === "resolved" && popup.value.exprExplicit ? /* @__PURE__ */ React.createElement(InteractiveCode, { fmt: popup.value.exprExplicit }) : popup.state === "rejected" ? `Error: ${mapRpcError(popup.error).message}` : "...");
}
var POPUP_OPEN_DELAY = 300;
var POPUP_CLOSE_DELAY = 200;
function LatexDisplay({ lines, mvarId }) {
  const { sources, tags } = React.useMemo(() => buildLatex(lines), [lines]);
  const rootRef = React.useRef(null);
  const mathRef = React.useRef(null);
  const [hovered, setHovered] = React.useState();
  const [selected, setSelected] = React.useState([]);
  const [popup, setPopup] = React.useState();
  React.useEffect(() => {
    setHovered(void 0);
    setSelected([]);
    setPopup(void 0);
  }, [tags]);
  const openTimer = React.useRef();
  const closeTimer = React.useRef();
  const clearTimers = () => {
    window.clearTimeout(openTimer.current);
    window.clearTimeout(closeTimer.current);
  };
  React.useEffect(() => clearTimers, []);
  const scheduleClose = () => {
    window.clearTimeout(closeTimer.current);
    closeTimer.current = window.setTimeout(
      () => setPopup((p) => p?.pinned ? p : void 0),
      POPUP_CLOSE_DELAY
    );
  };
  const hoveredRef = React.useRef();
  const onPointerMove = (e) => {
    const id = tagIdAt(e.clientX, e.clientY, mathRef.current);
    if (id === hoveredRef.current) return;
    hoveredRef.current = id;
    setHovered(id);
    clearTimers();
    if (id === void 0) {
      scheduleClose();
    } else {
      openTimer.current = window.setTimeout(
        () => setPopup((p) => p?.pinned ? p : { id, pinned: false }),
        POPUP_OPEN_DELAY
      );
    }
  };
  const onPointerLeave = () => {
    hoveredRef.current = void 0;
    setHovered(void 0);
    clearTimers();
    scheduleClose();
  };
  const onMouseDown = (e) => {
    if (e.shiftKey && tagIdAt(e.clientX, e.clientY, mathRef.current) !== void 0) e.preventDefault();
  };
  const onClick = (e) => {
    const id = tagIdAt(e.clientX, e.clientY, mathRef.current);
    if (id === void 0) {
      setPopup(void 0);
      return;
    }
    e.stopPropagation();
    if (e.shiftKey) {
      setSelected((sel) => sel.includes(id) ? sel.filter((i) => i !== id) : [...sel, id]);
    } else {
      clearTimers();
      setPopup((p) => p?.id === id && p.pinned ? void 0 : { id, pinned: true });
    }
  };
  const [boxes, setBoxes] = React.useState([]);
  const [layoutVersion, setLayoutVersion] = React.useState(0);
  React.useEffect(() => {
    const root = rootRef.current;
    if (!root || typeof ResizeObserver === "undefined") return;
    const obs = new ResizeObserver(() => setLayoutVersion((v) => v + 1));
    obs.observe(root);
    return () => obs.disconnect();
  }, []);
  const hoverId = hovered ?? popup?.id;
  React.useLayoutEffect(() => {
    const root = rootRef.current;
    if (!root) return;
    const highlights = selected.map((id) => [id, "highlight-selected"]);
    if (hoverId !== void 0) highlights.push([hoverId, "highlight"]);
    setBoxes(computeBoxes(root, highlights));
  }, [hoverId, selected, sources, layoutVersion]);
  const popupTag = popup !== void 0 ? tags[popup.id] : void 0;
  let popupStyle;
  if (popup !== void 0 && rootRef.current) {
    const el = rootRef.current.querySelector(`.lean-se-${popup.id}`);
    if (el) {
      const r = el.getBoundingClientRect();
      const rootRect = rootRef.current.getBoundingClientRect();
      popupStyle = {
        position: "absolute",
        left: Math.max(0, r.left - rootRect.left),
        top: r.bottom - rootRect.top + 4,
        zIndex: 10,
        maxWidth: "40em",
        maxHeight: "20em",
        display: "flex",
        flexDirection: "column",
        minWidth: "10em"
      };
    }
  }
  const selectedTags = selected.map((id) => tags[id]).filter((t) => t !== void 0);
  const selectedLocations = selectedTags.map((t) => tagLocation(t, mvarId)).filter((l) => l !== void 0);
  return /* @__PURE__ */ React.createElement(
    "div",
    {
      ref: rootRef,
      className: "lean-tex-display",
      style: { position: "relative" },
      "data-selected-locations": JSON.stringify(selectedLocations)
    },
    boxes.map((b) => /* @__PURE__ */ React.createElement(
      "div",
      {
        key: b.key,
        className: b.className,
        style: {
          position: "absolute",
          left: b.left,
          top: b.top,
          width: b.width,
          height: b.height,
          pointerEvents: "none",
          borderRadius: 2,
          zIndex: 0
        }
      }
    )),
    /* @__PURE__ */ React.createElement(
      "div",
      {
        ref: mathRef,
        style: { position: "relative", zIndex: 1, cursor: hovered !== void 0 ? "pointer" : void 0 },
        onPointerMove,
        onPointerLeave,
        onMouseDown,
        onClick
      },
      sources.map((source, i) => /* @__PURE__ */ React.createElement(MathLine, { key: i, source }))
    ),
    popupTag && popupStyle && /* @__PURE__ */ React.createElement(
      "div",
      {
        className: "tooltip",
        style: popupStyle,
        onPointerEnter: () => window.clearTimeout(closeTimer.current),
        onPointerLeave: scheduleClose
      },
      /* @__PURE__ */ React.createElement("div", { className: "tooltip-content" }, /* @__PURE__ */ React.createElement(InfoPopupContents, { info: popupTag.info }))
    ),
    selectedTags.length > 0 && /* @__PURE__ */ React.createElement("div", { className: "mt2", style: { position: "relative", zIndex: 1 } }, /* @__PURE__ */ React.createElement("div", { style: { opacity: 0.7 } }, "Selected (shift-click to toggle)", " ", /* @__PURE__ */ React.createElement("a", { className: "link pointer", onClick: () => setSelected([]) }, "clear")), selectedTags.map((tag) => /* @__PURE__ */ React.createElement(SelectedExpr, { key: tag.id, tag, mvarId })))
  );
}
export {
  LatexDisplay as default
};
