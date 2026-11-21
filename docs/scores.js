import { boundSeries, axis } from "./records.mjs";

const repo = "https://github.com/chongxuren/poisson-fts-public-test";
const svg = document.querySelector("#plot");
const grsCandidateBytes = 756;
const segments = [...document.querySelectorAll("[data-track]")];
const number = new Intl.NumberFormat("en");
const fmt = (v) => (v === null ? "Open" : number.format(v) + " B");
const trackName = {
  "lower-bound": "Lower bound",
  construction: "Construction",
};
const ns = "http://www.w3.org/2000/svg";
let track = "lower-bound";
let ledger, samples, selected, geometry;

function node(tag, attrs, text) {
  const el = document.createElementNS(ns, tag);
  for (const [key, val] of Object.entries(attrs)) el.setAttribute(key, val);
  if (text !== undefined) el.textContent = text;
  return el;
}
function link(label, url) {
  const a = document.createElement("a");
  a.textContent = label;
  a.href = repo + url;
  return a;
}
function avatar(name) {
  const icon = document.createElement("canvas");
  icon.className = "avatar";
  icon.width = icon.height = 9;
  icon.setAttribute("aria-hidden", "true");
  const c = icon.getContext("2d");
  let hash = 2166136261;
  for (const letter of name)
    hash = Math.imul(hash ^ letter.charCodeAt(0), 16777619) >>> 0;
  const hue = hash % 360;
  c.fillStyle = "hsl(" + hue + " 32% 22%)";
  c.fillRect(0, 0, 9, 9);
  c.fillStyle = "hsl(" + hue + " 64% 79%)";
  for (let y = 0; y < 5; y++)
    for (let x = 0; x < 3; x++)
      if (hash & (1 << (3 * y + x))) {
        c.fillRect(2 + x, 2 + y, 1, 1);
        c.fillRect(6 - x, 2 + y, 1, 1);
      }
  return icon;
}
function team(name) {
  const el = document.createElement("span");
  el.className = "team";
  el.append(avatar(name), name);
  return el;
}
function cell(row, content, cls = "") {
  const td = row.insertCell();
  td.className = cls;
  td.append(content);
}
function empty(body, count, text) {
  const td = body.insertRow().insertCell();
  td.colSpan = count;
  td.className = "empty";
  td.textContent = text;
}
function drawBoard() {
  segments.forEach((btn) =>
    btn.setAttribute("aria-pressed", String(btn.dataset.track === track)),
  );
  const rows = ledger.rankings[track];
  document.querySelector("#team-count").textContent =
    rows.length + " " + (rows.length === 1 ? "team" : "teams");
  document.querySelector("#track-hint").textContent =
    track === "lower-bound"
      ? "Higher byte bounds rank first."
      : "Smaller signatures rank first.";
  const body = document.querySelector("#ranks");
  body.replaceChildren();
  if (!rows.length)
    empty(
      body,
      4,
      track === "construction"
        ? "The first certified construction will open this track."
        : "Awaiting the first qualifying lower-bound record.",
    );
  for (const [i, r] of rows.entries()) {
    const tr = body.insertRow();
    if (i === 0) tr.className = "leader";
    cell(tr, String(i + 1).padStart(2, "0"), "rank");
    cell(tr, team(r.team));
    cell(tr, link(fmt(r.bound_bytes), "/pull/" + r.pr), "num bytes");
    cell(
      tr,
      r.delta === null ? "First" : "+" + number.format(r.delta) + " B",
      "num gain",
    );
  }
}
function drawHistory() {
  const body = document.querySelector("#history");
  body.replaceChildren();
  if (!ledger.history.length)
    empty(body, 5, "Awaiting the first verified submission.");
  for (const r of [...ledger.history].reverse()) {
    const tr = body.insertRow();
    cell(tr, link("#" + r.pr + " · " + r.id, "/pull/" + r.pr));
    cell(tr, r.team);
    cell(tr, trackName[r.track]);
    cell(tr, fmt(r.bound_bytes), "num bytes");
    cell(tr, link("Verified", "/actions/runs/" + r.run), "num");
  }
}
function inspect(index) {
  if (!geometry || !samples.length) return;
  selected = Math.max(0, Math.min(samples.length - 1, index));
  const s = samples[selected],
    x = geometry.x(selected);
  const guide = svg.querySelector(".cursor");
  guide.setAttribute("x1", x);
  guide.setAttribute("x2", x);
  for (const key of ["lower", "upper"]) {
    const dot = svg.querySelector(".point-" + key);
    dot.style.display = s[key] === null ? "none" : "";
    if (s[key] !== null) {
      dot.setAttribute("cx", x);
      dot.setAttribute("cy", geometry.y(s[key]));
    }
  }
  const upper = ledger.best.construction === null
    ? "Proposed upper " + fmt(grsCandidateBytes)
    : "Certified upper " + fmt(s.upper);
  const label = s.label + " · Lower " + fmt(s.lower) + " · " + upper;
  document.querySelector("#readout").textContent = label;
  svg.querySelector("desc").textContent =
    label + ". Use the left and right arrow keys to inspect submissions.";
}

function drawPlot() {
  const w = Math.round(svg.getBoundingClientRect().width);
  if (!samples?.length || w < 30) return;
  const h = 161,
    left = 39,
    right = w - 20,
    top = 12,
    bottom = h - 27;
  svg.setAttribute("viewBox", "0 0 " + w + " " + h);
  svg.setAttribute("tabindex", "0");
  const values = samples.flatMap((s) => [s.lower, s.upper]);
  const showCandidate = ledger.best.construction === null;
  if (showCandidate) values.push(grsCandidateBytes);
  const scale = axis(values);
  const x = (i) =>
    left +
    (samples.length === 1 ? 0 : ((right - left) * i) / (samples.length - 1));
  const y = (v) =>
    bottom - ((v - scale.min) * (bottom - top)) / (scale.max - scale.min);
  geometry = { left, right, x, y };
  svg.replaceChildren(
    node(
      "title",
      { id: "plot-title" },
      "Signature-size records by submission order",
    ),
    node("desc", { id: "plot-desc" }, ""),
  );
  const defs = node("defs", {}),
    gradient = node("linearGradient", {
      id: "lower-fill",
      x1: "0",
      y1: "0",
      x2: "0",
      y2: "1",
    });
  gradient.append(
    node("stop", {
      offset: "0%",
      "stop-color": "#8895ff",
      "stop-opacity": 0.23,
    }),
    node("stop", {
      offset: "100%",
      "stop-color": "#8895ff",
      "stop-opacity": 0.015,
    }),
  );
  defs.append(gradient);
  svg.append(defs);
  const label = (posX, posY, value, anchor = "start") =>
    node(
      "text",
      {
        x: posX,
        y: posY,
        "text-anchor": anchor,
        fill: "#acb6cf",
        "font-family": "ui-monospace, monospace",
        "font-size": 11,
      },
      value,
    );
  for (let v = scale.min; v <= scale.max; v += scale.step) {
    svg.append(
      node("line", {
        x1: left,
        y1: y(v),
        x2: right,
        y2: y(v),
        stroke: "#31394e",
        "stroke-dasharray": "3 5",
      }),
    );
    const tick =
      Math.abs(v) >= 10000
        ? Intl.NumberFormat("en", {
            notation: "compact",
            maximumFractionDigits: 1,
          }).format(v)
        : String(v);
    svg.append(label(left - 7, y(v) + 4, tick, "end"));
  }
  if (showCandidate) {
    svg.append(
      node("line", {
        x1: left,
        y1: y(grsCandidateBytes),
        x2: right,
        y2: y(grsCandidateBytes),
        stroke: "#e5b077",
        "stroke-width": 1.6,
        "stroke-dasharray": "5 5",
      }),
    );
    const proposalLabel = label(
      right - 2,
      y(grsCandidateBytes) < top + 17 ? y(grsCandidateBytes) + 14 : y(grsCandidateBytes) - 5,
      fmt(grsCandidateBytes) + " · GRS-CC proposal",
      "end",
    );
    proposalLabel.setAttribute("fill", "#efc68f");
    svg.append(proposalLabel);
  }
  for (const [key, color] of [
    ["lower", "#a3aaff"],
    ["upper", "#7de0bf"],
  ]) {
    let path = "",
      first = -1,
      last = -1,
      prior = null;
    const markers = [];
    for (let i = 0; i < samples.length; i++) {
      const v = samples[i][key];
      if (v === null) continue;
      if (first < 0) {
        first = i;
        path = "M " + x(i) + " " + y(v);
      } else if (v !== prior) {
        path += " H " + x(i) + " V " + y(v);
      }
      if (v !== prior) markers.push([i, v]);
      last = i;
      prior = v;
    }
    if (first < 0) continue;
    path += " H " + x(last);
    if (key === "lower")
      svg.append(
        node("path", {
          d: path + " V " + bottom + " H " + x(first) + " Z",
          fill: "url(#lower-fill)",
        }),
      );
    svg.append(
      node("path", {
        d: path,
        stroke: color,
        "stroke-width": 2.6,
        fill: "none",
        "stroke-linejoin": "round",
      }),
    );
    if (key === "lower" && showCandidate && samples.length <= 5) {
      for (const [i, v] of markers) {
        const anchor = i === 0 ? "start" : i === samples.length - 1 ? "end" : "middle";
        const text = label(x(i), y(v) - 9, fmt(v), anchor);
        text.setAttribute("fill", color);
        svg.append(text);
      }
    }
    if (markers.length <= 35)
      for (const [i, v] of markers)
        svg.append(
          node("circle", {
            cx: x(i),
            cy: y(v),
            r: 3,
            fill: color,
            stroke: "#13182a",
            "stroke-width": 1,
          }),
        );
  }
  const n = samples.length,
    middle = Math.floor((n - 1) / 2);
  const indices = w < 360 || n < 3 ? [0, n - 1] : [0, middle, n - 1];
  for (const i of new Set(indices))
    svg.append(
      label(
        x(i),
        h - 4,
        samples[i].label,
        i === 0 ? "start" : i === n - 1 ? "end" : "middle",
      ),
    );
  svg.append(
    node("line", {
      class: "cursor",
      y1: top,
      y2: bottom,
      stroke: "#aeb8de",
      "stroke-opacity": 0.45,
      "stroke-dasharray": "2 3",
    }),
  );
  for (const [key, color] of [
    ["lower", "#a3aaff"],
    ["upper", "#7de0bf"],
  ])
    svg.append(
      node("circle", {
        class: "point-" + key,
        r: 4.5,
        stroke: color,
        "stroke-width": 2,
        fill: "#11172a",
      }),
    );
  inspect(selected ?? n - 1);
}
function pointAt(event) {
  if (!geometry || samples.length < 2) return;
  const pos = event.clientX - svg.getBoundingClientRect().left;
  inspect(
    Math.round(
      ((pos - geometry.left) / (geometry.right - geometry.left)) *
        (samples.length - 1),
    ),
  );
}
svg.addEventListener("pointermove", (e) => {
  if (e.pointerType === "mouse") pointAt(e);
});
svg.addEventListener("pointerdown", pointAt);
svg.addEventListener("keydown", (e) => {
  if (!samples) return;
  const keys = {
    ArrowLeft: selected - 1,
    ArrowRight: selected + 1,
    Home: 0,
    End: samples.length - 1,
  };
  if (e.key in keys) {
    e.preventDefault();
    inspect(keys[e.key]);
  }
});
segments.forEach((btn) =>
  btn.addEventListener("click", () => {
    track = btn.dataset.track;
    if (ledger) drawBoard();
  }),
);
new ResizeObserver(drawPlot).observe(svg.parentElement);

function display(data, source) {
  ledger = data;
  samples = boundSeries(data);
  selected = samples.length - 1;
  document.querySelector("#lower").textContent = fmt(data.best["lower-bound"]);
  const hasUpper = data.best.construction !== null;
  document.querySelector("#upper").textContent = fmt(data.best.construction ?? grsCandidateBytes);
  document.querySelector("#upper-label").textContent = hasUpper ? "Certified upper bound" : "Proposed upper bound";
  document.querySelector("#upper-swatch").className = hasUpper ? "swatch green" : "swatch proposed";
  document.querySelector("#bounds-note").textContent = hasUpper
    ? "The rehearsal opened at 97 B. The upper curve begins at the first certified construction."
    : "The rehearsal opened at 97 B. The organizer proved 99 B. The dashed line shows the size of the GRS-CC candidate pending certification.";
  document.querySelector("#sync").textContent = source;
  drawBoard();
  drawHistory();
  drawPlot();
}
async function load() {
  const local = fetch("./scores.json", { cache: "no-cache" }).then((r) => {
    if (!r.ok) throw Error();
    return r.json();
  });
  const live = fetch(
    "https://api.github.com/repos/chongxuren/poisson-fts-public-test/contents/docs/scores.json?ref=main",
    {
      headers: { Accept: "application/vnd.github.raw+json" },
      cache: "no-cache",
    },
  ).then((r) => {
    if (!r.ok) throw Error();
    return r.json();
  });
  let current = false;
  await Promise.allSettled([
    local.then((data) => {
      if (!current) display(data, "Scores from the published snapshot.");
    }),
    live.then((data) => {
      display(data, "Scores from the verified main-branch ledger.");
      current = true;
    }),
  ]);
  if (!ledger)
    document.querySelector("#sync").textContent =
      "Scores unavailable. Open the score ledger to check the records.";
}
load();
