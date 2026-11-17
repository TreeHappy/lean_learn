// Regenerates the figures in docs/figures with the Catppuccin Mocha palette.
// Run: node docs/figures/gen-figures.mjs
import { writeFileSync } from "node:fs";

const C = {
  surface0: "#313244", overlay: "#6c7086", subtext: "#a6adc8", text: "#cdd6f4",
  red: "#f38ba8", peach: "#fab387", yellow: "#f9e2af", green: "#a6e3a1",
  teal: "#94e2d5", sky: "#89dceb", blue: "#89b4fa", lavender: "#b4befe", mauve: "#cba6f7",
};
const FONT = `font-family="sans-serif" font-size="14"`;

const write = (name, body, w, h) =>
  writeFileSync(new URL(name, import.meta.url),
    `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${w} ${h}" ${FONT}>\n${body}\n</svg>\n`);

/* ============================================================
   1. heightmap-lift: UV plane  →  mesh graph (proper axonometry)
   ============================================================ */
{
  const N = 4, M = 3;
  // bump height on the graph
  const h = (x, y) => 1.15 * Math.exp(-((x - 2) ** 2 + (y - 1.5) ** 2) / 1.1);
  // oblique projection of (x, y, z)
  const P = (x, y, z) => [380 + 40 * x + 18 * y, 232 - 16 * y - 30 * z];
  const pt = (a) => a.map((p) => p.map((v) => v.toFixed(1)).join(",")).join(" ");

  let s = "";
  // --- UV plane (left), same projection flattened ---
  const Q = (x, y) => [40 + 40 * x + 18 * y, 190 - 16 * y];
  const corners = pt([Q(0, 0), Q(N, 0), Q(N, M), Q(0, M)]);
  s += `<polygon points="${corners}" fill="${C.blue}" fill-opacity="0.12" stroke="${C.blue}" stroke-width="2"/>\n`;
  let grid = "";
  for (let i = 1; i < N; i++) grid += `<line x1="${Q(i,0)[0]}" y1="${Q(i,0)[1]}" x2="${Q(i,M)[0]}" y2="${Q(i,M)[1]}"/>`;
  for (let j = 1; j < M; j++) grid += `<line x1="${Q(0,j)[0]}" y1="${Q(0,j)[1]}" x2="${Q(N,j)[0]}" y2="${Q(N,j)[1]}"/>`;
  s += `<g stroke="${C.overlay}" stroke-width="0.8" opacity="0.6">${grid}</g>\n`;
  const [ux, uy] = Q(2, 1.5);
  s += `<circle cx="${ux}" cy="${uy}" r="5.5" fill="${C.red}"/>\n`;
  s += `<text x="147" y="228" text-anchor="middle" fill="${C.subtext}">UV / parameter plane (x, y)</text>\n`;
  s += `<text x="147" y="246" text-anchor="middle" fill="${C.overlay}" font-size="12">the bullet's position lives here</text>\n`;

  // --- lift arrow ---
  s += `<g stroke="${C.subtext}" stroke-width="2" fill="${C.subtext}">
    <line x1="268" y1="160" x2="328" y2="160"/>
    <polygon points="328,154 340,160 328,166"/>
  </g>\n<text x="304" y="146" text-anchor="middle" fill="${C.subtext}">lift</text>\n`;

  // --- mesh graph (right): quads painted back-to-front ---
  for (let j = M - 1; j >= 0; j--) {
    for (let i = 0; i < N; i++) {
      const quad = [P(i, j + 1, h(i, j + 1)), P(i + 1, j + 1, h(i + 1, j + 1)),
                    P(i + 1, j, h(i + 1, j)), P(i, j, h(i, j))];
      s += `<polygon points="${pt(quad)}" fill="${C.blue}" fill-opacity="0.14" stroke="${C.blue}" stroke-width="1.1" stroke-opacity="0.85"/>\n`;
    }
  }
  // lifted point + stem to its UV base
  const [bx, by] = P(2, 1.5, 0), [px, py] = P(2, 1.5, h(2, 1.5));
  s += `<line x1="${bx}" y1="${by}" x2="${px}" y2="${py}" stroke="${C.red}" stroke-width="1.2" stroke-dasharray="3 3" opacity="0.7"/>\n`;
  s += `<circle cx="${px}" cy="${py}" r="5.5" fill="${C.red}"/>\n`;
  s += `<text x="497" y="262" text-anchor="middle" fill="${C.subtext}">the mesh graph h: (x, y) ↦ (x, y, h(x,y))</text>\n`;
  s += `<text x="497" y="280" text-anchor="middle" fill="${C.overlay}" font-size="12">same red point, now displaced along +z</text>\n`;
  write("heightmap-lift.svg", s, 720, 290);
}

/* ============================================================
   2. geodesic-rule
   ============================================================ */
write("geodesic-rule.svg", `
  <polygon points="60,230 360,230 500,110 200,110" fill="${C.teal}" fill-opacity="0.15" stroke="${C.teal}" stroke-width="2"/>
  <path d="M 110 215 Q 260 150 430 140" fill="none" stroke="${C.red}" stroke-width="3"/>
  <circle cx="233" cy="172" r="6" fill="${C.peach}"/>
  <g stroke="${C.blue}" stroke-width="3" fill="${C.blue}">
    <line x1="233" y1="172" x2="308" y2="151"/>
    <polygon points="314,150 303,159 298,149"/>
  </g>
  <text x="322" y="148" fill="${C.blue}">velocity v (in the surface)</text>
  <g stroke="${C.mauve}" stroke-width="3" fill="${C.mauve}">
    <line x1="233" y1="172" x2="255" y2="112"/>
    <polygon points="259,109 258,124 250,120"/>
  </g>
  <text x="270" y="92" fill="${C.mauve}">acceleration ⟂ surface (along normal)</text>
  <text x="360" y="270" text-anchor="middle" fill="${C.subtext}">the rule: the 3D acceleration of graph h γ(t) may only point along normal h γ(t)</text>
  <text x="360" y="290" text-anchor="middle" fill="${C.overlay}" font-size="12">projected into UV space this is exactly γ̈ = -(G⁻¹ ((vᵀ H v) ∇h))</text>`, 720, 300);

/* ============================================================
   3. distorted-map
   ============================================================ */
write("distorted-map.svg", `
  <g transform="translate(30,20)">
    <rect x="0" y="0" width="260" height="200" fill="${C.blue}" fill-opacity="0.12" stroke="${C.blue}" stroke-width="2"/>
    <g stroke="${C.overlay}" stroke-width="0.8" opacity="0.6">
      <line x1="65" y1="0" x2="65" y2="200"/><line x1="130" y1="0" x2="130" y2="200"/><line x1="195" y1="0" x2="195" y2="200"/>
      <line x1="0" y1="50" x2="260" y2="50"/><line x1="0" y1="100" x2="260" y2="100"/><line x1="0" y1="150" x2="260" y2="150"/>
    </g>
    <path d="M 30 170 Q 130 40 230 170" fill="none" stroke="${C.red}" stroke-width="3"/>
    <circle cx="30" cy="170" r="5" fill="${C.red}"/><circle cx="230" cy="170" r="5" fill="${C.red}"/>
    <text x="130" y="225" text-anchor="middle" fill="${C.subtext}">UV map: the geodesic bends</text>
    <text x="130" y="244" text-anchor="middle" fill="${C.overlay}" font-size="12">like a great-circle route on a flat map</text>
  </g>
  <g stroke="${C.subtext}" stroke-width="2" fill="${C.subtext}">
    <line x1="330" y1="120" x2="388" y2="120"/>
    <polygon points="388,114 400,120 388,126"/>
  </g>
  <g transform="translate(420,20)">
    <polygon points="20,180 240,180 330,100 110,100" fill="${C.teal}" fill-opacity="0.15" stroke="${C.teal}" stroke-width="2"/>
    <path d="M 60 165 Q 165 90 280 160" fill="none" stroke="${C.red}" stroke-width="3"/>
    <circle cx="60" cy="165" r="5" fill="${C.red}"/><circle cx="280" cy="160" r="5" fill="${C.red}"/>
    <text x="175" y="225" text-anchor="middle" fill="${C.subtext}">on the surface: as straight as possible</text>
    <text x="175" y="244" text-anchor="middle" fill="${C.overlay}" font-size="12">zero tangential acceleration, glued to the surface</text>
  </g>`, 720, 280);

/* ============================================================
   4. euler-drift
   ============================================================ */
write("euler-drift.svg", `
  <path d="M 60 190 Q 360 60 660 60" fill="none" stroke="${C.overlay}" stroke-width="6" opacity="0.45"/>
  <path d="M 90 177 L 200 132 L 310 96 L 420 68 L 530 49"
        fill="none" stroke="${C.red}" stroke-width="3" stroke-dasharray="7 5"/>
  <g stroke="${C.blue}" stroke-width="2.5" fill="${C.blue}">
    <line x1="90" y1="177" x2="148" y2="154"/><polygon points="150,152 139,162 135,152"/>
    <line x1="200" y1="132" x2="253" y2="114"/><polygon points="255,113 244,122 240,112"/>
    <line x1="310" y1="96" x2="363" y2="86"/><polygon points="365,85 353,93 349,83"/>
  </g>
  <g fill="${C.red}">
    <circle cx="90" cy="177" r="5"/><circle cx="200" cy="132" r="5"/>
    <circle cx="310" cy="96" r="5"/><circle cx="420" cy="68" r="5"/>
    <circle cx="530" cy="49" r="5"/>
  </g>
  <text x="360" y="225" text-anchor="middle" fill="${C.subtext}">eulerStep: sample the slope once, run straight — the dashed shot drifts off the true path (grey)</text>`, 720, 240);

/* ============================================================
   5. rk4-slopes
   ============================================================ */
write("rk4-slopes.svg", `
  <g font-size="13">
  <path d="M 60 190 Q 360 60 660 60" fill="none" stroke="${C.overlay}" stroke-width="6" opacity="0.45"/>
  <path d="M 90 177 Q 280 105 420 81" fill="none" stroke="${C.red}" stroke-width="3"/>
  <circle cx="90" cy="177" r="5" fill="${C.red}"/>
  <circle cx="420" cy="81" r="5" fill="${C.red}"/>
  <g stroke-linecap="round">
    <g stroke="${C.blue}" stroke-width="3" fill="${C.blue}">
      <line x1="90" y1="177" x2="152" y2="150"/><polygon points="158,147 147,158 143,148"/>
    </g>
    <text x="40" y="215" fill="${C.blue}">k₁ = field h s   (start)</text>
    <g stroke="${C.green}" stroke-width="3" fill="${C.green}">
      <line x1="267" y1="117" x2="329" y2="101"/><polygon points="335,98 324,107 320,97"/>
    </g>
    <text x="215" y="225" fill="${C.green}">k₂ = field h (s + (dt/2) k₁)</text>
    <g stroke="${C.yellow}" stroke-width="3" fill="${C.yellow}">
      <line x1="285" y1="111" x2="350" y2="93"/><polygon points="356,90 345,99 341,89"/>
    </g>
    <text x="300" y="70" fill="${C.yellow}">k₃ = field h (s + (dt/2) k₂)</text>
    <g stroke="${C.mauve}" stroke-width="3" fill="${C.mauve}">
      <line x1="420" y1="81" x2="486" y2="64"/><polygon points="492,62 481,70 477,60"/>
    </g>
    <text x="450" y="110" fill="${C.mauve}">k₄ = field h (s + dt k₃)   (end)</text>
  </g>
  <text x="360" y="250" text-anchor="middle" fill="${C.subtext}">rk4Step: sₙ₊₁ = s + (dt/6)(k₁ + 2k₂ + 2k₃ + k₄) — the step lands on the true path (grey)</text>
  </g>`, 720, 260);

/* ============================================================
   6. surface-ingredients: plane point, lift, tangents, normal
   ============================================================ */
{
  // a gentle bump surface, drawn as a wireframe patch
  const h = (x, y) => 1.6 * Math.exp(-((x - 1.2) ** 2 + (y - 1.0) ** 2) / 1.2);
  const P = (x, y, z) => [360 + 42 * x + 20 * y, 150 - 14 * y - 34 * z];
  const px = 0.35, py = 0.25, pz = h(px, py);
  // tangents at the point
  const eps = 1e-4;
  const hx = (h(px + eps, py) - h(px - eps, py)) / (2 * eps);
  const hy = (h(px, py + eps) - h(px, py - eps)) / (2 * eps);
  const arrow = (from, to, color, label, lx, ly, anchor) => {
    const dx = to[0] - from[0], dy = to[1] - from[1];
    const L = Math.hypot(dx, dy), ux = dx / L, uy = dy / L;
    const tipx = from[0] + dx + 9 * ux, tipy = from[1] + dy + 9 * uy;
    return `<g stroke="${color}" stroke-width="3" fill="${color}">
      <line x1="${from[0]}" y1="${from[1]}" x2="${to[0]}" y2="${to[1]}"/>
      <polygon points="${tipx.toFixed(1)},${tipy.toFixed(1)} ${(to[0] + 4.5 * uy).toFixed(1)},${(to[1] - 4.5 * ux).toFixed(1)} ${(to[0] - 4.5 * uy).toFixed(1)},${(to[1] + 4.5 * ux).toFixed(1)}"/>
    </g>
    <text x="${lx}" y="${ly}" fill="${color}" text-anchor="${anchor}">${label}</text>\n`;
  };
  const [bx, by] = P(px, py, 0), [sx, sy] = P(px, py, pz);
  let s = "";
  // wireframe patch, quads back-to-front
  const N = 4, M = 3;
  for (let j = M - 1; j >= 0; j--) {
    for (let i = 0; i < N; i++) {
      const quad = [P(i, j + 1, h(i, j + 1)), P(i + 1, j + 1, h(i + 1, j + 1)),
                    P(i + 1, j, h(i + 1, j)), P(i, j, h(i, j))];
      s += `<polygon points="${quad.map((p) => p.map((v) => v.toFixed(1)).join(",")).join(" ")}"
        fill="${C.blue}" fill-opacity="0.12" stroke="${C.blue}" stroke-width="1" stroke-opacity="0.8"/>\n`;
    }
  }
  // plane patch underneath
  const Q = (x, y) => [360 + 42 * x + 20 * y, 250 - 14 * y];
  const corners = [Q(0, 0), Q(N, 0), Q(N, M), Q(0, M)]
    .map((p) => p.join(",")).join(" ");
  s += `<polygon points="${corners}" fill="none" stroke="${C.overlay}" stroke-width="1.2" stroke-dasharray="4 4" opacity="0.6"/>\n`;
  s += `<circle cx="${bx.toFixed(1)}" cy="${by.toFixed(1)}" r="4" fill="${C.peach}"/>\n`;
  s += `<text x="${(bx + 10).toFixed(1)}" y="${(by + 18).toFixed(1)}" fill="${C.peach}">p = (x, y) in the parameter plane</text>\n`;
  // lift stem
  s += `<line x1="${bx.toFixed(1)}" y1="${by.toFixed(1)}" x2="${sx.toFixed(1)}" y2="${sy.toFixed(1)}" stroke="${C.peach}" stroke-width="1.3" stroke-dasharray="3 3" opacity="0.8"/>\n`;
  s += `<circle cx="${sx.toFixed(1)}" cy="${sy.toFixed(1)}" r="5.5" fill="${C.peach}"/>\n`;
  s += `<text x="${(sx - 150).toFixed(1)}" y="${(sy + 42).toFixed(1)}" fill="${C.peach}">σ(p) = (x, y, h(x,y))</text>\n`;
  // tangents and normal
  const T = (a) => P(px + a, py, pz + a * hx);
  const S = (b) => P(px, py + b, pz + b * hy);
  const tX = T(0.85), tY = S(0.85);
  // unit normal (−hx, −hy, 1), scaled
  const nL = Math.hypot(hx, hy, 1);
  const nz = [(-hx / nL) * 0.75, (-hy / nL) * 0.75, (1 / nL) * 0.75];
  const nrm = P(px + nz[0], py + nz[1], pz + nz[2]);
  s += arrow([sx, sy], tX, C.sky, "tangentX = (1, 0, ∂ₓh)", tX[0] + 12, tX[1] + 4, "start");
  s += arrow([sx, sy], tY, C.green, "tangentY = (0, 1, ∂ᵧh)", tY[0] - 12, tY[1] - 12, "end");
  s += arrow([sx, sy], nrm, C.mauve, "normal = cross(tangentX, tangentY) = (−∂ₓh, −∂ᵧh, 1)", 40, 52, "start");
  s += `<text x="360" y="312" text-anchor="middle" fill="${C.subtext}">the ingredients at a point: the lift σ(p), the two coordinate tangents, and the normal they span</text>\n`;
  write("surface-ingredients.svg", s, 720, 325);
}

console.log("figures regenerated");
