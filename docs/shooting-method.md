# Shooting Geodesics for Dummies (a 3D graphics programmer's edition)

You know heights, normals, UVs, and physics integrators from games.
Good news: the "shooting method" in `lean/Brane/Shooting.lean` is just
**rolling a marble across a heightmap with an unusual physics rule**.

---

## 1. The surface is a heightmap — you already know this

In graphics, a heightmap is a grid of heights over a UV plane. Here it's the
continuous version: a function `h(x, y)` and the mesh

```
graph h (x, y) = (x, y, h x y)
```

Same thing, no LOD, infinite subdivision:

| Game engine | This file |
|---|---|
| UV space | parameter plane `ℝ²`, coordinates `(x, y)` |
| heightmap texture | `h : ℝ → ℝ → ℝ` |
| displaced mesh | `graph h` |
| vertex normal | `normal h p` (cross product of the two tangents) |

<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 720 260" font-family="sans-serif" font-size="14">
  <!-- UV plane -->
  <g transform="translate(40,60)">
    <rect x="0" y="0" width="160" height="120" fill="#dfe9f3" stroke="#5b7fa6" stroke-width="2"/>
    <g stroke="#9db8d2" stroke-width="1">
      <line x1="40" y1="0" x2="40" y2="120"/><line x1="80" y1="0" x2="80" y2="120"/><line x1="120" y1="0" x2="120" y2="120"/>
      <line x1="0" y1="40" x2="160" y2="40"/><line x1="0" y1="80" x2="160" y2="80"/>
    </g>
    <circle cx="80" cy="60" r="5" fill="#d33"/>
    <text x="80" y="145" text-anchor="middle" fill="#345">UV / parameter plane (x, y)</text>
    <text x="80" y="163" text-anchor="middle" fill="#888" font-size="12">the bullet's position lives here</text>
  </g>
  <!-- arrow -->
  <g stroke="#555" stroke-width="2" fill="#555">
    <line x1="240" y1="120" x2="300" y2="120"/>
    <polygon points="300,114 312,120 300,126"/>
  </g>
  <text x="276" y="108" text-anchor="middle" fill="#555">lift</text>
  <!-- heightmap surface -->
  <g transform="translate(330,30)">
    <polygon points="40,140 240,140 320,60 120,60" fill="#cfe3c8" stroke="#4a7a4a" stroke-width="2"/>
    <g stroke="#7fae7a" stroke-width="1" fill="none">
      <polygon points="85,140 265,140 320,88 140,88" opacity="0.7"/>
      <polygon points="130,140 290,140 320,116 160,116" opacity="0.5"/>
    </g>
    <circle cx="180" cy="102" r="5" fill="#d33"/>
    <text x="180" y="180" text-anchor="middle" fill="#345">the mesh graph h: (x, y) → (x, y, h(x,y))</text>
    <text x="180" y="198" text-anchor="middle" fill="#888" font-size="12">same red point, now displaced along +z</text>
  </g>
</svg>

The whole simulation runs in the **UV plane**. We never integrate in 3D;
we integrate `(x(t), y(t))` and evaluate `h` to get the 3D point. Exactly like
simulating a vehicle on a heightfield: cheap 2D state, 3D render.

---

## 2. The weird physics rule

On a normal heightfield you'd do gravity + friction + collision. Here the
marble obeys one commandment:

> **The acceleration must point exactly along the surface normal. Nothing
> else. No gravity, no friction — just "stay glued to the surface".**

A curve that obeys this rule is a **geodesic**. Intuition: it's the path a
stretched rubber band takes when pinned at both ends and pressed onto the
surface, or the path you'd walk on the terrain feeling no slope, only
curvature.

<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 720 300" font-family="sans-serif" font-size="14">
  <!-- tilted surface -->
  <polygon points="60,230 360,230 500,110 200,110" fill="#cfe3c8" stroke="#4a7a4a" stroke-width="2" opacity="0.9"/>
  <!-- curve on surface -->
  <path d="M 110 215 Q 260 150 430 140" fill="none" stroke="#d33" stroke-width="3"/>
  <circle cx="230" cy="163" r="6" fill="#222"/>
  <!-- tangent velocity -->
  <g stroke="#1a6bb5" stroke-width="3" fill="#1a6bb5">
    <line x1="230" y1="163" x2="310" y2="150"/>
    <polygon points="304,143 322,147 312,160"/>
  </g>
  <text x="322" y="146" fill="#1a6bb5">velocity (in the surface)</text>
  <!-- acceleration along normal -->
  <g stroke="#7a1ab5" stroke-width="3" fill="#7a1ab5">
    <line x1="230" y1="163" x2="255" y2="100"/>
    <polygon points="247,100 261,88 262,106"/>
  </g>
  <text x="270" y="92" fill="#7a1ab5">acceleration ⟂ surface (along normal)</text>
  <text x="360" y="270" text-anchor="middle" fill="#345">the rule: lift the velocity's tip and steer it so acceleration never drags it off the surface</text>
</svg>

### The equation, in engine terms

The acceleration is computed from exactly the matrices you already build
per-vertex:

```text
γ̈ = -(G⁻¹ *ᵥ ((vᵀ H v) • ∇h))
```

Read it like a shader:

| Symbol | Meaning | Where it comes from |
|---|---|---|
| `∇h = (∂ₓh, ∂ᵧh)` | gradient of the heightmap at the ball's UV | `gradientVec` — like sampling the height gradient |
| `H` | Hessian `[[h_xx, h_xy], [h_yx, h_yy]]` | `hessian` — second derivative texture |
| `vᵀ H v` | how much the surface curves *along the direction you're moving* | `hessQuad` — directional curvature |
| `G = JᵀJ` | Gram matrix — how the UV plane is stretched onto the surface | `gramMatrix` |
| `G⁻¹` | un-stretch: convert "surface constraints" back to UV space | `Matrix.inv` |

So the whole RHS says: *"the surface curves away under me by amount
`vᵀHv`; reproject that correction through the UV distortion `G⁻¹` and steer
against it."* One matrix-vector product. No Christoffel symbols, no index
tensors — if you can multiply a matrix by a vector, you can integrate this.

<details>
<summary>Why is that the whole story? (optional, one paragraph)</summary>

The 3D acceleration of the lifted point is `J γ̈ + (vᵀHv)·e₃`: one part from
changing the UV velocity, one part from the height bending. "Geodesic" means
this 3D acceleration has zero tangential component, i.e. it's parallel to the
normal. Dot it with the two mesh tangents (the columns of `J`) — the normal
part gives zero, and you're left with `G γ̈ + (vᵀHv)∇h = 0`. Solve for `γ̈`
by multiplying with `G⁻¹`. That's the formula above.
</details>

---

## 3. Shooting = "fire and integrate"

Like ballistic prediction in a game: pick a muzzle position and direction,
then integrate the ODE with fixed timestep. The state is the classic
second-order-ODE bundle:

```text
state s = (pos: float2, vel: float2)   // all in UV space
field h s = (vel, geoAccel h pos vel)  // like (v, a) in verlet-style code
```

Then any one-step integrator plugs into the same loop:

```text
sₙ₊₁ = step h sₙ dt
```

That's `shoot step h s₀ dt n` — just `n` iterations of `step`.
`impactPoint h s = (x, y, h x y)` is the render call.

### Explicit Euler (the cheap one)

The integrator you'd write first in any game jam:

```text
s += dt * field(s)
```

Sampling the derivative once per step, marching straight along it:

<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 720 240" font-family="sans-serif" font-size="14">
  <path d="M 60 190 Q 360 60 660 60" fill="none" stroke="#bbb" stroke-width="6" opacity="0.5"/>
  <path d="M 60 190 L 200 140 L 330 110 L 460 92 L 600 82" fill="none" stroke="#d33" stroke-width="3" stroke-dasharray="7 5"/>
  <g stroke="#1a6bb5" stroke-width="2.5" fill="#1a6bb5">
    <line x1="200" y1="140" x2="252" y2="122"/><polygon points="247,114 262,118 254,129"/>
    <line x1="330" y1="110" x2="384" y2="96"/><polygon points="380,88 394,93 386,103"/>
    <line x1="460" y1="92" x2="516" y2="80"/><polygon points="512,73 526,78 518,88"/>
  </g>
  <g fill="#d33"><circle cx="60" cy="190" r="5"/><circle cx="200" cy="140" r="5"/><circle cx="330" cy="110" r="5"/><circle cx="460" cy="92" r="5"/><circle cx="600" cy="82" r="5"/></g>
  <text x="360" y="225" text-anchor="middle" fill="#345">Euler: sample slope once, run straight, repeat — drifts off the true path (grey)</text>
</svg>

Two familiar problems: it undershoots/overshoots on curves (the dashed path
cuts the corner), and the error accumulates every step. On a strongly curved
surface the shot visibly spirals off the geodesic.

### Runge–Kutta 4 (the one you'll actually ship)

Same API, four `field` evaluations per step: slope at the start (`k₁`),
two midpoint probes (`k₂, k₃`), slope at the end (`k₄`), then a
1–2–2–1 weighted average:

```text
sₙ₊₁ = s + dt/6 * (k₁ + 2k₂ + 2k₃ + k₄)
```

<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 720 240" font-family="sans-serif" font-size="13">
  <path d="M 60 190 Q 360 60 660 60" fill="none" stroke="#bbb" stroke-width="6" opacity="0.5"/>
  <g fill="#d33"><circle cx="80" cy="182" r="5"/></g>
  <g stroke-linecap="round">
    <g stroke="#1a6bb5" stroke-width="3"><line x1="80" y1="182" x2="140" y2="160"/><polygon points="135,151 152,155 143,166" fill="#1a6bb5"/></g>
    <text x="112" y="150" fill="#1a6bb5">k₁ @ start</text>
    <g stroke="#3aa04a" stroke-width="3"><line x1="170" y1="171" x2="238" y2="150"/><polygon points="232,141 249,146 240,157" fill="#3aa04a"/></g>
    <text x="205" y="196" fill="#3aa04a">k₂ @ mid</text>
    <g stroke="#c47f00" stroke-width="3"><line x1="260" y1="160" x2="330" y2="138"/><polygon points="324,129 341,134 332,145" fill="#c47f00"/></g>
    <text x="292" y="185" fill="#c47f00">k₃ @ mid (again)</text>
    <g stroke="#7a1ab5" stroke-width="3"><line x1="350" y1="146" x2="426" y2="123"/><polygon points="420,114 437,119 428,130" fill="#7a1ab5"/></g>
    <text x="392" y="108" fill="#7a1ab5">k₄ @ end</text>
  </g>
  <path d="M 80 182 Q 240 120 440 120" fill="none" stroke="#d33" stroke-width="3"/>
  <circle cx="440" cy="120" r="5" fill="#d33"/>
  <text x="360" y="225" text-anchor="middle" fill="#345">RK4: average four slopes (1:2:2:1) — the step lands on the grey curve</text>
</svg>

In graphics terms: Euler is forward-difference, RK4 is central-difference
with a spline's worth of samples. In game-physics terms: RK4 is to Euler what
a proper spring solver is to "add gravity, clamp position".

---

## 4. Why "shooting"?

Because it's the shooting method from boundary-value problems: you don't
know the whole path, you **aim, fire, and watch where the bullet lands**.
If the landing point is wrong, adjust `muzzle` (direction, speed, start)
and fire again. The loop is:

1. `muzzle p dir speed` — set up the initial `(pos, vel)` in UV space.
2. `shoot eulerStep h s₀ dt n` or `shoot rk4Step h s₀ dt n` — integrate.
3. `impactPoint h sₙ` — where it hit.
4. Not happy? Retune the muzzle and go to 1.

---

## 5. Cheat sheet: file ↔ concept

| `Brane/Shooting.lean` | Graphics brain translation |
|---|---|
| `ShotState` | `struct { float2 pos; float2 vel; }` |
| `field h s` | the `(v, a)` RHS of your physics step |
| `geoAccel h p v` | the per-frame steering acceleration `-(G⁻¹ *ᵥ ((vᵀHv) • ∇h))` |
| `StepMethod` | `typedef void (*integrator)(scene, state, dt)` |
| `eulerStep` / `rk4Step` | the two integrators; identical interface |
| `shoot step h s₀ dt n` | `for (i = 0; i &lt; n; i++) s = step(h, s, dt);` |
| `muzzle p dir speed` | spawning the projectile |
| `impactPoint h s` | the world-space render position `(x, y, h(x,y))` |
| `gramMatrix`, `hessian` | per-sample G and H textures you'd bake for a heightfield shader |

Everything is *definitions only* for now (`no proofs yet`): the equations are
declared, the proofs that Euler/RK4 converge, that RK4 is 4th-order, and that
the discrete shot hugs the true geodesic as `dt → 0` are the next layer —
the Lean equivalent of writing the unit tests after the renderer works.
