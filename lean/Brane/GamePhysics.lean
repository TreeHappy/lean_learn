/-
Copyright (c) 2026 Brane contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brane contributors
-/

import Mathlib.Tactic

/-!
# The physics of the browser game, in Lean

This module is the Lean twin of the numerical core in `web/index.html`. It is
deliberately **executable** (everything runs on `Float`) and deliberately
**proof-light**: the few statements that would normally be lemmas are left as
`sorry`. The point is to make the game's ODEs inspectable and runnable, not to
certify them yet.

The browser game integrates a second-order ODE

    q̈ = A(q, q̇)

by first rewriting it as a first-order ODE on the *state* `(q, q̇)`:

    state = (x, y, vx, vy)
    d(state)/dt = (vx, vy, Ax, Ay)

`eulerStep` and `rk4Step` below are the same two one-step methods used in the
page. `geoAccel` is the pinball field (free rolling on a curved surface);
`walkAccelWith` adds gravity, a keyboard push and rolling friction. The
`Vec3` helpers at the end are the no-slip rolling kinematics that turn the
parameter velocity into the marble's angular velocity.

See `docs/ode-numerics.md` for a numerical introduction aimed at this code,
and `docs/game-math.md` for the full derivations.

Namespace: `Brane.GamePhysics`.
-/

namespace Brane

namespace GamePhysics

/-! ## 1. The terrain (a sum of Gaussians) -/

/-- One Gaussian hill (positive `a`) or crater (negative `a`). The fields have
the same names as the JavaScript object in `web/index.html`. -/
structure Bump where
  a  : Float
  cx : Float
  cy : Float
  r2 : Float
  deriving Repr

/-- A small deterministic terrain. The browser randomises its bumps; this one
is fixed so that `#eval` gives the same trajectory every time. -/
def demoBumps : Array Bump :=
  #[⟨1.0, -1.0, 0.0, 1.0⟩,
    ⟨-0.7, 1.0, 0.5, 0.8⟩,
    ⟨0.9, 0.0, -1.2, 1.3⟩]

/-- Height `h(x,y) = Σ aᵢ exp(-((x-cxᵢ)² + (y-cyᵢ)²)/r2ᵢ)`. -/
def heightAt (bumps : Array Bump) (x y : Float) : Float :=
  bumps.foldl (fun acc b =>
    let dx := x - b.cx
    let dy := y - b.cy
    acc + b.a * Float.exp (-(dx * dx + dy * dy) / b.r2)) 0

/-- The five derivatives the physics needs: `(hx, hy, hxx, hxy, hyy)`. -/
structure Derivs where
  hx  : Float
  hy  : Float
  hxx : Float
  hxy : Float
  hyy : Float
  deriving Repr

/-- Analytic derivatives of the Gaussian sum, computed in the same pass as the
height in the browser version. -/
def derivativesAt (bumps : Array Bump) (x y : Float) : Derivs :=
  bumps.foldl (fun d b =>
    let dx := x - b.cx
    let dy := y - b.cy
    let r2 := b.r2
    let e := b.a * Float.exp (-(dx * dx + dy * dy) / r2)
    { hx  := d.hx  + e * (-2 * dx / r2)
      hy  := d.hy  + e * (-2 * dy / r2)
      hxx := d.hxx + e * (4 * dx * dx / (r2 * r2) - 2 / r2)
      hxy := d.hxy + e * (4 * dx * dy / (r2 * r2))
      hyy := d.hyy + e * (4 * dy * dy / (r2 * r2) - 2 / r2) })
    ⟨0, 0, 0, 0, 0⟩

/-! ## 2. The state and the metric -/

/-- The ODE state: parameter position `(x,y)` and parameter velocity `(vx,vy)`.
This is the `s = [x, y, vx, vy]` array from the JavaScript RK4 routine. -/
structure State where
  x  : Float
  y  : Float
  vx : Float
  vy : Float
  deriving Repr

instance : Add State where
  add s t := ⟨s.x + t.x, s.y + t.y, s.vx + t.vx, s.vy + t.vy⟩

instance : SMul Float State where
  smul r s := ⟨r * s.x, r * s.y, r * s.vx, r * s.vy⟩

instance : Zero State where
  zero := ⟨0, 0, 0, 0⟩

/-- Apply the inverse of the surface metric `G = [[1+hx², hx·hy], [hx·hy, 1+hy²]]`
to a covector `(gx, gy)`. This is `ginvTimes` in the page. -/
def ginvTimes (hx hy gx gy : Float) : Float × Float :=
  let det := 1 + hx * hx + hy * hy
  (((1 + hy * hy) * gx - hx * hy * gy) / det,
   (-(hx * hy) * gx + (1 + hx * hx) * gy) / det)

/-- The Hessian quadratic form `vᵀHv`: how strongly the surface bends in the
current direction of travel. -/
def hessQuad (d : Derivs) (s : State) : Float :=
  s.vx * s.vx * d.hxx + 2 * s.vx * s.vy * d.hxy + s.vy * s.vy * d.hyy

/-! ## 3. The two accelerations -/

/-- Pinball acceleration: `q̈ = -G⁻¹ ((vᵀHv) ∇h)`. A geodesic has no
external force; curvature alone bends the path. -/
def geoAccel (bumps : Array Bump) (s : State) : Float × Float :=
  let d := derivativesAt bumps s.x s.y
  let k := hessQuad d s
  ginvTimes d.hx d.hy (-k * d.hx) (-k * d.hy)

/-- Walk-mode acceleration with explicit constants, so we can state a
"turn all forces off" lemma below. `push` is the generalized force `(fx,fy)`
obtained by projecting the keyboard direction onto the surface. -/
def walkAccelWith (g kfric : Float) (bumps : Array Bump)
    (push : Float × Float) (s : State) : Float × Float :=
  let d := derivativesAt bumps s.x s.y
  let k := hessQuad d s
  let (fx, fy) := push
  let (ax, ay) := ginvTimes d.hx d.hy
    (fx - (k + g) * d.hx) (fy - (k + g) * d.hy)
  (ax - kfric * s.vx, ay - kfric * s.vy)

/-- The constants used by the browser page. -/
def gravity    : Float := 2.2
def friction   : Float := 0.9
def pushScale  : Float := 4.5
def restitution : Float := 0.55
def marbleRadius : Float := 0.16
def domainLimit : Float := 3.2

/-- Walk acceleration with the game's gravity and friction. -/
def walkAccel (bumps : Array Bump) (push : Float × Float) (s : State) : Float × Float :=
  walkAccelWith gravity friction bumps push s

/-! ## 4. One-step integrators (the numerical heart) -/

/-- Turn a second-order field `q̈ = A(q,q̇)` into a first-order field on the
four-dimensional state. This is the `f` inside the JavaScript `rk4Step`. -/
def field (accel : State → Float × Float) (s : State) : State :=
  ⟨s.vx, s.vy, (accel s).1, (accel s).2⟩

/-- Explicit Euler: one slope probe, `sₙ₊₁ = sₙ + Δt · f(sₙ)`. -/
def eulerStep (accel : State → Float × Float) (s : State) (dt : Float) : State :=
  s + dt • field accel s

/-- Classical RK4: four probes weighted `1 : 2 : 2 : 1`. This is the exact
same arithmetic as `rk4Step` in `web/index.html`. -/
def rk4Step (accel : State → Float × Float) (s : State) (dt : Float) : State :=
  let k₁ := field accel s
  let k₂ := field accel (s + (dt / 2) • k₁)
  let k₃ := field accel (s + (dt / 2) • k₂)
  let k₄ := field accel (s + dt • k₃)
  s + (dt / 6) • (k₁ + (2 : Float) • k₂ + (2 : Float) • k₃ + k₄)

/-- A trajectory is just repeated stepping. `trajectory step accel s₀ dt n`
is the state after `n` steps. -/
def trajectory (step : (State → Float × Float) → State → Float → State)
    (accel : State → Float × Float) (s₀ : State) (dt : Float) : Nat → State
  | 0 => s₀
  | n + 1 => step accel (trajectory step accel s₀ dt n) dt

/-- The same trajectory as an array, including the initial state. This is what
a browser renderer would turn into dots or a marble path. -/
def samples (step : (State → Float × Float) → State → Float → State)
    (accel : State → Float × Float) (s₀ : State) (dt : Float) (n : Nat) : Array State :=
  go n s₀ #[]
where
  go : Nat → State → Array State → Array State
    | 0, s, acc => acc.push s
    | k + 1, s, acc => go k (step accel s dt) (acc.push s)

/-- Reflect the velocity at the square boundary, as the walk mode does. -/
def bounce (limit e : Float) (s : State) : State :=
  let x := max (-limit) (min limit s.x)
  let y := max (-limit) (min limit s.y)
  let vx := if s.x > limit ∨ s.x < -limit then -e * s.vx else s.vx
  let vy := if s.y > limit ∨ s.y < -limit then -e * s.vy else s.vy
  ⟨x, y, vx, vy⟩

/-- One walk-mode frame: RK4, then a boundary bounce. -/
def walkStep (bumps : Array Bump) (push : Float × Float) (s : State) (dt : Float) : State :=
  bounce domainLimit restitution (rk4Step (walkAccel bumps push) s dt)

/-! ## 5. Rolling kinematics (the marble's spin) -/

/-- A 3-vector in world coordinates (z is up). -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr

instance : Add Vec3 where
  add a b := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

instance : SMul Float Vec3 where
  smul r v := ⟨r * v.x, r * v.y, r * v.z⟩

/-- Cross product `a × b`. -/
def cross (a b : Vec3) : Vec3 :=
  ⟨a.y * b.z - a.z * b.y,
   a.z * b.x - a.x * b.z,
   a.x * b.y - a.y * b.x⟩

/-- Unit normal of the graph from a derivative record: `(-hx,-hy,1)/‖·‖`. -/
def normalOf (d : Derivs) : Vec3 :=
  let q := Float.sqrt (1 + d.hx * d.hx + d.hy * d.hy)
  ⟨-d.hx / q, -d.hy / q, 1 / q⟩

/-- Surface normal at a state. -/
def normal (bumps : Array Bump) (s : State) : Vec3 :=
  normalOf (derivativesAt bumps s.x s.y)

/-- Derivative of the normal in time, from the Hessian. Needed because the
marble's centre is `p + r·n`, not just `p + r·e_z`. -/
def normalDot (d : Derivs) (s : State) : Vec3 :=
  let q := Float.sqrt (1 + d.hx * d.hx + d.hy * d.hy)
  let a := d.hxx * s.vx + d.hxy * s.vy
  let b := d.hxy * s.vx + d.hyy * s.vy
  let n := normalOf d
  let c := (d.hx * a + d.hy * b) / (q * q)
  ⟨-a / q - n.x * c, -b / q - n.y * c, -n.z * c⟩

/-- Velocity of the marble's centre in world space. -/
def centerVelocity (bumps : Array Bump) (s : State) : Vec3 :=
  let d := derivativesAt bumps s.x s.y
  let nd := normalDot d s
  ⟨s.vx + marbleRadius * nd.x,
   s.vy + marbleRadius * nd.y,
   d.hx * s.vx + d.hy * s.vy + marbleRadius * nd.z⟩

/-- Angular velocity from the no-slip rolling constraint `ω = (n × v_c)/r`. -/
def angularVelocity (bumps : Array Bump) (s : State) : Vec3 :=
  (1 / marbleRadius) • cross (normal bumps s) (centerVelocity bumps s)

/-! ## 6. Statements left as `sorry`

These are the facts you would prove once the numerical definitions are stable.
They are written down now so the intended behaviour is documented. -/

/-- With gravity, friction and push all zero, walk mode is just pinball. -/
theorem walkAccelWith_zero (bumps : Array Bump) (s : State) :
    walkAccelWith 0 0 bumps (0, 0) s = geoAccel bumps s := by
  sorry

/-- The rolling constraint, rearranged: `r · (ω × n) = v_c`. -/
theorem rolling_constraint (bumps : Array Bump) (s : State) :
    marbleRadius • cross (angularVelocity bumps s) (normal bumps s) =
      centerVelocity bumps s := by
  sorry

/-- RK4 is fourth order: halving `dt` divides the local truncation error by 16
(for a smooth field). Making this precise needs Taylor estimates; the numerical
story is in `docs/ode-numerics.md`. -/
theorem rk4_local_error_is_fourth_order
    (accel : State → Float × Float) (s : State) (dt : Float) : True := by
  sorry

/-- A reproducible example trajectory. Try:

```lean
#eval samples rk4Step (geoAccel demoBumps) ⟨-1.6, -1.6, 0.5, 0.2⟩ 0.02 5
```

from a Lean file that imports this module. -/
def demoShot : Array State :=
  samples rk4Step (geoAccel demoBumps) ⟨-1.6, -1.6, 0.5, 0.2⟩ 0.02 5

end GamePhysics

end Brane
