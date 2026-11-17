/-
Copyright (c) 2026 Brane contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brane contributors
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Brane.DifferentialGeometry

/-!
# Shooting geodesics on graph surfaces

This file expresses the "shooting" algorithm for firing a bullet (a geodesic)
across a graph surface `graph h`, using only the matrix and vector
ingredients of `Brane.DiffGeom`: the Jacobian, the Hessian, and the Gram
matrix. No Christoffel symbols appear; the geodesic equation is written as a
single matrix–vector product.

The geodesic equation in matrix form. A curve on the surface with parameter
coordinates `γ(t)` lifts to `σ ∘ γ`. Its ambient acceleration is

`(σ ∘ γ)'' = J γ̈ + (γ̇ᵀ H γ̇) · e₃`,

where `J` is the Jacobian (`jacobian h γ`) and `H` the Hessian
(`hessian h γ`). The lifted curve is a geodesic exactly when this
acceleration is purely normal to the surface, i.e. has no tangential part.
Taking inner products with the two coordinate tangents `J e₀, J e₁`
kills the normal part and yields the matrix–vector equation

`g γ̈ + (γ̇ᵀ H γ̇) ∇h = 0`,

with `g = Jᵀ J` the Gram matrix (`gramMatrix h γ`) and `∇h` the parameter
gradient of `h`. Hence the geodesic acceleration is

`γ̈ = -g⁻¹ *ᵥ ((γ̇ᵀ H γ̇) • ∇h)`,

which is `geoAccel h p v` below (written as the closed-form solve of the 2×2
Gram system). All of `g`, `H`, `∇h` come from `Brane.DiffGeom`.

The integrator is factored through a single abstract one-step interface
`StepMethod`, so that the plain Euler step defined here (`eulerStep`) can be
swapped later for a Runge–Kutta 4 step (`rk4Step`, also defined here) without
changing any of the surrounding machinery: the trajectory is just iteration
of the chosen step (`shoot`), and every statement about trajectories need
only be proved once per step method.

## The number type is abstract

Every definition here is polymorphic in the number type `K`, quantified over
the `GeoKernel` class: the six partial derivatives of a height function plus
the handful of numerals the formulas need. There are two instances:

* `K = ℝ` — the partials are Mathlib's `deriv` (the mathematical definition,
  via `DiffGeom.partialX`, …). This instance is `noncomputable`; the proofs
  live here.
* `K = Float` — the partials are central finite differences. This instance
  is computable, and it is what the figure generator `lake exe gen-figures`
  (`make figures`) executes: the trajectory, tangent and normal figures in
  `docs/figures` are *computed by running these very definitions*.

So the figures never run a "mirror" of the math: `Shoot.shoot rk4Step
bowlHeight …` is the same `shoot`, `rk4Step` and `bowlHeight` the text cites.

Namespace: `Brane.Shoot`.
-/

namespace Brane

namespace Shoot

/-! ## The differentiation kernel

How to differentiate a height function `K → K → K`, plus the numerals the
geodesic formulas need. See the module docstring for the two instances. -/

class GeoKernel (K : Type) where
  /-- `∂h/∂x`. -/
  partialX : (K → K → K) → K → K → K
  /-- `∂h/∂y`. -/
  partialY : (K → K → K) → K → K → K
  /-- `∂²h/∂x²`. -/
  partialXX : (K → K → K) → K → K → K
  /-- `∂²h/∂y∂x`: the `y`-derivative of `∂h/∂x`. -/
  partialXY : (K → K → K) → K → K → K
  /-- `∂²h/∂x∂y`: the `x`-derivative of `∂h/∂y`. -/
  partialYX : (K → K → K) → K → K → K
  /-- `∂²h/∂y²`. -/
  partialYY : (K → K → K) → K → K → K
  /-- The numerals `0, 1, 2, 6` as elements of `K`. -/
  zero : K
  /-- The numeral `1`. -/
  one : K
  /-- The numeral `2`. -/
  two : K
  /-- The numeral `6`. -/
  six : K

export GeoKernel (partialX partialY partialXX partialXY partialYX partialYY)

/-! ### The computable `Float` kernel -/

/-- Half-width of the finite-difference stencil. -/
def floatEps : Float := 0.0001

/-- `∂h/∂x` over `Float`: central difference in the first argument. -/
def floatPartialX (h : Float → Float → Float) (x y : Float) : Float :=
  (h (x + floatEps) y - h (x - floatEps) y) / (2 * floatEps)

/-- `∂h/∂y` over `Float`: central difference in the second argument. -/
def floatPartialY (h : Float → Float → Float) (x y : Float) : Float :=
  (h x (y + floatEps) - h x (y - floatEps)) / (2 * floatEps)

/-- `∂²h/∂x²` over `Float`. -/
def floatPartialXX (h : Float → Float → Float) (x y : Float) : Float :=
  (floatPartialX h (x + floatEps) y - floatPartialX h (x - floatEps) y)
    / (2 * floatEps)

/-- `∂²h/∂y∂x` over `Float`. -/
def floatPartialXY (h : Float → Float → Float) (x y : Float) : Float :=
  (floatPartialX h x (y + floatEps) - floatPartialX h x (y - floatEps))
    / (2 * floatEps)

/-- `∂²h/∂x∂y` over `Float`. -/
def floatPartialYX (h : Float → Float → Float) (x y : Float) : Float :=
  (floatPartialY h (x + floatEps) y - floatPartialY h (x - floatEps) y)
    / (2 * floatEps)

/-- `∂²h/∂y²` over `Float`. -/
def floatPartialYY (h : Float → Float → Float) (x y : Float) : Float :=
  (floatPartialY h x (y + floatEps) - floatPartialY h x (y - floatEps))
    / (2 * floatEps)

/-- The computable kernel: central finite differences. The figure generator
runs the pipeline through this instance. -/
instance : GeoKernel Float where
  partialX := floatPartialX
  partialY := floatPartialY
  partialXX := floatPartialXX
  partialXY := floatPartialXY
  partialYX := floatPartialYX
  partialYY := floatPartialYY
  zero := 0
  one := 1
  two := 2
  six := 6

/-! ## The geodesic vector field

Everything here is a `def` built from the kernel; no proofs yet. The number
type `K` is arbitrary with a `GeoKernel` instance. -/

variable {K : Type} [GeoKernel K] [Add K] [Mul K] [Neg K] [Sub K] [Div K]

open GeoKernel

/-- The parameter gradient of `h`, as a `Fin 2 → K` vector:
`(∂₀h, ∂₁h) = (partialX, partialY)`. -/
def gradientVec (h : K → K → K) (p : K × K) : Fin 2 → K :=
  ![partialX h p.1 p.2, partialY h p.1 p.2]

/-- The Hessian quadratic form `γ̇ᵀ H γ̇`: the second derivative of `h` along
the parameter velocity `v`. This is `v ⬝ᵥ (H *ᵥ v)` written out coordinatewise
with `H = [[∂ₓₓh, ∂ₓᵧh], [∂ᵧₓh, ∂ᵧᵧh]]` (for `K = ℝ` this equality is
`hessQuad_eq` below). -/
def hessQuad (h : K → K → K) (p : K × K) (v : Fin 2 → K) : K :=
  v 0 * (partialXX h p.1 p.2 * v 0 + partialXY h p.1 p.2 * v 1)
    + v 1 * (partialYX h p.1 p.2 * v 0 + partialYY h p.1 p.2 * v 1)

/-- The three independent entries `(g₁₁, g₁₂, g₂₂)` of the Gram matrix of the
coordinate tangents: `g₁₁ = 1 + (∂ₓh)²`, `g₁₂ = ∂ₓh ∂ᵧh`, `g₂₂ = 1 + (∂ᵧh)²`.
For `K = ℝ` these are exactly the entries of `DiffGeom.gramMatrix`
(`gramEntries_eq` below), and `det g = 1 + |∇h|² ≥ 1`
(`DiffGeom.det_gramMatrix_eq`). -/
def gramEntries (h : K → K → K) (p : K × K) : K × K × K :=
  let fx := partialX h p.1 p.2
  let fy := partialY h p.1 p.2
  (one + fx * fx, fx * fy, one + fy * fy)

/-- The geodesic acceleration in parameter space, i.e. the solution of the
Gram system

`g γ̈ + (hessQuad h p v) • gradientVec h p = 0`,

written in closed form: `γ̈ = -g⁻¹ m` with the 2×2 inverse applied
entrywise, `g⁻¹ = (1/det g) [[g₂₂, -g₁₂], [-g₁₂, g₁₁]]`. For `K = ℝ` this
is `-((gramMatrix h p)⁻¹ *ᵥ (hessQuad h p v • gradientVec h p))`
(`geoAccel_eq_matrix` below).

A parameter curve `γ` with velocity `v = γ̇` is a geodesic exactly when its
acceleration satisfies `γ̈ = geoAccel h γ γ̇`. -/
def geoAccel (h : K → K → K) (p : K × K) (v : Fin 2 → K) : Fin 2 → K :=
  let (g11, g12, g22) := gramEntries h p
  let det := g11 * g22 - g12 * g12
  let k := hessQuad h p v
  let (m₁, m₂) := (k * partialX h p.1 p.2, k * partialY h p.1 p.2)
  ![-(g22 * m₁ - g12 * m₂) / det, -(-(g12 * m₁) + g11 * m₂) / det]

/-! ## The state of a shot

A shot is a second-order ODE, so its state is (position, velocity) in the
parameter plane `K²`. We bundle them into a structure and give it vector
space structure coordinatewise, which is what makes symmetric one-step
methods (Euler, Runge–Kutta) expressible uniformly. -/

/-- The state of a shot: parameter position and parameter velocity. -/
structure ShotState (K : Type) where
  /-- Position in the parameter plane. -/
  pos : K × K
  /-- Velocity in the parameter plane. -/
  vel : Fin 2 → K

/-- Coordinatewise addition of shot states. -/
def addShotState (s t : ShotState K) : ShotState K :=
  ⟨(s.pos.1 + t.pos.1, s.pos.2 + t.pos.2), fun k => s.vel k + t.vel k⟩

/-- Coordinatewise scalar multiplication of a shot state. -/
def smulShotState (r : K) (s : ShotState K) : ShotState K :=
  ⟨(r * s.pos.1, r * s.pos.2), fun k => r * s.vel k⟩

instance : Add (ShotState K) := ⟨addShotState⟩

instance : SMul K (ShotState K) := ⟨smulShotState⟩

/-- The zero state, the neutral element for later algebra. -/
def zeroShotState : ShotState K := ⟨(zero, zero), fun _ => zero⟩

instance : Zero (ShotState K) := ⟨zeroShotState⟩

/-! ## One-step integrators -/

/-- A one-step method: given the surface `h`, the current state and the time
step, produce the next state. Euler and Runge–Kutta 4 are both instances;
every trajectory statement can be made at this level of generality. -/
abbrev StepMethod (K : Type) := (K → K → K) → ShotState K → K → ShotState K

/-- The derivative of a shot state along the flow: velocity plus geodesic
acceleration. This is the vector field whose integral curve is the shot;
it does not depend explicitly on time, so all methods read `field h s`. -/
def field (h : K → K → K) (s : ShotState K) : ShotState K :=
  ⟨(s.vel 0, s.vel 1), geoAccel h s.pos s.vel⟩

/-- One explicit-Euler step: `sₙ₊₁ = sₙ + Δt · field h sₙ`. -/
def eulerStep : StepMethod K := fun h s dt => s + dt • field h s

/-! ### Runge–Kutta 4

The classical fourth-order method, expressed through the same `field` and
the same `Add` / `SMul` structure. Defined now, proofs later. -/

/-- One classical Runge–Kutta 4 step:
`sₙ₊₁ = sₙ + Δt/6 · (k₁ + 2k₂ + 2k₃ + k₄)`, where `k₁` is the slope at the
start, `k₂, k₃` the two midpoint probes and `k₄` the slope at the end. -/
def rk4Step : StepMethod K := fun h s dt =>
  let k₁ := field h s
  let k₂ := field h (s + (dt / two) • k₁)
  let k₃ := field h (s + (dt / two) • k₂)
  let k₄ := field h (s + dt • k₃)
  s + (dt / six) • (k₁ + (two (K := K)) • k₂ + (two (K := K)) • k₃ + k₄)

/-! ## The shooting trajectory -/

/-- The trajectory as an array of sampled parameter positions, including the
start: iterate the step method `n` times with fixed time step `dt`. This is
the computable wrapper the figure generator consumes. -/
def shootPositions (step : StepMethod K) (h : K → K → K) (s₀ : ShotState K)
    (dt : K) (n : Nat) : Array (K × K) :=
  go n s₀ #[]
where
  go : Nat → ShotState K → Array (K × K) → Array (K × K)
    | 0, s, acc => acc.push s.pos
    | (k + 1), s, acc => go k (step h s dt) (acc.push s.pos)

/-- The shot trajectory as a discrete stream: iterating the step method
`n` times with fixed time step `dt`. `shoot step h s₀ dt 0 = s₀` and
`shoot step h s₀ dt (n+1) = step h (shoot step h s₀ dt n) dt`. -/
def shoot (step : StepMethod K) (h : K → K → K) (s₀ : ShotState K) (dt : K) :
    ℕ → ShotState K
  | 0 => s₀
  | (n + 1) => step h (shoot step h s₀ dt n) dt

/-- The trajectory produced by explicit Euler: the baseline method. -/
abbrev eulerTrajectory (h : K → K → K) (s₀ : ShotState K) (dt : K) (n : ℕ) :
    ShotState K :=
  shoot eulerStep h s₀ dt n

/-- The trajectory produced by Runge–Kutta 4. -/
abbrev rk4Trajectory (h : K → K → K) (s₀ : ShotState K) (dt : K) (n : ℕ) :
    ShotState K :=
  shoot rk4Step h s₀ dt n

/-! ## The `ℝ` kernel, and the bridge to `DiffGeom`

Over `ℝ` the kernel is Mathlib's `deriv`, i.e. exactly the partials of
`Brane.DiffGeom`; the lemmas below connect the coordinatewise (kernel) forms
to the matrix forms the text derives. -/

open DiffGeom
open Matrix WithLp
open scoped Matrix RealInnerProductSpace

noncomputable section

/-- The mathematical kernel: `DiffGeom`'s `deriv`-based partials. -/
instance instGeoKernelReal : GeoKernel ℝ where
  partialX := DiffGeom.partialX
  partialY := DiffGeom.partialY
  partialXX := DiffGeom.partialXX
  partialXY := DiffGeom.partialXY
  partialYX := DiffGeom.partialYX
  partialYY := DiffGeom.partialYY
  zero := 0
  one := 1
  two := 2
  six := 6

/-- The kernel `hessQuad` is the matrix form `v ⬝ᵥ (H *ᵥ v)`. -/
theorem hessQuad_eq (h : HeightFun) (p : Point2) (v : Vel2) :
    hessQuad h p v = v ⬝ᵥ (hessian h p *ᵥ v) := by
  have hrhs : v ⬝ᵥ (hessian h p *ᵥ v) =
      v 0 * (DiffGeom.partialXX h p.1 p.2 * v 0
          + DiffGeom.partialXY h p.1 p.2 * v 1)
        + v 1 * (DiffGeom.partialYX h p.1 p.2 * v 0
          + DiffGeom.partialYY h p.1 p.2 * v 1) := by
    simp [hessian, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hrhs]
  rfl

/-- The kernel Gram entries are the entries of `DiffGeom.gramMatrix`. -/
theorem gramEntries_eq (h : HeightFun) (p : Point2) :
    gramEntries h p =
      (⟪tangentX h p, tangentX h p⟫, ⟪tangentX h p, tangentY h p⟫,
        ⟪tangentY h p, tangentY h p⟫) := by
  simp only [gramEntries]
  rw [inner_tangentX_tangentX, inner_tangentX_tangentY, inner_tangentY_tangentY,
    pow_two (DiffGeom.partialX h p.1 p.2), pow_two (DiffGeom.partialY h p.1 p.2)]
  rfl

/-! ### Exercises: the geodesic equation

These are left as `sorry` exercises; see the derivation in
`docs/shooting-method.md`. -/

/-- **Exercise.** The closed-form `geoAccel` is the matrix expression
`-((gramMatrix h p)⁻¹ *ᵥ (hessQuad h p v • gradientVec h p))`.

Hints:
* `gramEntries_eq` and `hessQuad_eq` identify the kernel forms with the
  matrix forms;
* `Matrix.mulVec` and `Fin.sum_univ_two` expand the right-hand side
  entrywise;
* the determinant of `g` is `1 + |∇h|²` (`DiffGeom.det_gramMatrix_eq`), so
  `g` is always invertible and the closed form is legitimate. -/
theorem geoAccel_eq_matrix (h : HeightFun) (p : Point2) (v : Vel2) :
    geoAccel h p v =
      -((gramMatrix h p)⁻¹ *ᵥ (hessQuad h p v • gradientVec h p)) := by
  sorry

/-- **Exercise.** `geoAccel` solves the geodesic equation
`G γ̈ + (vᵀ H v) ∇h = 0`, i.e. the parameter acceleration produced by
`geoAccel` exactly cancels the Hessian-quotient term when run through the
Gram matrix.

Hints: combine `geoAccel_eq_matrix` with `IsUnit` /
`Matrix.nonsing_inv_mul` (the determinant is `1 + |∇h|² ≥ 1`, so `G` is
always invertible — see `DiffGeom.det_gramMatrix_eq`), and
`DiffGeom.gramMatrix_eq_transpose_mul` to expand `G` through the tangents. -/
theorem geoAccel_solves_geodesic (h : HeightFun) (p : Point2) (v : Vel2) :
    gramMatrix h p *ᵥ geoAccel h p v + hessQuad h p v • gradientVec h p = 0 := by
  sorry

/-- **Exercise.** The vertical direction `e₃ = vec3 0 0 1` is *almost* the
surface normal: `normal h p = cross (tangentX h p) (tangentY h p)` differs from
`e₃` by the (horizontal) gradient of `h`:

`e₃ = normal h p + gradient h p`.

Hints: `DiffGeom.normal_eq`, `DiffGeom.gradient_eq`, `DiffGeom.vec3_add`,
`DiffGeom.vec3_eq_zero_iff`. -/
theorem e3_eq_normal_add_gradient (h : HeightFun) (p : Point2) :
    normal h p + gradient h p = vec3 0 0 1 := by
  sorry

/-- The muzzle state: start at `p` with velocity `speed` in the direction
`dir` (a point of the unit-speed directions of the parameter plane). -/
def muzzle (p : Point2) (dir : Vel2) (speed : ℝ) : ShotState ℝ :=
  ⟨p, fun k => speed * dir k⟩

/-- The spatial point reached by a shot at step `n`: the lifted parameter
position `graph h γₙ`, i.e. the bullet's position in `ℝ³`. -/
def impactPoint (h : HeightFun) (s : ShotState ℝ) : Point3 :=
  graph h s.pos

end

end Shoot

end Brane
