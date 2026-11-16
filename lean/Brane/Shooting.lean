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

which is `geoAccel h p v` below. All of `g⁻¹`, `H`, `∇h` come from
`Brane.DiffGeom`.

The integrator is factored through a single abstract one-step interface
`StepMethod`, so that the plain Euler step defined here (`eulerStep`) can be
swapped later for a Runge–Kutta 4 step (`rk4Step`, also defined here) without
changing any of the surrounding machinery: the trajectory is just iteration
of the chosen step (`shoot`), and every statement about trajectories need
only be proved once per step method.

Namespace: `Brane.Shoot`.
-/

namespace Brane

open DiffGeom
open Matrix WithLp
open scoped Matrix RealInnerProductSpace

noncomputable section

namespace Shoot

/-! ## The geodesic vector field, in matrices and vectors

Everything here is a `def` built from `Brane.DiffGeom`; no proofs yet. -/

/-- The parameter gradient of `h`, as a `Fin 2 → ℝ` vector:
`(∂₀h, ∂₁h) = (partialX, partialY)`. -/
def gradientVec (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Vel2 :=
  ![partialX h p.1 p.2, partialY h p.1 p.2]

/-- The Hessian quadratic form `γ̇ᵀ H γ̇`: the second derivative of `h` along
the parameter velocity `v`. -/
def hessQuad (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (v : Vel2) : ℝ :=
  v ⬝ᵥ (hessian h p *ᵥ v)

/-- The geodesic acceleration in parameter space, as a matrix–vector
expression:

`geoAccel h p v = -(gramMatrix h p)⁻¹ *ᵥ ((hessQuad h p v) • gradientVec h p)`.

A parameter curve `γ` with velocity `v = γ̇` is a geodesic exactly when its
acceleration satisfies `γ̈ = geoAccel h γ γ̈`. -/
def geoAccel (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (v : Vel2) : Vel2 :=
  -((gramMatrix h p)⁻¹ *ᵥ (hessQuad h p v • gradientVec h p))

/-! ## The state of a shot

A shot is a second-order ODE, so its state is (position, velocity) in the
parameter plane `ℝ²`. We bundle them into a structure and give it vector
space structure coordinatewise, which is what makes symmetric one-step
methods (Euler, Runge–Kutta) expressible uniformly. -/

/-- The state of a shot: parameter position and parameter velocity. -/
structure ShotState where
  /-- Position `(x, y)` in the parameter plane. -/
  pos : ℝ × ℝ
  /-- Velocity `(x', y')` in the parameter plane. -/
  vel : Vel2

/-- Coordinatewise addition of shot states. -/
def addShotState (s t : ShotState) : ShotState :=
  ⟨(s.pos.1 + t.pos.1, s.pos.2 + t.pos.2), fun k => s.vel k + t.vel k⟩

/-- Coordinatewise scalar multiplication of a shot state. -/
def smulShotState (r : ℝ) (s : ShotState) : ShotState :=
  ⟨(r * s.pos.1, r * s.pos.2), fun k => r * s.vel k⟩

instance : Add ShotState := ⟨addShotState⟩

instance : SMul ℝ ShotState := ⟨smulShotState⟩

/-- The zero state, the neutral element for later algebra. -/
def zeroShotState : ShotState := ⟨(0, 0), fun _ => 0⟩

instance : Zero ShotState := ⟨zeroShotState⟩

/-! ## One-step integrators -/

/-- A one-step method: given the surface `h`, the current state and the time
step, produce the next state. Euler and Runge–Kutta 4 are both instances;
every trajectory statement can be made at this level of generality. -/
abbrev StepMethod := (ℝ → ℝ → ℝ) → ShotState → ℝ → ShotState

/-- The derivative of a shot state along the flow: velocity plus geodesic
acceleration. This is the vector field whose integral curve is the shot;
it does not depend explicitly on time, so all methods read `field h s`. -/
def field (h : ℝ → ℝ → ℝ) (s : ShotState) : ShotState :=
  ⟨(s.vel 0, s.vel 1), geoAccel h s.pos s.vel⟩

/-- One explicit-Euler step: `sₙ₊₁ = sₙ + Δt · field h sₙ`. -/
def eulerStep : StepMethod := fun h s dt => s + dt • field h s

/-! ### Runge–Kutta 4

The classical fourth-order method, expressed through the same `field` and
the same `Add` / `SMul` structure. Defined now, proofs later. -/

/-- The four RK4 increments of a state with time step `dt`. -/
def rk4Increments (h : ℝ → ℝ → ℝ) (s : ShotState) (dt : ℝ) :
    ShotState × ShotState × ShotState × ShotState :=
  let k₁ := field h s
  let k₂ := field h (s + (dt / 2) • k₁)
  let k₃ := field h (s + (dt / 2) • k₂)
  let k₄ := field h (s + dt • k₃)
  ⟨k₁, k₂, k₃, k₄⟩

/-- One classical Runge–Kutta 4 step:
`sₙ₊₁ = sₙ + Δt/6 · (k₁ + 2k₂ + 2k₃ + k₄)`. -/
def rk4Step : StepMethod := fun h s dt =>
  let ⟨k₁, k₂, k₃, k₄⟩ := rk4Increments h s dt
  s + (dt / 6) • (k₁ + (2 : ℝ) • k₂ + (2 : ℝ) • k₃ + k₄)

/-! ## The shooting trajectory -/

/-- The muzzle state: start at `p` with velocity `speed` in the direction
`dir` (a point of the unit-speed directions of the parameter plane). -/
def muzzle (p : ℝ × ℝ) (dir : Vel2) (speed : ℝ) : ShotState :=
  ⟨p, fun k => speed * dir k⟩

/-- The shot trajectory as a discrete stream: iterating the step method
`n` times with fixed time step `dt`. `shoot step h s₀ dt 0 = s₀` and
`shoot step h s₀ dt (n+1) = step h (shoot step h s₀ dt n) dt`. -/
def shoot (step : StepMethod) (h : ℝ → ℝ → ℝ) (s₀ : ShotState) (dt : ℝ) :
    ℕ → ShotState
  | 0 => s₀
  | (n + 1) => step h (shoot step h s₀ dt n) dt

/-- The trajectory produced by explicit Euler: the baseline method. -/
abbrev eulerTrajectory (h : ℝ → ℝ → ℝ) (s₀ : ShotState) (dt : ℝ) (n : ℕ) :
    ShotState :=
  shoot eulerStep h s₀ dt n

/-- The trajectory produced by Runge–Kutta 4. -/
abbrev rk4Trajectory (h : ℝ → ℝ → ℝ) (s₀ : ShotState) (dt : ℝ) (n : ℕ) :
    ShotState :=
  shoot rk4Step h s₀ dt n

/-- The spatial point reached by a shot at step `n`: the lifted parameter
position `graph h γₙ`, i.e. the bullet's position in `ℝ³`. -/
def impactPoint (h : ℝ → ℝ → ℝ) (s : ShotState) : Vec3 :=
  graph h s.pos

end Shoot

end

end Brane
