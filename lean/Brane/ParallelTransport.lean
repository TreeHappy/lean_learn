/-
Copyright (c) 2026 Brane contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brane contributors
-/
import Brane.Connections
import Brane.Shooting

/-!
# Parallel transport along a curve

This file adds the *curve* side of the connection story to
`Brane.Connections`. Fix a curve `γ : ℝ → Point2` in the parameter plane and
a vector field `V` along it (`V t : Vel2`). The covariant derivative of `V`
along `γ` is

`DV/dt = V̇ + Γ(γ̇, V)`,

where `Γ` is a connection written in Christoffel symbols. The field is
**parallel** when `DV/dt = 0`, and **parallel transport** is the solution of
that linear ODE with a prescribed initial vector. A geodesic is precisely a
curve whose velocity field is parallel.

The ODE theory (existence, uniqueness, linearity, and the reverse-curve
inverse) is classical Picard–Lindelöf material; here it is stated and left
as `sorry`, in the same style as the geometric bridges of
`Brane.GADiffGeom`. The definitions themselves are concrete, so the bridge
to the shooting method of `Brane.Shoot` can be stated exactly.

## Main definitions

* `Brane.Trans.Curve`, `FieldAlong`, `curveVelocity`, `covAlongChristoffel`;
* `Brane.Trans.isParallel`, `parallelTransport`, `transportMap`;
* `Brane.Trans.reverseCurve`, `holonomyGroup`;
* `Brane.Trans.isGeodesic`.

## Status of proofs

`parallelTransport` is built from an existence statement via
`Classical.choose`; the initial condition and the parallel equation are
then immediate from the choice. Linearity, the reverse-curve inverse, and
the geodesic bridge to `Brane.Shoot.geoAccel` are `sorry`.

## Tags

parallel transport, covariant derivative along a curve, holonomy,
geodesic, Picard–Lindelöf
-/

namespace Brane
namespace Trans

open DiffGeom
open Brane.Conn

noncomputable section

/-! ## Curves and fields along them -/

/-- A curve in the parameter plane: `γ : ℝ → Point2`. -/
abbrev Curve : Type := ℝ → Point2

/-- A vector field along a curve `γ`: a `Vel2`-valued function on the
parameter interval. -/
abbrev FieldAlong (_γ : Curve) : Type := ℝ → Vel2

/-- The velocity of a parameter curve: `γ̇ = (dγ₀/dt, dγ₁/dt)`. -/
def curveVelocity (γ : Curve) (t : ℝ) : Vel2 :=
  ![deriv (fun s : ℝ => (γ s).1) t, deriv (fun s : ℝ => (γ s).2) t]

/-- The covariant derivative of a field `V` along `γ`, in Christoffel
symbols:
`DV/dt = V̇ + Γ(γ̇, V)`. -/
def covAlongChristoffel (Γ : Point2 → Fin 2 → Mat22) (γ : Curve)
    (V : FieldAlong γ) (t : ℝ) : Vel2 :=
  fun k => deriv (fun s : ℝ => V s k) t +
    christoffelCorr Γ (γ t) (curveVelocity γ t) (V t) k

/-- A field `V` along `γ` is **parallel** when its covariant derivative
along `γ` vanishes identically. -/
def isParallel (Γ : Point2 → Fin 2 → Mat22) (γ : Curve)
    (V : FieldAlong γ) : Prop :=
  ∀ t : ℝ, covAlongChristoffel Γ γ V t = 0

/-! ## Existence and the transport map

Parallel transport is the unique solution of the linear ODE
`DV/dt = 0` with `V t₀ = v₀`. Existence and uniqueness are Picard–Lindelöf;
we take them as the `sorry`ed theorem `parallelTransport_exists` and build
the transport map from it by choice. -/

/-- **Existence and uniqueness of parallel transport** (Picard–Lindelöf):
for every initial time and vector there is a unique parallel field with that
initial value. Only existence is needed for the definition; uniqueness is
what makes the map well defined. -/
theorem parallelTransport_exists (Γ : Point2 → Fin 2 → Mat22) (γ : Curve)
    (t₀ : ℝ) (v₀ : Vel2) :
    ∃ V : FieldAlong γ, isParallel Γ γ V ∧ V t₀ = v₀ := by
  sorry

/-- **Parallel transport** of `v₀` from time `t₀` along `γ`: the parallel
field chosen by `parallelTransport_exists`. -/
noncomputable def parallelTransport (Γ : Point2 → Fin 2 → Mat22) (γ : Curve)
    (t₀ : ℝ) (v₀ : Vel2) : FieldAlong γ :=
  Classical.choose (parallelTransport_exists Γ γ t₀ v₀)

/-- The field produced by `parallelTransport` is parallel. -/
theorem parallelTransport_isParallel (Γ : Point2 → Fin 2 → Mat22) (γ : Curve)
    (t₀ : ℝ) (v₀ : Vel2) :
    isParallel Γ γ (parallelTransport Γ γ t₀ v₀) :=
  (Classical.choose_spec (parallelTransport_exists Γ γ t₀ v₀)).1

/-- Parallel transport has the prescribed initial value. -/
theorem parallelTransport_initial (Γ : Point2 → Fin 2 → Mat22) (γ : Curve)
    (t₀ : ℝ) (v₀ : Vel2) :
    parallelTransport Γ γ t₀ v₀ t₀ = v₀ :=
  (Classical.choose_spec (parallelTransport_exists Γ γ t₀ v₀)).2

/-- The transport map `v ↦ V t` from time `s` to time `t`. -/
noncomputable def transportMap (Γ : Point2 → Fin 2 → Mat22) (γ : Curve)
    (s t : ℝ) : Vel2 → Vel2 :=
  fun v => parallelTransport Γ γ s v t

/-- Transport over a zero-length interval is the identity. -/
theorem transportMap_self (Γ : Point2 → Fin 2 → Mat22) (γ : Curve)
    (t : ℝ) (v : Vel2) :
    transportMap Γ γ t t v = v :=
  parallelTransport_initial Γ γ t v

/-- **Linearity of parallel transport**: the transport map is `ℝ`-linear. -/
theorem transportMap_linear (Γ : Point2 → Fin 2 → Mat22) (γ : Curve)
    (s t : ℝ) (a : ℝ) (v w : Vel2) :
    transportMap Γ γ s t (a • v + w) =
      a • transportMap Γ γ s t v + transportMap Γ γ s t w := by
  sorry

/-- The **reverse curve** `ρ(u) = γ(1 - u)`. -/
def reverseCurve (γ : Curve) : Curve :=
  fun u => γ (1 - u)

/-- Transporting along `γ` and then back along the reversed curve returns
the original vector: the transport map over `[s, t]` is invertible, with
inverse given by the reversed curve. -/
theorem transportMap_reverse (Γ : Point2 → Fin 2 → Mat22) (γ : Curve)
    (s t : ℝ) (v : Vel2) :
    transportMap Γ (reverseCurve γ) (1 - t) (1 - s) (transportMap Γ γ s t v) = v := by
  sorry

/-! ## Holonomy

The holonomy group at a point records the linear maps obtained by
transporting a vector around closed loops based at that point. -/

/-- The **holonomy group** at `p`: all transport maps around closed curves
`γ` with `γ 0 = γ 1 = p`. (It is stated as a set of functions; closure
under composition and inversion is part of the `sorry`ed structure theory.) -/
def holonomyGroup (Γ : Point2 → Fin 2 → Mat22) (p : Point2) :
    Set (Vel2 → Vel2) :=
  {T | ∃ γ : Curve, γ 0 = p ∧ γ 1 = p ∧ T = transportMap Γ γ 0 1}

/-- The identity is in the holonomy group (the constant loop). -/
theorem id_mem_holonomyGroup (Γ : Point2 → Fin 2 → Mat22) (p : Point2) :
    (fun v : Vel2 => v) ∈ holonomyGroup Γ p := by
  sorry

/-! ## Geodesics

A geodesic is a curve that is parallel *to itself*: its velocity field is
parallel along it. This is exactly the statement that the acceleration
`DV/dt` vanishes. -/

/-- A curve `γ` is a **geodesic** for the connection `Γ` when its velocity
field is parallel along it. -/
def isGeodesic (Γ : Point2 → Fin 2 → Mat22) (γ : Curve) : Prop :=
  isParallel Γ γ (curveVelocity γ)

/-- The acceleration of a parameter curve, componentwise. -/
def curveAccel (γ : Curve) (t : ℝ) : Vel2 :=
  fun k => deriv (fun s : ℝ => curveVelocity γ s k) t

/-- **Bridge to the shooting method.** The Christoffel-symbol geodesic
equation of the Levi-Civita connection of the graph surface is the matrix
equation `γ̈ = geoAccel h γ γ̇` of `Brane.Shoot`. This is the concrete form
of the statement "geodesics are the critical points of the energy", and it
is the link between this module and the numerical integrators in
`Brane.Shooting`. -/
theorem isGeodesic_leviCivita_iff_Shoot (h : HeightFun) (γ : Curve) :
    isGeodesic (christoffel (gramMatrix h)) γ ↔
      ∀ t : ℝ, curveAccel γ t = Shoot.geoAccel h (γ t) (curveVelocity γ t) := by
  sorry

end

end Trans
end Brane
