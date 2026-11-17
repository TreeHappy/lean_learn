/-
Copyright (c) 2026 Brane contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brane contributors
-/
module
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Tactic

/-!
# Differential geometry of graph surfaces

For a height function `h : ℝ → ℝ → ℝ`, the graph

`graph h (x, y) = (x, y, h x y)`

is a surface in `ℝ³`. This file develops its first- and second-order geometry
using Mathlib's own linear algebra, so that everything below reuses existing API:

* vectors live in `EuclideanSpace ℝ (Fin 3)` (`PiLp 2`), so `‖·‖` and `⟪·, ·⟫`
  are Mathlib's norm and real inner product;
* the normal vector is built from Mathlib's `crossProduct` (`⨯₃` on
  `Fin 3 → ℝ`, transported across `WithLp.toLp` / `WithLp.ofLp`);
* the tangent plane is a `Submodule ℝ Vec3`, and its dimension is computed
  with `Module.finrank` via `finrank_span_eq_card`;
* the Jacobian is a `Matrix (Fin 3) (Fin 2) ℝ` acting by `Matrix.mulVec`;
* the Gram matrix is exactly `Jᵀ * J`, where `J` is the Jacobian;
* second derivatives appear as the Jacobians of the tangents
  (`jacobianTangentX`, `jacobianTangentY`) and as the Hessian matrix;
* vector calculus of the surface: `gradient`, `directionalDerivative`,
  `divergence` (= the Laplacian `h_xx + h_yy`) and `curl`
  (= the mixed-partial difference `h_yx - h_xy`).

Along the way we use `LinearIndependent.pair_iff`, `Submodule.span_induction`,
`Submodule.mem_span_pair`, `real_inner_self_eq_norm_sq`, `cross_dot_cross`
(Lagrange's identity), and the one-variable derivative lemmas
`deriv_add_const`, `deriv_const_mul_field`, `deriv_pow_field`.

## Main definitions

* `Brane.DiffGeom.Vec3` — the vector type `EuclideanSpace ℝ (Fin 3)`;
  `Mat32`, `Mat22`, `Vel2` — the matrix and velocity shapes.
* `Brane.DiffGeom.graph` — the graph of a height function.
* `Brane.DiffGeom.partialX`, `partialY` — first partials of `h`;
  `partialXX`, `partialXY`, `partialYX`, `partialYY` — second partials.
* `Brane.DiffGeom.tangentX`, `tangentY` — tangent vectors;
  `tangentXX`, `tangentXY`, `tangentYX`, `tangentYY` — their derivatives.
* `Brane.DiffGeom.normal` — the normal vector, `cross (tangentX) (tangentY)`.
* `Brane.DiffGeom.tangentSpace` — the tangent plane as a submodule.
* `Brane.DiffGeom.jacobian` — the Jacobian matrix of the graph map;
  `jacobianTangentX`, `jacobianTangentY` — Jacobians of the tangents.
* `Brane.DiffGeom.hessian` — the `2×2` Hessian of `h`.
* `Brane.DiffGeom.gramMatrix` — the Gram matrix of the two tangents,
  equal to `Jᵀ * J`.
* `Brane.DiffGeom.gradient`, `directionalDerivative`, `divergence`, `curl`.
* `Brane.DiffGeom.unitNormal` — the normalized normal.

## Tags

differential geometry, surfaces, tangent plane, normal vector, cross product,
second derivative, Hessian, gradient, divergence, curl
-/

@[expose] public section

namespace Brane
namespace DiffGeom

open Matrix WithLp
open scoped Matrix RealInnerProductSpace

noncomputable section

/-! ## Definitions

All of the objects of the theory, without any proofs. Each `def` is followed
by its definitional equations (`rfl` lemmas), which we mark `@[simp]` so that
later proofs can compute coordinates directly. -/

/-- A vector in `ℝ³`, as Mathlib's Euclidean space over `Fin 3`. -/
abbrev Vec3 : Type := EuclideanSpace ℝ (Fin 3)

/-- A `3×2` real matrix: the shape of the Jacobians of `ℝ² → ℝ³` maps. -/
abbrev Mat32 : Type := Matrix (Fin 3) (Fin 2) ℝ

/-- A `2×2` real matrix: the shape of the Hessian and the Gram matrix. -/
abbrev Mat22 : Type := Matrix (Fin 2) (Fin 2) ℝ

/-- A parameter-space velocity: an element of the domain `ℝ²` as a function
`Fin 2 → ℝ`, the thing a Jacobian acts on by `Matrix.mulVec`. -/
abbrev Vel2 : Type := Fin 2 → ℝ

/-! ### Type synonyms for the roles a type plays

Everything below is a *pure type synonym*: each `abbrev` is definitionally
equal to the type it abbreviates, so all existing lemmas and instances apply
unchanged. Their only job is documentation-by-types: a signature can say
whether an argument is meant as a plane point, a tangent, a normal, ... -/

/-- A point of the parameter plane: coordinates `(x, y)`. -/
abbrev Point2 : Type := ℝ × ℝ

/-- A point of ambient `ℝ³`, e.g. the position of the marble on the surface. -/
abbrev Point3 : Type := Vec3

/-- A height function over the parameter plane: the abstract input of the
whole theory. -/
abbrev HeightFun : Type := ℝ → ℝ → ℝ

/-- A tangent vector of the surface at some point. -/
abbrev Tangent : Type := Vec3

/-- A normal vector of the surface at some point. -/
abbrev Normal : Type := Vec3

/-- An acceleration vector in the parameter plane. -/
abbrev Accel2 : Type := Vel2

/-- An acceleration vector in ambient `ℝ³`. -/
abbrev Accel3 : Type := Vec3

/-- The vector with coordinates `(a, b, c)`. -/
def vec3 (a b c : ℝ) : Vec3 := !₂[a, b, c]

/-- The cross product of two vectors in `ℝ³`, transported from Mathlib's
`crossProduct` on `Fin 3 → ℝ`. -/
def cross (a b : Vec3) : Vec3 :=
  toLp 2 (WithLp.ofLp a ⨯₃ WithLp.ofLp b)

/-- The graph of `h`, as a map from the parameter plane to `ℝ³`:
the input `(x, y)` is mapped to `(x, y, h x y)`. -/
def graph (h : HeightFun) (p : Point2) : Point3 :=
  vec3 p.1 p.2 (h p.1 p.2)

/-- The first partial derivative of `h` with respect to its first argument:
`∂h/∂x (x, y) = deriv (fun t => h t y) x`. -/
def partialX (h : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => h t y) x

/-- The first partial derivative of `h` with respect to its second argument:
`∂h/∂y (x, y) = deriv (fun t => h x t) y`. -/
def partialY (h : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => h x t) y

/-- The second partial `∂²h/∂x²`. -/
def partialXX (h : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => partialX h t y) x

/-- The mixed second partial `∂²h/∂y∂x`: the `y`-derivative of `∂h/∂x`. -/
def partialXY (h : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => partialX h x t) y

/-- The mixed second partial `∂²h/∂x∂y`: the `x`-derivative of `∂h/∂y`. -/
def partialYX (h : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => partialY h t y) x

/-- The second partial `∂²h/∂y²`. -/
def partialYY (h : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => partialY h x t) y

/-- The tangent vector in the `x`-direction:
the derivative of `x ↦ (x, y, h x y)` at `x`. -/
def tangentX (h : HeightFun) (p : Point2) : Tangent :=
  vec3 1 0 (partialX h p.1 p.2)

/-- The tangent vector in the `y`-direction:
the derivative of `y ↦ (x, y, h x y)` at `y`. -/
def tangentY (h : HeightFun) (p : Point2) : Tangent :=
  vec3 0 1 (partialY h p.1 p.2)

/-- The derivative of the `x`-tangent with respect to `x`: `∂²σ/∂x²`. -/
def tangentXX (h : HeightFun) (p : Point2) : Tangent := vec3 0 0 (partialXX h p.1 p.2)

/-- The derivative of the `x`-tangent with respect to `y`: `∂²σ/∂y∂x`. -/
def tangentXY (h : HeightFun) (p : Point2) : Tangent := vec3 0 0 (partialXY h p.1 p.2)

/-- The derivative of the `y`-tangent with respect to `x`: `∂²σ/∂x∂y`. -/
def tangentYX (h : HeightFun) (p : Point2) : Tangent := vec3 0 0 (partialYX h p.1 p.2)

/-- The derivative of the `y`-tangent with respect to `y`: `∂²σ/∂y²`. -/
def tangentYY (h : HeightFun) (p : Point2) : Tangent := vec3 0 0 (partialYY h p.1 p.2)

/-- The normal vector, defined as the cross product of the two tangents. -/
def normal (h : HeightFun) (p : Point2) : Normal :=
  cross (tangentX h p) (tangentY h p)

/-- The tangent space at a point, spanned by the coordinate tangents. -/
def tangentSpace (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Submodule ℝ Vec3 :=
  Submodule.span ℝ ({tangentX h p, tangentY h p} : Set Vec3)

/-- A point lies in the tangent plane when the difference to the surface point
is in the tangent space. -/
def tangentPlane (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Set Vec3 :=
  {q | q - graph h p ∈ tangentSpace h p}

/-- The Jacobian of the graph map `(x, y) ↦ (x, y, h x y)`.
Its two columns are the coordinate tangents. -/
def jacobian (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Mat32 :=
  !![1, 0; 0, 1; partialX h p.1 p.2, partialY h p.1 p.2]

/-- The Jacobian of the `x`-tangent: its columns are the derivatives of
`tangentX` in the `x`- and `y`-directions (`tangentXX`, `tangentXY`). -/
def jacobianTangentX (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Mat32 :=
  !![0, 0; 0, 0; partialXX h p.1 p.2, partialXY h p.1 p.2]

/-- The Jacobian of the `y`-tangent: its columns are the derivatives of
`tangentY` in the `x`- and `y`-directions (`tangentYX`, `tangentYY`). -/
def jacobianTangentY (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Mat32 :=
  !![0, 0; 0, 0; partialYX h p.1 p.2, partialYY h p.1 p.2]

/-- The Hessian of `h`: the `2×2` matrix of second partials. -/
def hessian (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Mat22 :=
  !![partialXX h p.1 p.2, partialXY h p.1 p.2;
     partialYX h p.1 p.2, partialYY h p.1 p.2]

/-- The Gram matrix of the two tangents, with entries given by the Mathlib
inner product. -/
def gramMatrix (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Mat22 :=
  !![⟪tangentX h p, tangentX h p⟫, ⟪tangentX h p, tangentY h p⟫;
     ⟪tangentY h p, tangentX h p⟫, ⟪tangentY h p, tangentY h p⟫]

/-- The gradient of `h`, as a horizontal vector in `ℝ³`:
`(∂h/∂x, ∂h/∂y, 0)`. -/
def gradient (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Vec3 :=
  vec3 (partialX h p.1 p.2) (partialY h p.1 p.2) 0

/-- The directional derivative of `h` along a vector `v`:
the inner product of the gradient with `v`. -/
def directionalDerivative (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (v : Vec3) : ℝ :=
  ⟪gradient h p, v⟫

/-- The divergence of the gradient field of `h`, i.e. the Laplacian:
`∂²h/∂x² + ∂²h/∂y²`. -/
def divergence (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  partialXX h p.1 p.2 + partialYY h p.1 p.2

/-- The (scalar) curl of the gradient field of `h`:
the mixed-partial difference `∂²h/∂x∂y - ∂²h/∂y∂x`. -/
def curl (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  partialYX h p.1 p.2 - partialXY h p.1 p.2

/-- The unit normal vector. -/
def unitNormal (h : HeightFun) (p : Point2) : Normal :=
  (‖normal h p‖)⁻¹ • normal h p

/-! ### Definitional equations

`rfl` lemmas spelling out each definition coordinatewise. -/

@[simp]
theorem vec3_apply_zero (a b c : ℝ) : vec3 a b c 0 = a := rfl

@[simp]
theorem vec3_apply_one (a b c : ℝ) : vec3 a b c 1 = b := rfl

@[simp]
theorem vec3_apply_two (a b c : ℝ) : vec3 a b c 2 = c := rfl

@[simp]
theorem graph_fst (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : graph h p 0 = p.1 := rfl

@[simp]
theorem graph_snd (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : graph h p 1 = p.2 := rfl

@[simp]
theorem graph_height (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : graph h p 2 = h p.1 p.2 := rfl

@[simp]
theorem tangentX_apply_zero (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : tangentX h p 0 = 1 := rfl

@[simp]
theorem tangentX_apply_one (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : tangentX h p 1 = 0 := rfl

@[simp]
theorem tangentX_apply_two (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    tangentX h p 2 = partialX h p.1 p.2 := rfl

@[simp]
theorem tangentY_apply_zero (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : tangentY h p 0 = 0 := rfl

@[simp]
theorem tangentY_apply_one (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : tangentY h p 1 = 1 := rfl

@[simp]
theorem tangentY_apply_two (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    tangentY h p 2 = partialY h p.1 p.2 := rfl

@[simp]
theorem tangentXX_apply_two (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    tangentXX h p 2 = partialXX h p.1 p.2 := rfl

@[simp]
theorem tangentXY_apply_two (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    tangentXY h p 2 = partialXY h p.1 p.2 := rfl

@[simp]
theorem tangentYX_apply_two (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    tangentYX h p 2 = partialYX h p.1 p.2 := rfl

@[simp]
theorem tangentYY_apply_two (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    tangentYY h p 2 = partialYY h p.1 p.2 := rfl

/-! ## Proofs

From here on, everything is proved using Mathlib's existing API. -/

/-! ### Coordinate algebra of `vec3` -/

@[simp]
theorem vec3_zero : vec3 0 0 0 = (0 : Vec3) := by
  ext i
  fin_cases i <;> rfl

@[simp]
theorem vec3_add (a b c a' b' c' : ℝ) :
    vec3 a b c + vec3 a' b' c' = vec3 (a + a') (b + b') (c + c') := by
  ext i
  fin_cases i <;> rfl

@[simp]
theorem vec3_sub (a b c a' b' c' : ℝ) :
    vec3 a b c - vec3 a' b' c' = vec3 (a - a') (b - b') (c + -(c')) := by
  ext i
  fin_cases i <;> rfl

@[simp]
theorem vec3_smul (r a b c : ℝ) : r • vec3 a b c = vec3 (r * a) (r * b) (r * c) := by
  ext i
  fin_cases i <;> rfl

/-- A coordinate vector is zero exactly when all its coordinates are. -/
theorem vec3_eq_zero_iff (a b c : ℝ) : vec3 a b c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hof : WithLp.ofLp (vec3 a b c) = WithLp.ofLp (0 : Vec3) := by rw [h]
    refine ⟨?_, ?_, ?_⟩
    · simpa using congrFun hof 0
    · simpa using congrFun hof 1
    · simpa using congrFun hof 2
  · rintro ⟨rfl, rfl, rfl⟩
    ext i
    fin_cases i <;> simp [vec3]

/-- The Mathlib inner product on `ℝ³` computes coordinatewise. -/
theorem vec3_inner (a b c a' b' c' : ℝ) :
    ⟪vec3 a b c, vec3 a' b' c'⟫ = a * a' + b * b' + c * c' := by
  simp [vec3, EuclideanSpace.inner_toLp_toLp, mul_comm]
  ring

/-- The Mathlib norm on `ℝ³` is the square root of the sum of squares. -/
theorem norm_vec3 (a b c : ℝ) :
    ‖vec3 a b c‖ = Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [vec3, Fin.sum_univ_three]

/-! ### The cross product on `ℝ³`

Mathlib defines `crossProduct` (`⨯₃`) on the plain function type `Fin 3 → R`.
Since `EuclideanSpace ℝ (Fin 3)` is `Fin 3 → ℝ` wrapped in `WithLp`, we
transport it across `WithLp.toLp` / `WithLp.ofLp`. -/

/-- The cross product in coordinates. -/
theorem cross_coordinates (a b : Vec3) :
    cross a b =
      vec3 (a 1 * b 2 - a 2 * b 1) (a 2 * b 0 - a 0 * b 2) (a 0 * b 1 - a 1 * b 0) := by
  ext i
  fin_cases i <;> simp [cross, vec3, cross_apply, PiLp.toLp_apply]

/-- The inner product agrees with Mathlib's `dotProduct` on the underlying
function vectors. -/
theorem inner_eq_dot (u v : Vec3) :
    ⟪u, v⟫ = WithLp.ofLp u ⬝ᵥ WithLp.ofLp v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- The cross product is orthogonal to its first argument. -/
theorem inner_cross_left (a b : Vec3) : ⟪a, cross a b⟫ = 0 := by
  rw [inner_eq_dot, cross, WithLp.ofLp_toLp, dot_self_cross]

/-- The cross product is orthogonal to its second argument. -/
theorem inner_cross_right (a b : Vec3) : ⟪cross a b, b⟫ = 0 := by
  rw [inner_eq_dot, cross, WithLp.ofLp_toLp, dotProduct_comm, dot_cross_self]

/-- Swapping the factors negates the cross product. -/
theorem cross_swap (a b : Vec3) : cross b a = -(cross a b) := by
  ext i
  fin_cases i <;> simp [cross, cross_apply] <;> ring

/-- Lagrange's identity: the squared norm of a cross product. -/
theorem inner_cross_self (u v : Vec3) :
    ⟪cross u v, cross u v⟫ = ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2 := by
  simp only [inner_eq_dot, cross]
  rw [cross_dot_cross, dotProduct_comm (WithLp.ofLp v) (WithLp.ofLp u)]
  ring

/-! ### The normal vector -/

/-- The normal vector in coordinates: `(-∂h/∂x, -∂h/∂y, 1)`. -/
theorem normal_eq (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    normal h p = vec3 (-partialX h p.1 p.2) (-partialY h p.1 p.2) 1 := by
  rw [normal, tangentX, tangentY, cross_coordinates]
  simp

/-- A coordinate vector with third coordinate `1` is never zero. -/
theorem vec3_ne_zero_of_third (a b : ℝ) : vec3 a b 1 ≠ 0 := by
  intro hzero
  have hof : WithLp.ofLp (vec3 a b 1) = WithLp.ofLp (0 : Vec3) := by rw [hzero]
  have h2 := congrFun hof 2
  simp at h2

/-- The normal vector is never zero, since its third coordinate is `1`. -/
theorem normal_ne_zero (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : normal h p ≠ 0 := by
  rw [normal_eq]
  exact vec3_ne_zero_of_third _ _

/-- The first tangent is orthogonal to the normal. -/
@[simp]
theorem tangentX_inner_normal (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ⟪tangentX h p, normal h p⟫ = 0 := by
  rw [normal]
  exact inner_cross_left (tangentX h p) (tangentY h p)

/-- The second tangent is orthogonal to the normal. -/
@[simp]
theorem tangentY_inner_normal (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ⟪tangentY h p, normal h p⟫ = 0 := by
  rw [normal, real_inner_comm]
  exact inner_cross_right (tangentX h p) (tangentY h p)

/-! ### Inner products of the tangents -/

/-- The squared length of the `x`-tangent: `1 + (∂h/∂x)²`. -/
@[simp]
theorem inner_tangentX_tangentX (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ⟪tangentX h p, tangentX h p⟫ = 1 + partialX h p.1 p.2 ^ 2 := by
  rw [tangentX, vec3_inner]
  ring

/-- The inner product of the two tangents. -/
@[simp]
theorem inner_tangentX_tangentY (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ⟪tangentX h p, tangentY h p⟫ =
      partialX h p.1 p.2 * partialY h p.1 p.2 := by
  rw [tangentX, tangentY, vec3_inner]
  simp

/-- The squared length of the `y`-tangent: `1 + (∂h/∂y)²`. -/
@[simp]
theorem inner_tangentY_tangentY (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ⟪tangentY h p, tangentY h p⟫ = 1 + partialY h p.1 p.2 ^ 2 := by
  rw [tangentY, vec3_inner]
  ring

@[simp]
theorem norm_sq_tangentX (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ‖tangentX h p‖ ^ 2 = 1 + partialX h p.1 p.2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_tangentX_tangentX]

@[simp]
theorem norm_sq_tangentY (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ‖tangentY h p‖ ^ 2 = 1 + partialY h p.1 p.2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_tangentY_tangentY]

/-! ### The tangent plane as a submodule -/

theorem tangentX_mem_tangentSpace (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    tangentX h p ∈ tangentSpace h p :=
  Submodule.subset_span (by simp)

theorem tangentY_mem_tangentSpace (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    tangentY h p ∈ tangentSpace h p :=
  Submodule.subset_span (by simp)

/-- A vector is in the tangent space exactly when it is a linear combination of
the two coordinate tangents (`Submodule.mem_span_pair`). -/
theorem mem_tangentSpace_iff (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (v : Vec3) :
    v ∈ tangentSpace h p ↔ ∃ a b : ℝ, a • tangentX h p + b • tangentY h p = v := by
  rw [tangentSpace, Submodule.mem_span_pair]

/-- Every vector in the tangent space is orthogonal to the normal, proved with
`Submodule.span_induction`. -/
theorem normal_orthogonal_tangentSpace (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) {v : Vec3}
    (hv : v ∈ tangentSpace h p) : ⟪v, normal h p⟫ = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact tangentX_inner_normal h p
    · exact tangentY_inner_normal h p
  · simp
  · intro u w _ _ hu hw
    rw [inner_add_left, hu, hw, add_zero]
  · intro r u _ hu
    rw [real_inner_smul_left, hu, mul_zero]

/-- The two coordinate tangents are linearly independent
(`LinearIndependent.pair_iff`). -/
theorem linearIndependent_tangents (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    LinearIndependent ℝ ![tangentX h p, tangentY h p] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hof : WithLp.ofLp (s • tangentX h p + t • tangentY h p) =
      WithLp.ofLp (0 : Vec3) := by
    rw [hst]
  have h0 := congrFun hof 0
  have h1 := congrFun hof 1
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_zero, tangentX, tangentY,
    vec3, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero, zero_add] at h0 h1
  exact ⟨h0, h1⟩

/-- The tangent plane is two-dimensional: it is spanned by two independent
vectors (`finrank_span_eq_card`). -/
theorem finrank_tangentSpace (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    Module.finrank ℝ (tangentSpace h p) = 2 := by
  rw [tangentSpace]
  have hspan : ({tangentX h p, tangentY h p} : Set Vec3) =
      Set.range ![tangentX h p, tangentY h p] := by
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
  rw [hspan, finrank_span_eq_card (linearIndependent_tangents h p)]
  simp

theorem mem_tangentPlane_iff (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (q : Vec3) :
    q ∈ tangentPlane h p ↔ q - graph h p ∈ tangentSpace h p := Iff.rfl

/-- The normal annihilates every displacement inside the tangent plane. -/
theorem tangentPlane_inner_normal (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) {q : Vec3}
    (hq : q ∈ tangentPlane h p) : ⟪q - graph h p, normal h p⟫ = 0 :=
  normal_orthogonal_tangentSpace h p hq

/-! ### The Jacobian and its action -/

/-- The Jacobian sends an `xy`-velocity to the corresponding tangent vector;
the result is lifted back into `EuclideanSpace` with `WithLp.toLp`. -/
theorem jacobian_mulVec (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (v : Vel2) :
    toLp 2 (jacobian h p *ᵥ v) = v 0 • tangentX h p + v 1 • tangentY h p := by
  ext i
  fin_cases i <;> simp [jacobian, tangentX, tangentY, vec3, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

/-- The first column of the Jacobian is the `x`-tangent. -/
@[simp]
theorem jacobian_mulVec_zero (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    toLp 2 (jacobian h p *ᵥ ![1, 0]) = tangentX h p := by
  rw [jacobian_mulVec]
  simp

/-- The second column of the Jacobian is the `y`-tangent. -/
@[simp]
theorem jacobian_mulVec_one (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    toLp 2 (jacobian h p *ᵥ ![0, 1]) = tangentY h p := by
  rw [jacobian_mulVec]
  simp

/-- The tangent space is the range of the Jacobian. -/
theorem mem_tangentSpace_iff_jacobian (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (v : Vec3) :
    v ∈ tangentSpace h p ↔ ∃ u : Vel2, toLp 2 (jacobian h p *ᵥ u) = v := by
  rw [mem_tangentSpace_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨![a, b], by simp [jacobian_mulVec]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u 0, u 1, by rw [jacobian_mulVec]⟩

/-! ### The Jacobians of the tangents (second derivatives) -/

/-- Multiplying the Jacobian of the `x`-tangent by an `xy`-velocity gives the
corresponding combination of the second derivatives `tangentXX`, `tangentXY`. -/
theorem jacobianTangentX_mulVec (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (v : Vel2) :
    toLp 2 (jacobianTangentX h p *ᵥ v) =
      v 0 • tangentXX h p + v 1 • tangentXY h p := by
  ext i
  fin_cases i <;> simp [jacobianTangentX, tangentXX, tangentXY, vec3, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

/-- Multiplying the Jacobian of the `y`-tangent by an `xy`-velocity gives the
corresponding combination of the second derivatives `tangentYX`, `tangentYY`. -/
theorem jacobianTangentY_mulVec (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (v : Vel2) :
    toLp 2 (jacobianTangentY h p *ᵥ v) =
      v 0 • tangentYX h p + v 1 • tangentYY h p := by
  ext i
  fin_cases i <;> simp [jacobianTangentY, tangentYX, tangentYY, vec3, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

/-- The bottom row of the Jacobian of the `x`-tangent is the first row of the
Hessian. -/
theorem jacobianTangentX_apply (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (j : Fin 2) :
    jacobianTangentX h p 2 j = hessian h p 0 j := by
  fin_cases j <;> simp [jacobianTangentX, hessian]

/-- The bottom row of the Jacobian of the `y`-tangent is the second row of the
Hessian. -/
theorem jacobianTangentY_apply (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (j : Fin 2) :
    jacobianTangentY h p 2 j = hessian h p 1 j := by
  fin_cases j <;> simp [jacobianTangentY, hessian]

/-! ### The Gram matrix

The Gram matrix of the tangents is exactly `Jᵀ * J`, where `J` is the
Jacobian of the graph map. -/

/-- The Gram matrix equals `Jᵀ * J`. -/
theorem gramMatrix_eq_transpose_mul (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    gramMatrix h p = (jacobian h p)ᵀ * jacobian h p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramMatrix, jacobian, Matrix.mul_apply, Fin.sum_univ_three, real_inner_comm]
  all_goals ring

/-- The determinant of the Gram matrix is the first fundamental form:
`1 + (∂h/∂x)² + (∂h/∂y)²`. -/
theorem det_gramMatrix_eq (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    (gramMatrix h p).det =
      1 + partialX h p.1 p.2 ^ 2 + partialY h p.1 p.2 ^ 2 := by
  rw [gramMatrix, Matrix.det_fin_two_of]
  simp only [inner_tangentX_tangentX, inner_tangentX_tangentY, inner_tangentY_tangentY,
    real_inner_comm]
  ring

/-- The determinant of the Gram matrix equals `‖normal‖²`
(Lagrange's identity, `inner_cross_self`). -/
theorem det_gramMatrix (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    (gramMatrix h p).det = ‖normal h p‖ ^ 2 := by
  rw [gramMatrix, Matrix.det_fin_two_of, ← real_inner_self_eq_norm_sq, normal,
    inner_cross_self, real_inner_comm (tangentY h p) (tangentX h p)]
  ring

/-- The squared norm of the normal is `1 + (∂h/∂x)² + (∂h/∂y)²`
(`real_inner_self_eq_norm_sq`). -/
theorem norm_sq_normal (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ‖normal h p‖ ^ 2 =
      1 + partialX h p.1 p.2 ^ 2 + partialY h p.1 p.2 ^ 2 := by
  rw [← det_gramMatrix, det_gramMatrix_eq]

/-- The area element of a graph over a point: `√(1 + f_x² + f_y²)`.
This is the factor by which a small `xy`-rectangle is stretched by the graph. -/
theorem norm_normal (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ‖normal h p‖ =
      Real.sqrt (1 + partialX h p.1 p.2 ^ 2 + partialY h p.1 p.2 ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (normal h p)), norm_sq_normal]

/-- The unit normal is still orthogonal to the first tangent. -/
@[simp]
theorem unitNormal_inner_tangentX (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ⟪unitNormal h p, tangentX h p⟫ = 0 := by
  rw [unitNormal, real_inner_smul_left, real_inner_comm, tangentX_inner_normal h p]
  simp

/-- The unit normal is still orthogonal to the second tangent. -/
@[simp]
theorem unitNormal_inner_tangentY (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ⟪unitNormal h p, tangentY h p⟫ = 0 := by
  rw [unitNormal, real_inner_smul_left, real_inner_comm, tangentY_inner_normal h p]
  simp

/-- The unit normal really is a unit vector. -/
theorem norm_unitNormal (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ‖unitNormal h p‖ = 1 := by
  rw [unitNormal, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (normal_ne_zero h p))

/-! ### Gradient, directional derivative, divergence and curl -/

/-- The gradient as a vector in `ℝ³` is horizontal:
it is orthogonal to the vertical direction. -/
@[simp]
theorem gradient_eq (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    gradient h p = vec3 (partialX h p.1 p.2) (partialY h p.1 p.2) 0 := rfl

/-- The gradient pairs with the `x`-tangent to give `∂h/∂x`. -/
@[simp]
theorem gradient_inner_tangentX (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ⟪gradient h p, tangentX h p⟫ = partialX h p.1 p.2 := by
  rw [gradient_eq, tangentX, vec3_inner]
  simp

/-- The gradient pairs with the `y`-tangent to give `∂h/∂y`. -/
@[simp]
theorem gradient_inner_tangentY (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ⟪gradient h p, tangentY h p⟫ = partialY h p.1 p.2 := by
  rw [gradient_eq, tangentY, vec3_inner]
  simp

/-- The directional derivative along a tangent combination is the
corresponding combination of partials. -/
theorem directionalDerivative_tangentCombination (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
    (a b : ℝ) :
    directionalDerivative h p (a • tangentX h p + b • tangentY h p) =
      a * partialX h p.1 p.2 + b * partialY h p.1 p.2 := by
  rw [directionalDerivative, inner_add_right, real_inner_smul_right, real_inner_smul_right,
    gradient_inner_tangentX, gradient_inner_tangentY]

/-- The divergence of a gradient field is zero when the mixed partials agree:
for `C²` functions, curl of grad vanishes. -/
theorem curl_eq_zero_of_eq (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ)
    (hsym : partialXY h p.1 p.2 = partialYX h p.1 p.2) : curl h p = 0 := by
  simp only [curl, hsym, sub_self]

/-! ### Examples

The three model surfaces: the plane, the paraboloid (bowl), and the saddle.
Each comes with its partial derivatives of both orders, tangents, normal, and
vector-calculus invariants. -/

/-- A plane with slopes `a` and `b` and height `c` at the origin. -/
def planeHeight (a b c : ℝ) (x y : ℝ) : ℝ :=
  a * x + b * y + c

@[simp]
theorem partialX_planeHeight (a b c x y : ℝ) :
    partialX (planeHeight a b c) x y = a := by
  simp only [partialX, planeHeight]
  rw [deriv_add_const, deriv_add_const, deriv_const_mul_field, deriv_id'']
  ring

@[simp]
theorem partialY_planeHeight (a b c x y : ℝ) :
    partialY (planeHeight a b c) x y = b := by
  simp only [partialY, planeHeight]
  rw [deriv_add_const, deriv_const_add, deriv_const_mul_field, deriv_id'']
  ring

@[simp]
theorem partialXX_planeHeight (a b c x y : ℝ) :
    partialXX (planeHeight a b c) x y = 0 := by
  simp only [partialXX, partialX_planeHeight]
  rw [deriv_const]

@[simp]
theorem partialXY_planeHeight (a b c x y : ℝ) :
    partialXY (planeHeight a b c) x y = 0 := by
  simp only [partialXY, partialX_planeHeight]
  rw [deriv_const]

@[simp]
theorem partialYX_planeHeight (a b c x y : ℝ) :
    partialYX (planeHeight a b c) x y = 0 := by
  simp only [partialYX, partialY_planeHeight]
  rw [deriv_const]

@[simp]
theorem partialYY_planeHeight (a b c x y : ℝ) :
    partialYY (planeHeight a b c) x y = 0 := by
  simp only [partialYY, partialY_planeHeight]
  rw [deriv_const]

/-- The paraboloid `z = x² + y²`. -/
def bowlHeight (x y : ℝ) : ℝ :=
  x ^ 2 + y ^ 2

@[simp]
theorem partialX_bowlHeight (x y : ℝ) : partialX bowlHeight x y = 2 * x := by
  simp only [partialX, bowlHeight]
  rw [deriv_add_const, deriv_pow_field]
  norm_num

@[simp]
theorem partialY_bowlHeight (x y : ℝ) : partialY bowlHeight x y = 2 * y := by
  simp only [partialY, bowlHeight]
  rw [deriv_const_add, deriv_pow_field]
  norm_num

@[simp]
theorem partialXX_bowlHeight (x y : ℝ) : partialXX bowlHeight x y = 2 := by
  simp only [partialXX, partialX_bowlHeight]
  rw [deriv_const_mul_field, deriv_id'']
  simp

@[simp]
theorem partialXY_bowlHeight (x y : ℝ) : partialXY bowlHeight x y = 0 := by
  simp only [partialXY, partialX_bowlHeight]
  rw [deriv_const]

@[simp]
theorem partialYX_bowlHeight (x y : ℝ) : partialYX bowlHeight x y = 0 := by
  simp only [partialYX, partialY_bowlHeight]
  rw [deriv_const]

@[simp]
theorem partialYY_bowlHeight (x y : ℝ) : partialYY bowlHeight x y = 2 := by
  simp only [partialYY, partialY_bowlHeight]
  rw [deriv_const_mul_field, deriv_id'']
  simp

/-- The saddle `z = x² - y²`. -/
def saddleHeight (x y : ℝ) : ℝ :=
  x ^ 2 - y ^ 2

@[simp]
theorem partialX_saddleHeight (x y : ℝ) : partialX saddleHeight x y = 2 * x := by
  simp only [partialX, saddleHeight]
  rw [deriv_sub_const, deriv_pow_field]
  norm_num

@[simp]
theorem partialY_saddleHeight (x y : ℝ) : partialY saddleHeight x y = -(2 * y) := by
  simp only [partialY, saddleHeight]
  rw [deriv_const_sub, deriv_pow_field]
  ring

@[simp]
theorem partialXX_saddleHeight (x y : ℝ) : partialXX saddleHeight x y = 2 := by
  simp only [partialXX, partialX_saddleHeight]
  rw [deriv_const_mul_field, deriv_id'']
  simp

@[simp]
theorem partialXY_saddleHeight (x y : ℝ) : partialXY saddleHeight x y = 0 := by
  simp only [partialXY, partialX_saddleHeight]
  rw [deriv_const]

@[simp]
theorem partialYX_saddleHeight (x y : ℝ) : partialYX saddleHeight x y = 0 := by
  simp only [partialYX, partialY_saddleHeight]
  rw [deriv_const]

@[simp]
theorem partialYY_saddleHeight (x y : ℝ) : partialYY saddleHeight x y = -(2 : ℝ) := by
  simp only [partialYY, partialY_saddleHeight]
  have hf : (fun t => -(2 * t)) = fun t => (-2 : ℝ) * t := by
    funext t; simp
  rw [hf, deriv_const_mul_field, deriv_id'']
  simp

/-! ### Tangents, normals and areas of the examples -/

@[simp]
theorem tangentX_planeHeight (a b c x y : ℝ) :
    tangentX (planeHeight a b c) (x, y) = vec3 1 0 a := by
  simp [tangentX]

@[simp]
theorem tangentY_planeHeight (a b c x y : ℝ) :
    tangentY (planeHeight a b c) (x, y) = vec3 0 1 b := by
  simp [tangentY]

@[simp]
theorem normal_planeHeight (a b c x y : ℝ) :
    normal (planeHeight a b c) (x, y) = vec3 (-a) (-b) 1 := by
  rw [normal_eq]
  simp

@[simp]
theorem tangentX_bowlHeight (x y : ℝ) :
    tangentX bowlHeight (x, y) = vec3 1 0 (2 * x) := by
  simp [tangentX]

@[simp]
theorem tangentY_bowlHeight (x y : ℝ) :
    tangentY bowlHeight (x, y) = vec3 0 1 (2 * y) := by
  simp [tangentY]

@[simp]
theorem normal_bowlHeight (x y : ℝ) :
    normal bowlHeight (x, y) = vec3 (-(2 * x)) (-(2 * y)) 1 := by
  rw [normal_eq]
  simp

/-- The area element of the paraboloid: `‖normal‖² = 1 + 4x² + 4y²`. -/
theorem norm_sq_normal_bowlHeight (x y : ℝ) :
    ‖normal bowlHeight (x, y)‖ ^ 2 = 1 + 4 * x ^ 2 + 4 * y ^ 2 := by
  rw [norm_sq_normal]
  simp
  ring

@[simp]
theorem tangentX_saddleHeight (x y : ℝ) :
    tangentX saddleHeight (x, y) = vec3 1 0 (2 * x) := by
  simp [tangentX]

@[simp]
theorem tangentY_saddleHeight (x y : ℝ) :
    tangentY saddleHeight (x, y) = vec3 0 1 (-(2 * y)) := by
  simp [tangentY]

@[simp]
theorem normal_saddleHeight (x y : ℝ) :
    normal saddleHeight (x, y) = vec3 (-(2 * x)) (2 * y) 1 := by
  rw [normal_eq]
  simp

/-- The area element of the saddle: `‖normal‖² = 1 + 4x² + 4y²`. -/
theorem norm_sq_normal_saddleHeight (x y : ℝ) :
    ‖normal saddleHeight (x, y)‖ ^ 2 = 1 + 4 * x ^ 2 + 4 * y ^ 2 := by
  rw [norm_sq_normal]
  simp
  ring

/-- The Gram matrix of the paraboloid at `(x, y)`. -/
theorem gramMatrix_bowlHeight (x y : ℝ) :
    gramMatrix bowlHeight (x, y) = !![1 + 4 * x ^ 2, 4 * x * y; 4 * x * y, 1 + 4 * y ^ 2] := by
  rw [gramMatrix_eq_transpose_mul, jacobian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  all_goals ring

/-- The area element of the plane is constant: `‖normal‖² = 1 + a² + b²`. -/
theorem norm_sq_normal_planeHeight (a b c x y : ℝ) :
    ‖normal (planeHeight a b c) (x, y)‖ ^ 2 = 1 + a ^ 2 + b ^ 2 := by
  rw [norm_sq_normal]
  simp

/-! ### Vector calculus of the examples -/

/-- For all three examples the mixed partials agree, so curl of grad is `0`. -/
example (x y : ℝ) : curl bowlHeight (x, y) = 0 := by
  simp [curl]

example (x y : ℝ) : curl saddleHeight (x, y) = 0 := by
  simp [curl]

example (a b c x y : ℝ) : curl (planeHeight a b c) (x, y) = 0 := by
  simp [curl]

/-- The Laplacian of the bowl is `4` everywhere. -/
example (x y : ℝ) : divergence bowlHeight (x, y) = 4 := by
  simp only [divergence]
  norm_num

/-- The Laplacian of the saddle is `0` (it is harmonic). -/
example (x y : ℝ) : divergence saddleHeight (x, y) = 0 := by
  simp [divergence]

/-- The plane is harmonic as well. -/
example (a b c x y : ℝ) : divergence (planeHeight a b c) (x, y) = 0 := by
  simp [divergence]

end

end DiffGeom
end Brane
