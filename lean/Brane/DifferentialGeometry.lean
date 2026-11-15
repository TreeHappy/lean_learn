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

is a surface in `ℝ³`. This file develops its first-order geometry using
Mathlib's own linear algebra, so that everything below reuses existing API:

* vectors live in `EuclideanSpace ℝ (Fin 3)` (`PiLp 2`), so `‖·‖` and `⟪·, ·⟫`
  are Mathlib's norm and real inner product;
* the normal vector is built from Mathlib's `crossProduct` (`⨯₃` on
  `Fin 3 → ℝ`, transported across `WithLp.toLp` / `WithLp.ofLp`);
* the tangent plane is a `Submodule ℝ Vec3`, and its dimension is computed
  with `Module.finrank` via `finrank_span_eq_card`;
* the Jacobian is a `Matrix (Fin 3) (Fin 2) ℝ` acting by `Matrix.mulVec`;
* the Gram matrix of the two tangents is a `Matrix (Fin 2) (Fin 2) ℝ`, and its
  determinant equals `‖normal‖²` by Lagrange's identity (`cross_dot_cross`).

Along the way we use `LinearIndependent.pair_iff`, `Submodule.span_induction`,
`Submodule.mem_span_pair`, `real_inner_self_eq_norm_sq`, and the one-variable
derivative lemmas `deriv_add_const`, `deriv_const_mul_field`, `deriv_pow_field`.

## Main definitions

* `Brane.DiffGeom.Vec3` — the vector type `EuclideanSpace ℝ (Fin 3)`.
* `Brane.DiffGeom.graph` — the graph of a height function.
* `Brane.DiffGeom.tangentX`, `Brane.DiffGeom.tangentY` — tangent vectors.
* `Brane.DiffGeom.normal` — the normal vector, `cross (tangentX) (tangentY)`.
* `Brane.DiffGeom.tangentSpace` — the tangent plane as a submodule.
* `Brane.DiffGeom.jacobian` — the Jacobian matrix of the graph map.
* `Brane.DiffGeom.gramMatrix` — the Gram matrix of the two tangents.
* `Brane.DiffGeom.unitNormal` — the normalized normal.

## Tags

differential geometry, surfaces, tangent plane, normal vector, cross product
-/

@[expose] public section

namespace Brane
namespace DiffGeom

open Matrix WithLp
open scoped Matrix RealInnerProductSpace

noncomputable section

/-! ## Vectors in `ℝ³`

We work in `EuclideanSpace ℝ (Fin 3)`, Mathlib's standard model of `ℝ³` as an
inner product space. The helper `vec3` builds a vector from coordinates, and
`!₂[a, b, c]` is Mathlib's own notation for elements of `EuclideanSpace`. -/

/-- A vector in `ℝ³`, as Mathlib's Euclidean space over `Fin 3`. -/
abbrev Vec3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The vector with coordinates `(a, b, c)`. -/
def vec3 (a b c : ℝ) : Vec3 := !₂[a, b, c]

@[simp]
theorem vec3_apply_zero (a b c : ℝ) : vec3 a b c 0 = a := rfl

@[simp]
theorem vec3_apply_one (a b c : ℝ) : vec3 a b c 1 = b := rfl

@[simp]
theorem vec3_apply_two (a b c : ℝ) : vec3 a b c 2 = c := rfl

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
    vec3 a b c - vec3 a' b' c' = vec3 (a - a') (b - b') (c - c') := by
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

/-! ## The cross product on `ℝ³`

Mathlib defines `crossProduct` (`⨯₃`) on the plain function type
`Fin 3 → R`. Since `EuclideanSpace ℝ (Fin 3)` is `Fin 3 → ℝ` wrapped in
`WithLp`, we transport it across `WithLp.toLp` / `WithLp.ofLp`. -/

/-- The cross product of two vectors in `ℝ³`, transported from Mathlib's
`crossProduct` on `Fin 3 → ℝ`. -/
def cross (a b : Vec3) : Vec3 :=
  toLp 2 (WithLp.ofLp a ⨯₃ WithLp.ofLp b)

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

/-! ## Graphs of height functions -/

/-- The graph of `h`, as a map `ℝ² → ℝ³`:
the input `(x, y)` is mapped to `(x, y, h x y)`. -/
def graph (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Vec3 :=
  vec3 p.1 p.2 (h p.1 p.2)

@[simp]
theorem graph_apply (h : ℝ → ℝ → ℝ) (x y : ℝ) :
    graph h (x, y) = vec3 x y (h x y) := rfl

@[simp]
theorem graph_fst (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : graph h p 0 = p.1 := rfl

@[simp]
theorem graph_snd (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : graph h p 1 = p.2 := rfl

@[simp]
theorem graph_height (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : graph h p 2 = h p.1 p.2 := rfl

/-- The tangent vector in the `x`-direction:
the derivative of `x ↦ (x, y, h x y)` at `x`. -/
def tangentX (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Vec3 :=
  vec3 1 0 (deriv (fun x => h x p.2) p.1)

/-- The tangent vector in the `y`-direction:
the derivative of `y ↦ (x, y, h x y)` at `y`. -/
def tangentY (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Vec3 :=
  vec3 0 1 (deriv (fun y => h p.1 y) p.2)

@[simp]
theorem tangentX_apply_zero (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : tangentX h p 0 = 1 := rfl

@[simp]
theorem tangentX_apply_one (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : tangentX h p 1 = 0 := rfl

@[simp]
theorem tangentX_apply_two (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    tangentX h p 2 = deriv (fun x => h x p.2) p.1 := rfl

@[simp]
theorem tangentY_apply_zero (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : tangentY h p 0 = 0 := rfl

@[simp]
theorem tangentY_apply_one (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : tangentY h p 1 = 1 := rfl

@[simp]
theorem tangentY_apply_two (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    tangentY h p 2 = deriv (fun y => h p.1 y) p.2 := rfl

/-- The normal vector, defined as the cross product of the two tangents. -/
def normal (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Vec3 :=
  cross (tangentX h p) (tangentY h p)

/-- The normal vector in coordinates: `(-∂h/∂x, -∂h/∂y, 1)`. -/
theorem normal_eq (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    normal h p = vec3 (-deriv (fun x => h x p.2) p.1)
      (-deriv (fun y => h p.1 y) p.2) 1 := by
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

/-! ## The tangent plane as a submodule -/

/-- The tangent space at a point, spanned by the coordinate tangents. -/
def tangentSpace (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Submodule ℝ Vec3 :=
  Submodule.span ℝ ({tangentX h p, tangentY h p} : Set Vec3)

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

/-! ## The Jacobian matrix -/

/-- The Jacobian of the graph map `(x, y) ↦ (x, y, h x y)`.
Its two columns are the coordinate tangents. -/
def jacobian (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![1, 0; 0, 1;
    deriv (fun x => h x p.2) p.1, deriv (fun y => h p.1 y) p.2]

/-- The Jacobian sends an `xy`-velocity to the corresponding tangent vector;
the result is lifted back into `EuclideanSpace` with `WithLp.toLp`. -/
theorem jacobian_mulVec (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (v : Fin 2 → ℝ) :
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
    v ∈ tangentSpace h p ↔ ∃ u : Fin 2 → ℝ, toLp 2 (jacobian h p *ᵥ u) = v := by
  rw [mem_tangentSpace_iff]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨![a, b], by simp [jacobian_mulVec]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u 0, u 1, by rw [jacobian_mulVec]⟩

/-! ## The tangent plane and the unit normal -/

/-- A point lies in the tangent plane when the difference to the surface point is
in the tangent space. -/
def tangentPlane (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Set Vec3 :=
  {q | q - graph h p ∈ tangentSpace h p}

theorem mem_tangentPlane_iff (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (q : Vec3) :
    q ∈ tangentPlane h p ↔ q - graph h p ∈ tangentSpace h p := Iff.rfl

/-- The normal annihilates every displacement inside the tangent plane. -/
theorem tangentPlane_inner_normal (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) {q : Vec3}
    (hq : q ∈ tangentPlane h p) : ⟪q - graph h p, normal h p⟫ = 0 :=
  normal_orthogonal_tangentSpace h p hq

/-- The unit normal vector. -/
def unitNormal (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Vec3 :=
  (‖normal h p‖)⁻¹ • normal h p

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

/-! ## The area element -/

/-- The squared norm of the normal is `1 + (∂h/∂x)² + (∂h/∂y)²`
(`real_inner_self_eq_norm_sq`). -/
theorem norm_sq_normal (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ‖normal h p‖ ^ 2 =
      1 + deriv (fun x => h x p.2) p.1 ^ 2 +
        deriv (fun y => h p.1 y) p.2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  rw [normal_eq, vec3_inner]
  ring

/-- The area element of a graph over a point: `√(1 + f_x² + f_y²)`.
This is the factor by which a small `xy`-rectangle is stretched by the graph. -/
theorem norm_normal (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    ‖normal h p‖ =
      Real.sqrt (1 + deriv (fun x => h x p.2) p.1 ^ 2 +
        deriv (fun y => h p.1 y) p.2 ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (normal h p)), norm_sq_normal]

/-- The Gram matrix of the two tangents, with entries given by the Mathlib
inner product. -/
def gramMatrix (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![⟪tangentX h p, tangentX h p⟫, ⟪tangentX h p, tangentY h p⟫;
     ⟪tangentY h p, tangentX h p⟫, ⟪tangentY h p, tangentY h p⟫]

/-- The determinant of the Gram matrix equals `‖normal‖²`
(Lagrange's identity, `inner_cross_self`). -/
theorem det_gramMatrix (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    (gramMatrix h p).det = ‖normal h p‖ ^ 2 := by
  rw [gramMatrix, Matrix.det_fin_two_of, ← real_inner_self_eq_norm_sq, normal,
    inner_cross_self, real_inner_comm (tangentY h p) (tangentX h p)]
  ring

/-! ## Examples -/

/-- A plane with slopes `a` and `b` and height `c` at the origin. -/
def planeHeight (a b c : ℝ) (x y : ℝ) : ℝ :=
  a * x + b * y + c

@[simp]
theorem deriv_planeHeight_x (a b c y x : ℝ) :
    deriv (fun t => planeHeight a b c t y) x = a := by
  simp only [planeHeight]
  rw [deriv_add_const, deriv_add_const, deriv_const_mul_field, deriv_id'']
  ring

@[simp]
theorem deriv_planeHeight_y (a b c x y : ℝ) :
    deriv (fun t => planeHeight a b c x t) y = b := by
  simp only [planeHeight]
  rw [deriv_add_const, deriv_const_add, deriv_const_mul_field, deriv_id'']
  ring

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

/-- The paraboloid `z = x² + y²`. -/
def bowlHeight (x y : ℝ) : ℝ :=
  x ^ 2 + y ^ 2

@[simp]
theorem deriv_bowlHeight_x (x y : ℝ) :
    deriv (fun t => bowlHeight t y) x = 2 * x := by
  simp only [bowlHeight]
  rw [deriv_add_const, deriv_pow_field]
  norm_num

@[simp]
theorem deriv_bowlHeight_y (x y : ℝ) :
    deriv (fun t => bowlHeight x t) y = 2 * y := by
  simp only [bowlHeight]
  rw [deriv_const_add, deriv_pow_field]
  norm_num

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

/-- The saddle `z = x² - y²`. -/
def saddleHeight (x y : ℝ) : ℝ :=
  x ^ 2 - y ^ 2

@[simp]
theorem deriv_saddleHeight_x (x y : ℝ) :
    deriv (fun t => saddleHeight t y) x = 2 * x := by
  simp only [saddleHeight]
  rw [deriv_sub_const, deriv_pow_field]
  norm_num

@[simp]
theorem deriv_saddleHeight_y (x y : ℝ) :
    deriv (fun t => saddleHeight x t) y = -(2 * y) := by
  simp only [saddleHeight]
  rw [deriv_const_sub, deriv_pow_field]
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

end

end DiffGeom
end Brane
