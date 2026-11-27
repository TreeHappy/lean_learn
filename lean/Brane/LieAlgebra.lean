/-
Copyright (c) 2026 Brane contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brane contributors
-/
import Brane.GeometricAlgebra
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Derivation.Basic

/-!
# Lie algebras: the cross product and `so(3)`

This file instantiates Mathlib's Lie-algebra API with the concrete vector
space `Vec3 = ℝ³` of `Brane.DiffGeom`. The bracket is the cross product, and
the Jacobi identity is proved by transporting Mathlib's `jacobi_cross`
through the `WithLp` wrapper that defines `cross`.

The dictionary:

* a **Lie ring** is an additive group with an alternating bilinear bracket
  satisfying the Jacobi identity (`LieRing`);
* a **Lie algebra** is a Lie ring that is also a module, with the bracket
  compatible with scalar multiplication (`LieAlgebra`);
* on `Vec3`, the bracket is the cross product, so `Vec3` is the Lie algebra
  `so(3)` up to the standard identification with skew-symmetric matrices;
* the **adjoint action** `ad u = [u, ·]` is a linear endomorphism
  (`crossAdjoint`), and the Jacobi identity says it is a derivation of the
  bracket (`crossAdjoint_leibniz`);
* the **hat map** `hatMatrix` sends a vector to the skew-symmetric matrix of
  cross product by that vector, giving the equivalence
  `Vec3 ≃ₗ⁅ℝ⁆ so(3)` (`so3MatrixEquiv`).

## Main definitions

* `Brane.Lie.crossLieRing`, `crossLieAlgebra`: `Vec3` as a Lie algebra;
* `Brane.Lie.crossAdjoint`: the adjoint endomorphism `v ↦ [u, v]`;
* `Brane.Lie.hatMatrix`: the skew-symmetric matrix of a vector;
* `Brane.Lie.so3MatrixEquiv`: the Lie-algebra equivalence with `so(3)`.

## Status of proofs

The cross-product Lie-ring axioms and Jacobi are proved. The skew-symmetry
of `hatMatrix` and its commutator identity are proved. The final Lie-algebra
equivalence `so3MatrixEquiv` is left as `sorry`; it needs the explicit
inverse of the hat map and the compatibility of the two brackets.

## Tags

Lie algebra, cross product, Jacobi identity, so(3), adjoint action,
derivation
-/

namespace Brane
namespace Lie

open DiffGeom
open scoped Matrix

noncomputable section

/-! ## The cross product as a Lie bracket -/

/-- The `Bracket` instance on `Vec3`: the cross product. -/
instance : Bracket Vec3 Vec3 := ⟨cross⟩

/-- The cross product is additive in its first argument (restated for the
Lie-bracket notation). -/
theorem bracket_add_left (u u' v : Vec3) :
    ⁅u + u', v⁆ = ⁅u, v⁆ + ⁅u', v⁆ :=
  Brane.GA.cross_add_left u u' v

/-- The cross product is additive in its second argument. -/
theorem bracket_add_right (u v v' : Vec3) :
    ⁅u, v + v'⁆ = ⁅u, v⁆ + ⁅u, v'⁆ :=
  Brane.GA.cross_add_right u v v'

/-- The cross product is alternating: `[u, u] = 0`. -/
theorem bracket_self (u : Vec3) : ⁅u, u⁆ = 0 :=
  Brane.GA.cross_self u

/-- The cross product is antisymmetric: `[u, v] = -[v, u]`. -/
theorem bracket_anticomm (u v : Vec3) : ⁅u, v⁆ = -⁅v, u⁆ := by
  change cross u v = -cross v u
  rw [cross_swap u v, neg_neg]

/-- The cross product is `ℝ`-linear in its second argument. -/
theorem bracket_smul_right (t : ℝ) (u v : Vec3) :
    ⁅u, t • v⁆ = t • ⁅u, v⁆ :=
  Brane.GA.cross_smul_right u t v

/-- The cross product is `ℝ`-linear in its first argument (derived from
antisymmetry and second-argument linearity). -/
theorem bracket_smul_left (t : ℝ) (u v : Vec3) :
    ⁅t • u, v⁆ = t • ⁅u, v⁆ :=
  Brane.GA.cross_smul_left t u v

/-- The cross product is additive in its second argument, written for
negation: `[u, -v] = -[u, v]`. -/
theorem bracket_neg_right (u v : Vec3) : ⁅u, -v⁆ = -⁅u, v⁆ := by
  change cross u (-v) = -cross u v
  simpa using Brane.GA.cross_smul_right u (-1) v

/-- The **Jacobi identity** for the cross product:
`[u, [v, w]] + [v, [w, u]] + [w, [u, v]] = 0`. -/
theorem bracket_jacobi (u v w : Vec3) :
    ⁅u, ⁅v, w⁆⁆ + ⁅v, ⁅w, u⁆⁆ + ⁅w, ⁅u, v⁆⁆ = 0 := by
  change cross u (cross v w) + cross v (cross w u) + cross w (cross u v) = 0
  rw [cross_coordinates, cross_coordinates, cross_coordinates, cross_coordinates,
    cross_coordinates, cross_coordinates]
  ext i
  fin_cases i <;> simp [vec3] <;> ring

/-- The **Leibniz form of Jacobi**: `ad u` is a derivation of the bracket,
`[u, [v, w]] = [[u, v], w] + [v, [u, w]]`. -/
theorem bracket_leibniz (u v w : Vec3) :
    ⁅u, ⁅v, w⁆⁆ = ⁅⁅u, v⁆, w⁆ + ⁅v, ⁅u, w⁆⁆ := by
  change cross u (cross v w) = cross (cross u v) w + cross v (cross u w)
  have h := bracket_jacobi u v w
  change cross u (cross v w) + cross v (cross w u) + cross w (cross u v) = 0 at h
  rw [cross_swap u w, cross_swap (cross u v) w] at h
  have hneg : cross v (-(cross u w)) = -cross v (cross u w) := by
    simpa using Brane.GA.cross_smul_right v (-1) (cross u w)
  rw [hneg] at h
  have h' : cross u (cross v w) - cross v (cross u w) - cross (cross u v) w = 0 := by
    simpa [sub_eq_add_neg] using h
  have h1 : cross u (cross v w) - cross v (cross u w) = cross (cross u v) w :=
    sub_eq_zero.mp h'
  exact sub_eq_iff_eq_add.mp h1

/-- `Vec3` with the cross product is a **Lie ring**. -/
instance crossLieRing : LieRing Vec3 where
  add_lie := Brane.GA.cross_add_left
  lie_add := Brane.GA.cross_add_right
  lie_self := Brane.GA.cross_self
  leibniz_lie := bracket_leibniz

/-- `Vec3` with the cross product is the **Lie algebra** `so(3)`. -/
instance crossLieAlgebra : LieAlgebra ℝ Vec3 where
  lie_smul := fun t x y => Brane.GA.cross_smul_right x t y

/-! ## The adjoint action

`ad u` is the endomorphism `v ↦ [u, v]`. The Jacobi identity is exactly
the statement that `ad u` is a derivation of the bracket. -/

/-- The **adjoint endomorphism** `ad u : v ↦ [u, v]`, as a linear map. -/
def crossAdjoint (u : Vec3) : Vec3 →ₗ[ℝ] Vec3 where
  toFun v := ⁅u, v⁆
  map_add' v w := Brane.GA.cross_add_right u v w
  map_smul' t v := Brane.GA.cross_smul_right u t v

/-- The adjoint action is a **derivation** of the Lie bracket. -/
theorem crossAdjoint_leibniz (u v w : Vec3) :
    crossAdjoint u ⁅v, w⁆ = ⁅crossAdjoint u v, w⁆ + ⁅v, crossAdjoint u w⁆ :=
  bracket_leibniz u v w

/-- The adjoint action is a **Lie-algebra homomorphism**:
`ad [u, v] = [ad u, ad v]`, where the bracket on the right is the
commutator of linear endomorphisms. This is the Jacobi identity in
disguise. -/
theorem crossAdjoint_lie (u v : Vec3) :
    crossAdjoint ⁅u, v⁆ =
      crossAdjoint u * crossAdjoint v - crossAdjoint v * crossAdjoint u := by
  apply LinearMap.ext
  intro w
  change ⁅⁅u, v⁆, w⁆ = ⁅u, ⁅v, w⁆⁆ - ⁅v, ⁅u, w⁆⁆
  rw [bracket_leibniz]
  abel

/-- The Clifford commutator recovers the cross product:
`[embed u, embed v] = 2 (u × v) I`, where `I` is the pseudoscalar.
Since `I` is invertible, the commutator in `Cl(ℝ³)` and the Lie bracket
on `Vec3` carry the same information. -/
theorem embed_commutator (u v : Vec3) :
    Brane.GA.embed u * Brane.GA.embed v -
        Brane.GA.embed v * Brane.GA.embed u =
      2 * Brane.GA.embed (cross u v) * Brane.GA.I := by
  rw [Brane.GA.embed_mul_dual u v, Brane.GA.embed_mul_dual v u,
    cross_swap, Brane.GA.embed_neg, real_inner_comm v u]
  noncomm_ring

/-! ## The hat map and `so(3)`

The hat map sends `u = (u₀, u₁, u₂)` to the skew-symmetric matrix

`[[0, -u₂, u₁], [u₂, 0, -u₀], [-u₁, u₀, 0]]`,

which represents the linear map `v ↦ u × v`. Its image is exactly the
special orthogonal Lie algebra `so(3)`, and the map is an isomorphism of Lie
algebras. -/

/-- The **hat map**: the skew-symmetric matrix of the cross product by `u`. -/
def hatMatrix (u : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -u 2, u 1; u 2, 0, -u 0; -u 1, u 0, 0]

/-- The hat matrix represents the cross product: `hat u *ᵥ v = u × v`. -/
theorem hatMatrix_mulVec (u v : Vec3) :
    hatMatrix u *ᵥ v = cross u v := by
  ext i
  fin_cases i <;>
    simp [hatMatrix, cross_coordinates, vec3, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] <;>
    ring

/-- The hat matrix is skew-symmetric, i.e. it lies in `so(3)`. -/
theorem hatMatrix_mem_so (u : Vec3) :
    hatMatrix u ∈ LieAlgebra.Orthogonal.so (Fin 3) ℝ := by
  rw [LieAlgebra.Orthogonal.mem_so]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hatMatrix]

/-- The hat map turns the cross product into the matrix commutator:
`hat(u × v) = [hat u, hat v]`. -/
theorem hatMatrix_commutator (u v : Vec3) :
    hatMatrix ⁅u, v⁆ = hatMatrix u * hatMatrix v - hatMatrix v * hatMatrix u := by
  change hatMatrix (cross u v) = hatMatrix u * hatMatrix v - hatMatrix v * hatMatrix u
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hatMatrix, cross_coordinates, vec3] <;> ring

/-- The **Lie-algebra equivalence** `Vec3 ≃ so(3)`: the hat map, restricted
to skew-symmetric matrices. The bracket is preserved by
`hatMatrix_commutator`; the inverse extracts the three independent entries
`(A₂₁, A₀₂, A₁₀)` of a skew-symmetric matrix. -/
noncomputable def so3MatrixEquiv :
    Vec3 ≃ₗ⁅ℝ⁆ LieAlgebra.Orthogonal.so (Fin 3) ℝ := by
  sorry

/-! ## Mathlib's matrix Lie algebras

Mathlib already provides the matrix Lie algebras used above. These
restatements record the dictionary: the bracket on matrices is the
commutator, `sl n` is the trace-zero subalgebra, and `so n` is the
skew-symmetric one. -/

/-- The Lie bracket of square matrices is the commutator. -/
theorem matrix_bracket_eq_commutator (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    ⁅A, B⁆ = A * B - B * A :=
  rfl

/-- `so n` is the Lie algebra of skew-symmetric matrices. -/
theorem mem_so_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A ∈ LieAlgebra.Orthogonal.so (Fin 3) ℝ ↔ Aᵀ = -A :=
  LieAlgebra.Orthogonal.mem_so (Fin 3) ℝ A

/-- `sl n` is the Lie algebra of trace-zero matrices. -/
theorem mem_sl_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A ∈ LieAlgebra.SpecialLinear.sl (Fin 3) ℝ ↔ A.trace = 0 := by
  simp [LieAlgebra.SpecialLinear.sl]

/-- A **derivation** of an `ℝ`-algebra satisfies the Leibniz rule. This is
the algebraic model of "differentiate a product" used by the connection
Leibniz axioms in `Brane.Connections`. -/
theorem derivation_leibniz {A : Type*} [CommRing A] [Algebra ℝ A]
    (D : Derivation ℝ A A) (a b : A) :
    D (a * b) = a • D b + b • D a :=
  D.leibniz a b

end

end Lie
end Brane
