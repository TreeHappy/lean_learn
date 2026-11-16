import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic
import Brane.DifferentialGeometry

/-!
# Geometric algebra of ℝ³

The geometric algebra `Cl(ℝ³)` as Mathlib's `CliffordAlgebra` of the Euclidean
quadratic form `Q v = ⟪v, v⟫` on `Vec3`. Vectors embed via `embed` (`ι`); the
fundamental identity `uv + vu = 2⟪u,v⟫` holds, orthogonal vectors anticommute,
the pseudoscalar `I = e₀e₁e₂` squares to `-1`, and multiplication of two
vectors splits into the scalar inner product plus the Hodge dual of their
cross product (`embed_mul_dual`), tying this layer back to `Brane.DiffGeom`.

Namespace: `Brane.GA`.
-/

noncomputable section

namespace Brane.GA

open scoped RealInnerProductSpace
open Brane.DiffGeom

abbrev Vec3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The Euclidean quadratic form on `Vec3`: `Q v = ⟪v, v⟫`. -/
def quadVec : QuadraticForm ℝ Vec3 :=
  QuadraticMap.ofPolar (fun v => ⟪v, v⟫)
    (by
      intro a x
      simp only [real_inner_smul_left, real_inner_smul_right, smul_eq_mul]
      ring)
    (by
      intro x x' y
      simp only [QuadraticMap.polar, inner_add_left, inner_add_right]
      ring)
    (by
      intro a x y
      simp only [QuadraticMap.polar, real_inner_smul_left, real_inner_smul_right,
        inner_add_left, inner_add_right, smul_eq_mul]
      ring)

@[simp]
theorem quadVec_apply (v : Vec3) : quadVec v = ⟪v, v⟫ := rfl

/-- The geometric algebra of `ℝ³`: the Clifford algebra of the Euclidean
quadratic form. -/
abbrev GA3 := CliffordAlgebra quadVec

/-- The embedding of vectors into the geometric algebra. -/
def embed (v : Vec3) : GA3 := CliffordAlgebra.ι quadVec v

@[simp]
theorem embed_add (v w : Vec3) : embed (v + w) = embed v + embed w :=
  map_add _ v w

@[simp]
theorem embed_smul (r : ℝ) (v : Vec3) : embed (r • v) = r • embed v :=
  map_smul _ r v

/-- A vector squares to its norm squared: `v² = ⟪v,v⟫` (as a scalar). -/
theorem embed_sq (v : Vec3) : embed v * embed v = algebraMap ℝ GA3 ⟪v, v⟫ := by
  rw [embed, CliffordAlgebra.ι_sq_scalar, quadVec_apply]

/-- The standard orthonormal basis of `Vec3`. -/
def e0 : Vec3 := vec3 1 0 0
def e1 : Vec3 := vec3 0 1 0
def e2 : Vec3 := vec3 0 0 1

@[simp]
theorem e0_inner_self : ⟪e0, e0⟫ = 1 := by
  simp only [e0, vec3_inner]
  norm_num

@[simp]
theorem e1_inner_self : ⟪e1, e1⟫ = 1 := by
  simp only [e1, vec3_inner]
  norm_num

@[simp]
theorem e2_inner_self : ⟪e2, e2⟫ = 1 := by
  simp only [e2, vec3_inner]
  norm_num

theorem vec3_eq_smul (v : Vec3) : v = v 0 • e0 + v 1 • e1 + v 2 • e2 := by
  ext i
  fin_cases i <;> simp [e0, e1, e2, vec3]

/-- The fundamental identity of the geometric algebra:
`uv + vu = 2⟪u,v⟫` (scalars embedded via `algebraMap`). -/
theorem embed_mul_add (u v : Vec3) :
    embed u * embed v + embed v * embed u = algebraMap ℝ GA3 (2 * ⟪u, v⟫) := by
  -- the "defect" `D w := embed u * embed w + embed w * embed u - 2⟪u,w⟫` is
  -- additive and homogeneous in `w`; it vanishes on each basis vector
  -- (via `(u+e)² = ⟪u+e,u+e⟫`), hence everywhere.
  have hstep : ∀ e : Vec3, ⟪e, e⟫ = 1 →
      embed u * embed e + embed e * embed u
        - (algebraMap ℝ GA3 ⟪u, e⟫ + algebraMap ℝ GA3 ⟪u, e⟫) = 0 := by
    intro e he
    have h1 := embed_sq (u + e)
    rw [embed_add, mul_add, add_mul, add_mul, inner_add_left, inner_add_right,
      inner_add_right, real_inner_comm u e, he, embed_sq u, embed_sq e, he] at h1
    simp only [map_add, map_one] at h1
    have h2 := sub_eq_zero_of_eq h1
    abel_nf at h2 ⊢
    exact h2
  have hadd : ∀ w w' : Vec3,
      (embed u * embed (w + w') + embed (w + w') * embed u
        - (algebraMap ℝ GA3 ⟪u, w + w'⟫ + algebraMap ℝ GA3 ⟪u, w + w'⟫)) =
      (embed u * embed w + embed w * embed u
        - (algebraMap ℝ GA3 ⟪u, w⟫ + algebraMap ℝ GA3 ⟪u, w⟫)) +
        (embed u * embed w' + embed w' * embed u
        - (algebraMap ℝ GA3 ⟪u, w'⟫ + algebraMap ℝ GA3 ⟪u, w'⟫)) := by
    intro w w'
    simp only [embed_add, mul_add, add_mul, inner_add_right, map_add]
    abel
  have hsmul : ∀ (r : ℝ) w,
      (embed u * embed (r • w) + embed (r • w) * embed u
        - (algebraMap ℝ GA3 ⟪u, r • w⟫ + algebraMap ℝ GA3 ⟪u, r • w⟫)) =
      r • (embed u * embed w + embed w * embed u
        - (algebraMap ℝ GA3 ⟪u, w⟫ + algebraMap ℝ GA3 ⟪u, w⟫)) := by
    intro r w
    rw [embed_smul, real_inner_smul_right, map_mul, mul_smul_comm, smul_mul_assoc,
      ← Algebra.smul_def, smul_sub, smul_add, smul_add]
  have hzero : ∀ w : Vec3,
      embed u * embed w + embed w * embed u
        - (algebraMap ℝ GA3 ⟪u, w⟫ + algebraMap ℝ GA3 ⟪u, w⟫) = 0 := by
    intro w
    have hv : w = w 0 • e0 + w 1 • e1 + w 2 • e2 := vec3_eq_smul w
    rw [hv, hadd, hadd, hsmul, hsmul, hsmul]
    rw [hstep e0 e0_inner_self, hstep e1 e1_inner_self, hstep e2 e2_inner_self,
      smul_zero, smul_zero, smul_zero, add_zero, add_zero]
  rw [two_mul, map_add]
  exact eq_of_sub_eq_zero (hzero v)

/-! ### Anticommutation and the pseudoscalar -/

@[simp]
theorem e0_e1_inner : ⟪e0, e1⟫ = 0 := by
  simp only [e0, e1, vec3_inner]
  norm_num

@[simp]
theorem e0_e2_inner : ⟪e0, e2⟫ = 0 := by
  simp only [e0, e2, vec3_inner]
  norm_num

@[simp]
theorem e1_e2_inner : ⟪e1, e2⟫ = 0 := by
  simp only [e1, e2, vec3_inner]
  norm_num

/-- Orthogonal vectors anticommute: `vw = -uv`. -/
theorem embed_anti (u v : Vec3) (h : ⟪u, v⟫ = 0) :
    embed v * embed u = -(embed u * embed v) := by
  have h2 := embed_mul_add u v
  rw [h, mul_zero, map_zero] at h2
  have h3 : embed v * embed u + embed u * embed v = 0 := by
    rw [add_comm (embed v * embed u) (embed u * embed v)]
    exact h2
  exact add_eq_zero_iff_eq_neg.mp h3

theorem e1_mul_e0 : embed e1 * embed e0 = -(embed e0 * embed e1) :=
  embed_anti e0 e1 e0_e1_inner

theorem e2_mul_e0 : embed e2 * embed e0 = -(embed e0 * embed e2) :=
  embed_anti e0 e2 e0_e2_inner

theorem e2_mul_e1 : embed e2 * embed e1 = -(embed e1 * embed e2) :=
  embed_anti e1 e2 e1_e2_inner

/-- The unit pseudoscalar `I = e₀e₁e₂` (volume element). -/
def I : GA3 := embed e0 * embed e1 * embed e2

/-- Multiplying by `I` on the left is the Hodge dual on basis vectors. -/
theorem e0_mul_I : embed e0 * I = embed e1 * embed e2 := by
  simp only [I]
  rw [mul_assoc (embed e0) (embed e1) (embed e2),
    ← mul_assoc (embed e0) (embed e0) (embed e1 * embed e2), embed_sq e0,
    e0_inner_self, map_one, one_mul]

theorem e1_mul_I : embed e1 * I = -(embed e0 * embed e2) := by
  simp only [I]
  rw [← mul_assoc (embed e1) (embed e0 * embed e1) (embed e2),
    ← mul_assoc (embed e1) (embed e0) (embed e1), e1_mul_e0, neg_mul, neg_mul,
    mul_assoc (embed e0) (embed e1) (embed e1),
    mul_assoc (embed e0) (embed e1 * embed e1) (embed e2), embed_sq e1,
    e1_inner_self, map_one, one_mul]

theorem e2_mul_I : embed e2 * I = embed e0 * embed e1 := by
  simp only [I]
  rw [← mul_assoc (embed e2) (embed e0 * embed e1) (embed e2),
    ← mul_assoc (embed e2) (embed e0) (embed e1), e2_mul_e0, neg_mul, neg_mul,
    mul_assoc (embed e0) (embed e2) (embed e1), e2_mul_e1, mul_neg, neg_mul, neg_neg,
    mul_assoc (embed e0) (embed e1 * embed e2) (embed e2),
    mul_assoc (embed e1) (embed e2) (embed e2),
    embed_sq e2, e2_inner_self, map_one, mul_one]

/-- The pseudoscalar squares to `-1`. -/
theorem I_sq : I * I = -(algebraMap ℝ GA3 1) := by
  simp only [I]
  rw [mul_assoc (embed e0 * embed e1) (embed e2) (embed e0 * embed e1 * embed e2),
    ← mul_assoc (embed e2) (embed e0 * embed e1) (embed e2),
    ← mul_assoc (embed e2) (embed e0) (embed e1), e2_mul_e0, neg_mul, neg_mul,
    mul_assoc (embed e0) (embed e2) (embed e1), e2_mul_e1,
    mul_neg (embed e0) (embed e1 * embed e2),
    neg_mul (embed e0 * (embed e1 * embed e2)) (embed e2), neg_neg,
    mul_assoc (embed e0) (embed e1 * embed e2) (embed e2),
    mul_assoc (embed e1) (embed e2) (embed e2),
    embed_sq e2, e2_inner_self, map_one, mul_one,
    mul_assoc (embed e0) (embed e1) (embed e0 * embed e1),
    ← mul_assoc (embed e1) (embed e0) (embed e1), e1_mul_e0, neg_mul, mul_neg,
    mul_assoc (embed e0) (embed e1) (embed e1),
    ← mul_assoc (embed e0) (embed e0) (embed e1 * embed e1), embed_sq e0,
    e0_inner_self, embed_sq e1, e1_inner_self, map_one, mul_one]

/-! ### Linearity of the cross product -/

theorem cross_add_right (u v w : Vec3) : cross u (v + w) = cross u v + cross u w := by
  rw [cross_coordinates, cross_coordinates, cross_coordinates]
  ext i
  fin_cases i <;> simp [vec3, PiLp.toLp_apply] <;> ring

theorem cross_add_left (u u' v : Vec3) : cross (u + u') v = cross u v + cross u' v := by
  rw [cross_coordinates, cross_coordinates, cross_coordinates]
  ext i
  fin_cases i <;> simp [vec3, PiLp.toLp_apply] <;> ring

theorem cross_smul_right (u : Vec3) (r : ℝ) (v : Vec3) :
    cross u (r • v) = r • cross u v := by
  rw [cross_coordinates, cross_coordinates]
  ext i
  fin_cases i <;> simp [vec3, PiLp.toLp_apply, smul_eq_mul] <;> ring

theorem cross_smul_left (r : ℝ) (u v : Vec3) : cross (r • u) v = r • cross u v := by
  rw [cross_coordinates, cross_coordinates]
  ext i
  fin_cases i <;> simp [vec3, PiLp.toLp_apply, smul_eq_mul] <;> ring

theorem cross_self (u : Vec3) : cross u u = 0 := by
  rw [cross_coordinates]
  ext i
  fin_cases i <;> simp [vec3, PiLp.toLp_apply] <;> ring

/-! ### Cross products of basis vectors -/

theorem cross_e0_e1 : cross e0 e1 = e2 := by
  rw [cross_coordinates]
  ext i
  fin_cases i <;> simp [e0, e1, e2, vec3, PiLp.toLp_apply]

theorem cross_e1_e2 : cross e1 e2 = e0 := by
  rw [cross_coordinates]
  ext i
  fin_cases i <;> simp [e0, e1, e2, vec3, PiLp.toLp_apply]

theorem cross_e2_e0 : cross e2 e0 = e1 := by
  rw [cross_coordinates]
  ext i
  fin_cases i <;> simp [e0, e1, e2, vec3, PiLp.toLp_apply]

/-! ### The blade product / Hodge dual -/

@[simp]
theorem embed_neg (v : Vec3) : embed (-v) = -(embed v) := map_neg _ v

@[simp]
theorem embed_zero : embed (0 : Vec3) = 0 := map_zero _

/-- The blade product in `ℝ³`: multiplying two vectors gives their inner
product plus the Hodge dual of their cross product:
`uv = ⟪u,v⟫ + (u × v) · I` where `I = e₀e₁e₂` is the pseudoscalar. -/
theorem embed_mul_dual (u v : Vec3) :
    embed u * embed v = algebraMap ℝ GA3 ⟪u, v⟫ + embed (cross u v) * I := by
  have key : ∀ a b : Vec3,
      embed a * embed b
        - (algebraMap ℝ GA3 ⟪a, b⟫ + embed (cross a b) * I) = 0 := by
    intro a b
    -- additivity and homogeneity in the first argument
    have haddu : ∀ a a' b : Vec3,
        (embed (a + a') * embed b
          - (algebraMap ℝ GA3 ⟪a + a', b⟫ + embed (cross (a + a') b) * I)) =
        (embed a * embed b
          - (algebraMap ℝ GA3 ⟪a, b⟫ + embed (cross a b) * I)) +
          (embed a' * embed b
          - (algebraMap ℝ GA3 ⟪a', b⟫ + embed (cross a' b) * I)) := by
      intro a a' b
      simp only [embed_add, add_mul, inner_add_left, map_add,
        cross_add_left, embed_add, add_mul]
      abel
    have hsmulu : ∀ (r : ℝ) (a b : Vec3),
        (embed (r • a) * embed b
          - (algebraMap ℝ GA3 ⟪r • a, b⟫ + embed (cross (r • a) b) * I)) =
        r • (embed a * embed b
          - (algebraMap ℝ GA3 ⟪a, b⟫ + embed (cross a b) * I)) := by
      intro r a b
      rw [embed_smul, real_inner_smul_left, map_mul, ← Algebra.smul_def,
        smul_mul_assoc, cross_smul_left, embed_smul, smul_mul_assoc, smul_sub,
        smul_add]
    -- additivity and homogeneity in the second argument
    have haddv : ∀ a b b' : Vec3,
        (embed a * embed (b + b')
          - (algebraMap ℝ GA3 ⟪a, b + b'⟫ + embed (cross a (b + b')) * I)) =
        (embed a * embed b
          - (algebraMap ℝ GA3 ⟪a, b⟫ + embed (cross a b) * I)) +
          (embed a * embed b'
          - (algebraMap ℝ GA3 ⟪a, b'⟫ + embed (cross a b') * I)) := by
      intro a b b'
      simp only [embed_add, mul_add, add_mul, inner_add_right, map_add,
        cross_add_right, embed_add, add_mul]
      abel
    have hsmulv : ∀ (r : ℝ) (a b : Vec3),
        (embed a * embed (r • b)
          - (algebraMap ℝ GA3 ⟪a, r • b⟫ + embed (cross a (r • b)) * I)) =
        r • (embed a * embed b
          - (algebraMap ℝ GA3 ⟪a, b⟫ + embed (cross a b) * I)) := by
      intro r a b
      rw [embed_smul, real_inner_smul_right, map_mul, ← Algebra.smul_def,
        mul_smul_comm, cross_smul_right, embed_smul, smul_mul_assoc, smul_sub,
        smul_add]
    -- the defect vanishes on all nine basis pairs
    have h00 : embed e0 * embed e0
        - (algebraMap ℝ GA3 ⟪e0, e0⟫ + embed (cross e0 e0) * I) = 0 := by
      rw [cross_self, embed_zero, zero_mul, add_zero, embed_sq e0, sub_self]
    have h11 : embed e1 * embed e1
        - (algebraMap ℝ GA3 ⟪e1, e1⟫ + embed (cross e1 e1) * I) = 0 := by
      rw [cross_self, embed_zero, zero_mul, add_zero, embed_sq e1, sub_self]
    have h22 : embed e2 * embed e2
        - (algebraMap ℝ GA3 ⟪e2, e2⟫ + embed (cross e2 e2) * I) = 0 := by
      rw [cross_self, embed_zero, zero_mul, add_zero, embed_sq e2, sub_self]
    have h01 : embed e0 * embed e1
        - (algebraMap ℝ GA3 ⟪e0, e1⟫ + embed (cross e0 e1) * I) = 0 := by
      rw [cross_e0_e1, e2_mul_I, e0_e1_inner, map_zero, zero_add, sub_self]
    have h10 : embed e1 * embed e0
        - (algebraMap ℝ GA3 ⟪e1, e0⟫ + embed (cross e1 e0) * I) = 0 := by
      rw [e1_mul_e0, cross_swap, cross_e0_e1, embed_neg, neg_mul, e2_mul_I,
        real_inner_comm, e0_e1_inner, map_zero, zero_add, sub_self]
    have h02 : embed e0 * embed e2
        - (algebraMap ℝ GA3 ⟪e0, e2⟫ + embed (cross e0 e2) * I) = 0 := by
      rw [cross_swap, cross_e2_e0, embed_neg, neg_mul, e1_mul_I, neg_neg,
        e0_e2_inner, map_zero, zero_add, sub_self]
    have h20 : embed e2 * embed e0
        - (algebraMap ℝ GA3 ⟪e2, e0⟫ + embed (cross e2 e0) * I) = 0 := by
      rw [e2_mul_e0, cross_e2_e0, e1_mul_I, real_inner_comm, e0_e2_inner,
        map_zero, zero_add, sub_self]
    have h12 : embed e1 * embed e2
        - (algebraMap ℝ GA3 ⟪e1, e2⟫ + embed (cross e1 e2) * I) = 0 := by
      rw [cross_e1_e2, e0_mul_I, e1_e2_inner, map_zero, zero_add, sub_self]
    have h21 : embed e2 * embed e1
        - (algebraMap ℝ GA3 ⟪e2, e1⟫ + embed (cross e2 e1) * I) = 0 := by
      rw [e2_mul_e1, cross_swap, cross_e1_e2, embed_neg, neg_mul, e0_mul_I,
        real_inner_comm, e1_e2_inner, map_zero, zero_add, sub_self]
    -- expand both arguments in the basis
    have hvb : b = b 0 • e0 + b 1 • e1 + b 2 • e2 := vec3_eq_smul b
    have hua : a = a 0 • e0 + a 1 • e1 + a 2 • e2 := vec3_eq_smul a
    rw [hvb, haddv, haddv, hsmulv, hsmulv, hsmulv]
    rw [hua, haddu, haddu, haddu, haddu, haddu, haddu,
      hsmulu, hsmulu, hsmulu, hsmulu, hsmulu, hsmulu, hsmulu, hsmulu, hsmulu]
    rw [h00, h01, h02, h10, h11, h12, h20, h21, h22]
    simp only [smul_zero, add_zero]
  exact eq_of_sub_eq_zero (key u v)

end Brane.GA
