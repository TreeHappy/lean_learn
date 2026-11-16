import Brane.DifferentialGeometry
import Brane.GeometricAlgebra

/-!
# Geometric-algebra interpretation of the graph-surface geometry

This file restates the differential geometry of `Brane.DiffGeom` in the
language of geometric algebra, using the Clifford algebra `Brane.GA.GA3`
of `ℝ³`. The goal (for you, the prover) is to show that the GA objects and
the vector/matrix objects carry *the same information*: every `sorry` below
is a bridge between the two encodings.

The GA dictionary used here:

* the **geometric product** of vectors `u, v` is `embed u * embed v`;
* the **inner product** is its symmetric half, `dotGA u v`;
* the **wedge (exterior) product** is its antisymmetric half, `wedgeGA u v`;
* the wedge of two tangent vectors is a **bivector blade** spanning the
  tangent plane — its Hodge dual (`* I`) is exactly the vector normal
  `normal h p` of `DiffGeom`;
* the squared magnitude of a 2-blade is `-B * B` (since a 2-blade reverses
  under reversion), which must agree with `‖normal h p‖²`.

Nothing here is proved yet: each bridging theorem is stated and left as
`sorry` on purpose, so the vector-math and GA approaches can be shown to
coincide one lemma at a time. The two `sorry`s at the bottom of the chain
(`dotGA_eq`, `wedgeGA_dual`) already follow almost immediately from
`GA.embed_mul_add` and `GA.embed_mul_dual` — start there.

Namespace: `Brane.GADG`.
-/

namespace Brane

open Brane.DiffGeom
open scoped RealInnerProductSpace

noncomputable section

/-- The geometric algebra `Cl(ℝ³)` from `Brane.GA`. -/
abbrev GA3 := Brane.GA.GA3

/-- Embedding of vectors into the GA, aliased from `Brane.GA.embed`. -/
def embed (v : Vec3) : GA3 := Brane.GA.embed v

/-- The pseudoscalar, aliased from `Brane.GA.I`. -/
def I : GA3 := Brane.GA.I

namespace GADG

/-! ## The geometric product split into dot and wedge -/

/-- The inner product as the symmetric half of the geometric product,
living in `GA3` (it should turn out to be a plain scalar). -/
def dotGA (u v : Vec3) : GA3 := ((1:ℝ)/2) • (embed u * embed v + embed v * embed u)

/-- The wedge (exterior) product as the antisymmetric half of the geometric
product: a bivector. -/
def wedgeGA (u v : Vec3) : GA3 := ((1:ℝ)/2) • (embed u * embed v - embed v * embed u)

/-- Helper: symmetric and antisymmetric halves reassemble the product.
This is pure algebra and needs no input from `DiffGeom`. -/
theorem halves_recombine (A B : GA3) :
    ((1:ℝ)/2) • (A + B) + ((1:ℝ)/2) • (A - B) = A := by
  have h1 : A + B + (A - B) = A + A := by abel
  have h2 : (1:ℝ)/2 + (1:ℝ)/2 = 1 := by norm_num
  calc ((1:ℝ)/2) • (A + B) + ((1:ℝ)/2) • (A - B)
      = ((1:ℝ)/2) • (A + B + (A - B)) := by
        rw [← smul_add]
    _ = ((1:ℝ)/2) • (A + A) := by rw [h1]
    _ = ((1:ℝ)/2 + (1:ℝ)/2) • A := by rw [smul_add, ← add_smul]
    _ = (1:ℝ) • A := by rw [h2]
    _ = A := by rw [one_smul]

/-- The geometric product splits as dot + wedge. -/
theorem gprod_split (u v : Vec3) :
    embed u * embed v = dotGA u v + wedgeGA u v := by
  change embed u * embed v =
    ((1:ℝ)/2) • (embed u * embed v + embed v * embed u) +
    ((1:ℝ)/2) • (embed u * embed v - embed v * embed u)
  rw [halves_recombine (embed u * embed v) (embed v * embed u)]

@[simp]
theorem wedgeGA_self (u : Vec3) : wedgeGA u u = 0 := by
  rw [wedgeGA, sub_self, smul_zero]

/-- The wedge is antisymmetric. -/
theorem wedgeGA_anti (u v : Vec3) : wedgeGA v u = -(wedgeGA u v) := by
  simp only [wedgeGA, smul_sub]
  abel

/-- The dot is symmetric. -/
theorem dotGA_comm (u v : Vec3) : dotGA v u = dotGA u v := by
  simp only [dotGA]
  abel

/-- **Bridge 1.** The symmetric half of the geometric product is exactly the
scalar inner product, embedded. (Follows from `GA.embed_mul_add`.) -/
theorem dotGA_eq (u v : Vec3) : dotGA u v = algebraMap ℝ GA3 ⟪u, v⟫ := by sorry

/-- **Bridge 2.** The wedge of two vectors is the Hodge dual of their cross
product: `u ∧ v = (u × v) I`. (Follows from `GA.embed_mul_dual` together
with `dotGA_eq`.) -/
theorem wedgeGA_dual (u v : Vec3) :
    wedgeGA u v = embed (cross u v) * I := by sorry

/-- **Bridge 3 (the two products determine each other).** Conversely, the
inner product can be recovered from the wedge and the pseudoscalar:
`⟪u,v⟫ = ((u ∧ v) I⁻¹) ... ` — state and prove whatever recovery formula
you like here. -/
theorem dotGA_of_wedge (u v : Vec3) :
    algebraMap ℝ GA3 ⟪u, v⟫ = dotGA u v := by sorry

/-! ## The tangent plane as a bivector blade -/

/-- The tangent bivector (blade) of the graph surface at `p`: the wedge of
the two coordinate tangents. It spans the tangent plane. -/
def tangentBlade (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : GA3 :=
  wedgeGA (tangentX h p) (tangentY h p)

/-- **Bridge 4.** The tangent blade is the Hodge dual of the vector normal:
`∂ₓσ ∧ ∂ᵧσ = (∂ₓσ × ∂ᵧσ) I = normal · I`.
This is the key dictionary entry between the two encodings. -/
theorem tangentBlade_dual (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    tangentBlade h p = embed (normal h p) * I := by
  exact wedgeGA_dual _ _

/-- The squared magnitude of a 2-blade: a 2-blade is anti-reversion, so
`B · B` is (minus) its squared norm. -/
def bladeNormSq (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : GA3 :=
  -(tangentBlade h p * tangentBlade h p)

/-- **Bridge 5.** The blade magnitude agrees with the vector magnitude:
`-B² = ‖normal h p‖²` as scalars. Prove using `tangentBlade_dual`,
`embed_sq`-style computations, `GA.I_sq`, and `DiffGeom.norm_sq_normal`.
Hint: write `B = N I` with `N = embed (normal h p)`, then
`B² = N I N I = -N² I² = ⟪N,N⟫`. -/
theorem bladeNormSq_eq (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    bladeNormSq h p = algebraMap ℝ GA3 (‖normal h p‖ ^ 2) := by sorry

/-- A tangent combination wedged with the first tangent gives the coefficient
of the second: linearity of the wedge plus `wedgeGA_self`. -/
theorem wedgeGA_tangentCombination (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (a b : ℝ) :
    wedgeGA (tangentX h p) (a • tangentX h p + b • tangentY h p) =
      b • tangentBlade h p := by sorry

/-- **Bridge 6.** Tangent-plane membership detected by the wedge: a vector is
in the tangent space exactly when it is a combination of the tangents
(vector statement, `DiffGeom.mem_tangentSpace_iff`) — restate membership
purely in GA terms however you like, e.g. through
`wedgeGA_tangentCombination` and symmetry in both tangents. -/
theorem mem_tangentSpace_iff_wedge (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (v : Vec3) :
    v ∈ tangentSpace h p ↔
      ∃ a b : ℝ, a • tangentX h p + b • tangentY h p = v := by sorry

/-- The blade vanishes exactly when the tangents are parallel — for graph
surfaces this never happens, since the blade's dual `normal h p` is never
zero. -/
theorem tangentBlade_ne_zero (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    tangentBlade h p ≠ 0 := by sorry

/-- The `i`-th coordinate tangent: `tangentX` for `i = 0`, `tangentY` for
`i = 1` (same indexing as the columns of the Jacobian). -/
def tangentIth (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (i : Fin 2) : Vec3 :=
  match i with
  | 0 => tangentX h p
  | 1 => tangentY h p

/-- The `l`-th first partial of `h`: `partialX` for `l = 0`, `partialY`
for `l = 1`. -/
def firstPartial (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (l : Fin 2) : ℝ :=
  match l with
  | 0 => partialX h p.1 p.2
  | 1 => partialY h p.1 p.2

/-! ## Second derivatives in GA -/

/-- The `i j`-entry of the Hessian, as a vertical vector embedded in GA:
`∂ᵢ∂ⱼσ = Hess[i, j] · e₃` is purely vertical. -/
def secondEmbed (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (i j : Fin 2) : GA3 :=
  embed (vec3 0 0 (hessian h p i j))

/-- **Bridge 7.** The tangents are orthogonal to every second derivative:
in GA terms the product `embed (tangentX h p) * secondEmbed h p i j` has
zero scalar (dot) part. Prove from `DiffGeom.tangentX_inner_normal`-style
orthogonality (here: the dot of `tangentX` with a vertical vector is `0`)
and the split `gprod_split`. -/
theorem dotGA_tangent_second (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (i j : Fin 2) :
    dotGA (tangentX h p) (vec3 0 0 (hessian h p i j)) = 0 := by sorry

/-- **Bridge 8.** The bivector part of `∂ₖσ · ∂ᵢ∂ⱼσ` is the GA shape-operator
input: it equals `Hess[i, j] * (partialₖ h)` times the tangent blade.
This is exactly the quantity from which the Christoffel symbols / the
Gram-inverse in `Shooting.lean` are built. -/
theorem wedgeGA_second_tangent (h : ℝ → ℝ → ℝ) (p : ℝ × ℝ) (k i j : Fin 2) :
    wedgeGA (vec3 0 0 (hessian h p i j)) (tangentIth h p k) =
      (hessian h p i j * firstPartial h p k) •
        wedgeGA (vec3 0 0 1) (tangentIth h p k) := by
  sorry

end GADG

end

end Brane
