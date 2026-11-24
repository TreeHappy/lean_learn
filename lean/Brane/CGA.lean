import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Conformal geometric algebra (`Brane.CGA`)

This file ports the conformal geometric-algebra classes of the
[Terathon Math Library](https://github.com/EricLengyel/Terathon-Math-Library)
to Lean, using Mathlib's `CliffordAlgebra` as the underlying engine.

The two vector models are

* `D2` — four-dimensional `Cl(2,0,2)` for the plane, with Euclidean basis
  `e₁, e₂` and two null directions `e₃, e₄` satisfying `e₃² = e₄² = 0` and
  `e₃ e₄ + e₄ e₃ = -2` (so `e₃ · e₄ = -1`).
* `D3` — five-dimensional `Cl(3,0,2)` for space, with Euclidean basis
  `e₁, e₂, e₃` and null directions `e₄, e₅`, again with `e₄ · e₅ = -1`.

Terathon calls these models "conformal geometric algebra" and uses the
component names on `e₄` (weight) and `e₅` (the squared-distance coordinate).  The quadratic form is written with the cross term
`- 2 w u` precisely so that the round point

`x e₁ + y e₂ + z e₃ + w e₄ + u e₅`, with `w = 1` and
`u = (x² + y² + z²) / 2`,

is null, as in the standard conformal model.  The coefficient vectors and the
named blades match the Terathon README, so `roundPoint3` and the other
constructors are direct translations of the C++ constructors.

The named classes are type synonyms for the Clifford algebra; the
`RoundPoint2D/3D`, `Dipole2D/3D`, `Circle2D/3D`, and `Sphere3D` constructors
give the concrete blades.  The sandwich action is the same one used in
`Brane.PGA`: `transform Q p = Q p Q̰`.

Namespace: `Brane.CGA`.
-/

noncomputable section

namespace Brane
namespace CGA

/-! ## The two-dimensional conformal model -/

namespace D2

/-- Coefficient vectors for the 2D conformal model. -/
abbrev V : Type := Fin 4 → ℝ

/-- The conformal quadratic form `x² + y² - 2 z w`. -/
def quad : QuadraticForm ℝ V :=
  QuadraticMap.ofPolar (fun v => v 0 * v 0 + v 1 * v 1 - 2 * v 2 * v 3)
    (by
      intro a x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)
    (by
      intro x x' y
      simp only [QuadraticMap.polar, Pi.add_apply]
      ring_nf)
    (by
      intro a x y
      simp only [QuadraticMap.polar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring_nf)

@[simp]
theorem quad_apply (v : V) : quad v = v 0 * v 0 + v 1 * v 1 - 2 * v 2 * v 3 := rfl

/-- The 2D conformal geometric algebra. -/
abbrev GA : Type := CliffordAlgebra quad

/-- Embed a coefficient vector. -/
def iota (v : V) : GA := CliffordAlgebra.ι quad v

/-- The `i`-th basis vector. -/
def e (i : Fin 4) : GA := iota (Pi.single i 1)

/-- `e₁`. -/
def e1 : GA := e 0
/-- `e₂`. -/
def e2 : GA := e 1
/-- `e₃`, the null weight direction. -/
def e3 : GA := e 2
/-- `e₄`, the null squared-distance direction. -/
def e4 : GA := e 3

@[simp]
theorem e1_sq : e1 * e1 = 1 := by
  rw [e1, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

@[simp]
theorem e2_sq : e2 * e2 = 1 := by
  rw [e2, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

/-- The weight direction is null. -/
@[simp]
theorem e3_sq : e3 * e3 = 0 := by
  rw [e3, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

/-- The squared-distance direction is null. -/
@[simp]
theorem e4_sq : e4 * e4 = 0 := by
  rw [e4, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

/-- The two null directions have inner product `-1`. -/
theorem e3_mul_e4_add :
    e3 * e4 + e4 * e3 = -(2 : GA) := by
  rw [e3, e4, e, e, iota, iota, CliffordAlgebra.ι_mul_ι_add_swap]
  simp [QuadraticMap.polar, quad_apply, Pi.single]
  rfl

/-- Bivector `e₂₃`. -/
def e23 : GA := e2 * e3
/-- Bivector `e₃₁`. -/
def e31 : GA := e3 * e1
/-- Bivector `e₁₂`. -/
def e12 : GA := e1 * e2
/-- Bivector `e₄₁`. -/
def e41 : GA := e4 * e1
/-- Bivector `e₄₂`. -/
def e42 : GA := e4 * e2
/-- Bivector `e₄₃`. -/
def e43 : GA := e4 * e3

/-- Trivector `e₃₂₁`. -/
def e321 : GA := e3 * e2 * e1
/-- Trivector `e₄₂₃`. -/
def e423 : GA := e4 * e2 * e3
/-- Trivector `e₄₃₁`. -/
def e431 : GA := e4 * e3 * e1
/-- Trivector `e₄₁₂`. -/
def e412 : GA := e4 * e1 * e2

end D2

/-! ## The three-dimensional conformal model -/

namespace D3

/-- Coefficient vectors for the 3D conformal model. -/
abbrev V : Type := Fin 5 → ℝ

/-- The conformal quadratic form `x² + y² + z² - 2 w u`. -/
def quad : QuadraticForm ℝ V :=
  QuadraticMap.ofPolar (fun v => v 0 * v 0 + v 1 * v 1 + v 2 * v 2 - 2 * v 3 * v 4)
    (by
      intro a x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring)
    (by
      intro x x' y
      simp only [QuadraticMap.polar, Pi.add_apply]
      ring_nf)
    (by
      intro a x y
      simp only [QuadraticMap.polar, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring_nf)

@[simp]
theorem quad_apply (v : V) :
    quad v = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 - 2 * v 3 * v 4 := rfl

/-- The 3D conformal geometric algebra. -/
abbrev GA : Type := CliffordAlgebra quad

/-- Embed a coefficient vector. -/
def iota (v : V) : GA := CliffordAlgebra.ι quad v

/-- The `i`-th basis vector. -/
def e (i : Fin 5) : GA := iota (Pi.single i 1)

/-- `e₁`. -/
def e1 : GA := e 0
/-- `e₂`. -/
def e2 : GA := e 1
/-- `e₃`. -/
def e3 : GA := e 2
/-- `e₄`, the null weight direction. -/
def e4 : GA := e 3
/-- `e₅`, the null squared-distance direction. -/
def e5 : GA := e 4

@[simp]
theorem e1_sq : e1 * e1 = 1 := by
  rw [e1, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

@[simp]
theorem e2_sq : e2 * e2 = 1 := by
  rw [e2, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

@[simp]
theorem e3_sq : e3 * e3 = 1 := by
  rw [e3, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

/-- The weight direction is null. -/
@[simp]
theorem e4_sq : e4 * e4 = 0 := by
  rw [e4, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

/-- The squared-distance direction is null. -/
@[simp]
theorem e5_sq : e5 * e5 = 0 := by
  rw [e5, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

/-- The two null directions have inner product `-1`. -/
theorem e4_mul_e5_add :
    e4 * e5 + e5 * e4 = -(2 : GA) := by
  rw [e4, e5, e, e, iota, iota, CliffordAlgebra.ι_mul_ι_add_swap]
  simp [QuadraticMap.polar, quad_apply, Pi.single]
  rfl

/-- Bivector `e₄₁`. -/
def e41 : GA := e4 * e1
/-- Bivector `e₄₂`. -/
def e42 : GA := e4 * e2
/-- Bivector `e₄₃`. -/
def e43 : GA := e4 * e3
/-- Bivector `e₂₃`. -/
def e23 : GA := e2 * e3
/-- Bivector `e₃₁`. -/
def e31 : GA := e3 * e1
/-- Bivector `e₁₂`. -/
def e12 : GA := e1 * e2
/-- Bivector `e₁₅`. -/
def e15 : GA := e1 * e5
/-- Bivector `e₂₅`. -/
def e25 : GA := e2 * e5
/-- Bivector `e₃₅`. -/
def e35 : GA := e3 * e5
/-- Bivector `e₄₅`. -/
def e45 : GA := e4 * e5

/-- Trivector `e₄₂₃`. -/
def e423 : GA := e4 * e2 * e3
/-- Trivector `e₄₃₁`. -/
def e431 : GA := e4 * e3 * e1
/-- Trivector `e₄₁₂`. -/
def e412 : GA := e4 * e1 * e2
/-- Trivector `e₃₂₁`. -/
def e321 : GA := e3 * e2 * e1
/-- Trivector `e₄₁₅`. -/
def e415 : GA := e4 * e1 * e5
/-- Trivector `e₄₂₅`. -/
def e425 : GA := e4 * e2 * e5
/-- Trivector `e₄₃₅`. -/
def e435 : GA := e4 * e3 * e5
/-- Trivector `e₂₃₅`. -/
def e235 : GA := e2 * e3 * e5
/-- Trivector `e₃₁₅`. -/
def e315 : GA := e3 * e1 * e5
/-- Trivector `e₁₂₅`. -/
def e125 : GA := e1 * e2 * e5

/-- Quadrivector `e₁₂₃₄`. -/
def e1234 : GA := e1 * e2 * e3 * e4
/-- Quadrivector `e₄₂₃₅`. -/
def e4235 : GA := e4 * e2 * e3 * e5
/-- Quadrivector `e₄₃₁₅`. -/
def e4315 : GA := e4 * e3 * e1 * e5
/-- Quadrivector `e₄₁₂₅`. -/
def e4125 : GA := e4 * e1 * e2 * e5
/-- Quadrivector `e₃₂₁₅`. -/
def e3215 : GA := e3 * e2 * e1 * e5

end D3

/-! ## The named classes -/

/-- The underlying 2D conformal geometric algebra. -/
abbrev CGA2 : Type := D2.GA
/-- The underlying 3D conformal geometric algebra. -/
abbrev CGA3 : Type := D3.GA

/-- A 2D round point `x e₁ + y e₂ + z e₃ + w e₄`. -/
abbrev RoundPoint2D : Type := D2.GA
/-- A 2D dipole (flat line + flat point). -/
abbrev Dipole2D : Type := D2.GA
/-- A 2D circle (a trivector in the conformal model). -/
abbrev Circle2D : Type := D2.GA

/-- A 3D round point `x e₁ + y e₂ + z e₃ + w e₄ + u e₅`. -/
abbrev RoundPoint3D : Type := D3.GA
/-- A 3D dipole, a bivector. -/
abbrev Dipole3D : Type := D3.GA
/-- A 3D circle, a trivector. -/
abbrev Circle3D : Type := D3.GA
/-- A 3D sphere, a quadrivector. -/
abbrev Sphere3D : Type := D3.GA

/-! ### Constructors and null-point lemmas -/

/-- The coefficient vector of a 2D round point:
`x e₁ + y e₂ + e₃ + (x² + y²)/2 e₄`. -/
def roundPoint2Vec (x y : ℝ) : D2.V :=
  ![x, y, 1, (x * x + y * y) / 2]

@[simp]
theorem roundPoint2Vec_0 (x y : ℝ) : roundPoint2Vec x y 0 = x := rfl
@[simp]
theorem roundPoint2Vec_1 (x y : ℝ) : roundPoint2Vec x y 1 = y := rfl
@[simp]
theorem roundPoint2Vec_2 (x y : ℝ) : roundPoint2Vec x y 2 = 1 := rfl
@[simp]
theorem roundPoint2Vec_3 (x y : ℝ) :
    roundPoint2Vec x y 3 = (x * x + y * y) / 2 := rfl

/-- A 2D round point. -/
def roundPoint2 (x y : ℝ) : RoundPoint2D := D2.iota (roundPoint2Vec x y)

theorem quad_roundPoint2Vec (x y : ℝ) : D2.quad (roundPoint2Vec x y) = 0 := by
  rw [D2.quad_apply]
  simp only [roundPoint2Vec_0, roundPoint2Vec_1, roundPoint2Vec_2,
    roundPoint2Vec_3]
  ring

/-- Round points are null vectors: `p² = 0`. -/
theorem roundPoint2_sq (x y : ℝ) :
    roundPoint2 x y * roundPoint2 x y = 0 := by
  rw [roundPoint2, D2.iota, CliffordAlgebra.ι_sq_scalar,
    quad_roundPoint2Vec, map_zero]

/-- A 2D dipole with Terathon's six components. -/
def dipole2 (gx gy gz px py pz : ℝ) : Dipole2D :=
  gx • D2.e23 + gy • D2.e31 + gz • D2.e12 +
    px • D2.e41 + py • D2.e42 + pz • D2.e43

/-- A 2D circle `w e₃₂₁ + x e₄₂₃ + y e₄₃₁ + z e₄₁₂`. -/
def circle2 (w x y z : ℝ) : Circle2D :=
  w • D2.e321 + x • D2.e423 + y • D2.e431 + z • D2.e412

/-- The coefficient vector of a 3D round point:
`x e₁ + y e₂ + z e₃ + e₄ + (x² + y² + z²)/2 e₅`. -/
def roundPoint3Vec (x y z : ℝ) : D3.V :=
  ![x, y, z, 1, (x * x + y * y + z * z) / 2]

@[simp]
theorem roundPoint3Vec_0 (x y z : ℝ) : roundPoint3Vec x y z 0 = x := rfl
@[simp]
theorem roundPoint3Vec_1 (x y z : ℝ) : roundPoint3Vec x y z 1 = y := rfl
@[simp]
theorem roundPoint3Vec_2 (x y z : ℝ) : roundPoint3Vec x y z 2 = z := rfl
@[simp]
theorem roundPoint3Vec_3 (x y z : ℝ) : roundPoint3Vec x y z 3 = 1 := rfl
@[simp]
theorem roundPoint3Vec_4 (x y z : ℝ) :
    roundPoint3Vec x y z 4 = (x * x + y * y + z * z) / 2 := rfl

/-- A 3D round point. -/
def roundPoint3 (x y z : ℝ) : RoundPoint3D := D3.iota (roundPoint3Vec x y z)

theorem quad_roundPoint3Vec (x y z : ℝ) : D3.quad (roundPoint3Vec x y z) = 0 := by
  rw [D3.quad_apply]
  simp only [roundPoint3Vec_0, roundPoint3Vec_1, roundPoint3Vec_2,
    roundPoint3Vec_3, roundPoint3Vec_4]
  ring

/-- Round points are null vectors: `p² = 0`. -/
theorem roundPoint3_sq (x y z : ℝ) :
    roundPoint3 x y z * roundPoint3 x y z = 0 := by
  rw [roundPoint3, D3.iota, CliffordAlgebra.ι_sq_scalar,
    quad_roundPoint3Vec, map_zero]

/-- A 3D dipole with Terathon's ten components. -/
def dipole3 (vx vy vz mx my mz px py pz pw : ℝ) : Dipole3D :=
  vx • D3.e41 + vy • D3.e42 + vz • D3.e43 +
    mx • D3.e23 + my • D3.e31 + mz • D3.e12 +
    px • D3.e15 + py • D3.e25 + pz • D3.e35 + pw • D3.e45

/-- A 3D circle with Terathon's ten components. -/
def circle3 (gx gy gz gw vx vy vz mx my mz : ℝ) : Circle3D :=
  gx • D3.e423 + gy • D3.e431 + gz • D3.e412 + gw • D3.e321 +
    vx • D3.e415 + vy • D3.e425 + vz • D3.e435 +
    mx • D3.e235 + my • D3.e315 + mz • D3.e125

/-- A 3D sphere `u e₁₂₃₄ + x e₄₂₃₅ + y e₄₃₁₅ + z e₄₁₂₅ + w e₃₂₁₅`. -/
def sphere3 (u x y z w : ℝ) : Sphere3D :=
  u • D3.e1234 + x • D3.e4235 + y • D3.e4315 +
    z • D3.e4125 + w • D3.e3215

/-! ## Reversion and the sandwich action -/

/-- Grade reversion, inherited from the Clifford algebra. -/
def reverse {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (x : CliffordAlgebra Q) : CliffordAlgebra Q :=
  CliffordAlgebra.reverse x

/-- The grade involution, inherited from the Clifford algebra. -/
def involute {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (x : CliffordAlgebra Q) : CliffordAlgebra Q :=
  CliffordAlgebra.involute x

/-- Clifford conjugation: reversion composed with the grade involution. -/
def conjugate {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (x : CliffordAlgebra Q) : CliffordAlgebra Q :=
  involute (CliffordAlgebra.reverse x)

/-- The sandwich action `Q p Q̰`. -/
def sandwich {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (q p : CliffordAlgebra Q) : CliffordAlgebra Q :=
  q * p * CliffordAlgebra.reverse q

@[simp]
theorem reverse_reverse {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (x : CliffordAlgebra Q) :
    reverse (reverse x) = x :=
  CliffordAlgebra.reverse_reverse x

/-- The identity transformation acts trivially. -/
@[simp]
theorem sandwich_one {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (p : CliffordAlgebra Q) : sandwich 1 p = p := by
  simp [sandwich]

/-- Composition of transformations. -/
theorem sandwich_mul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (q r p : CliffordAlgebra Q) :
    sandwich q (sandwich r p) = sandwich (q * r) p := by
  simp [sandwich, mul_assoc]

/-- Transform a 2D round point by a conformal versor. -/
def transform2 (p : RoundPoint2D) (Q : RoundPoint2D) : RoundPoint2D :=
  sandwich Q p

/-- Transform a 3D round point by a conformal versor. -/
def transform3 (p : RoundPoint3D) (Q : RoundPoint3D) : RoundPoint3D :=
  sandwich Q p

end CGA
end Brane
