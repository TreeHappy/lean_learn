import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Projective / rigid geometric algebra (`Brane.PGA`)

This file ports the rigid (projective) geometric-algebra classes of the
[Terathon Math Library](https://github.com/EricLengyel/Terathon-Math-Library)
to Lean.  The C++ library stores one concrete coefficient vector per class;
here the underlying object is Mathlib's `CliffordAlgebra`, so the geometric
product, reversion, and the sandwich action are inherited instead of being
reimplemented.

The two algebras are

* `D2` — `Cl(2,0,1)` for the plane.  Basis `e₁, e₂` are Euclidean and `e₃` is
  the null homogeneous direction (`e₃² = 0`).
* `D3` — `Cl(3,0,1)` for space.  Basis `e₁, e₂, e₃` are Euclidean and `e₄`
  is the null homogeneous direction (`e₄² = 0`).

The named classes (`FlatPoint3D`, `Line3D`, `Plane3D`, `Motor3D`,
`Flector3D`, and the 2D analogues) are type synonyms for the corresponding
Clifford algebra.  Their constructors below use exactly the basis blades
listed in Terathon's README, so a coefficient vector can be copied over
verbatim.  Grade is a property of a constructed value rather than a separate
Lean type; this keeps the algebra operations total and makes the sandwich
product available on every element.

The action used by motors and flectors is

`transform Q p = Q * p * reverse Q`,

which is Terathon's `Transform(p, Q) = Q ⟇ p ⟇ Q̰` for the component
conventions in the two libraries.

Namespace: `Brane.PGA`.
-/

noncomputable section

namespace Brane
namespace PGA

/-! ## The two-dimensional algebra `Cl(2,0,1)` -/

namespace D2

/-- Coefficient vectors for the 2D algebra. -/
abbrev V : Type := Fin 3 → ℝ

/-- The degenerate quadratic form of `Cl(2,0,1)`: `x² + y²`; the third
coordinate is the null homogeneous direction. -/
def quad : QuadraticForm ℝ V :=
  QuadraticMap.ofPolar (fun v => v 0 * v 0 + v 1 * v 1)
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
theorem quad_apply (v : V) : quad v = v 0 * v 0 + v 1 * v 1 := rfl

/-- The 2D rigid geometric algebra. -/
abbrev GA : Type := CliffordAlgebra quad

/-- Embed a coefficient vector. -/
def iota (v : V) : GA := CliffordAlgebra.ι quad v

/-- The `i`-th basis vector. -/
def e (i : Fin 3) : GA := iota (Pi.single i 1)

/-- `e₁`, the first Euclidean basis vector. -/
def e1 : GA := e 0
/-- `e₂`, the second Euclidean basis vector. -/
def e2 : GA := e 1
/-- `e₃`, the null homogeneous basis vector. -/
def e3 : GA := e 2

@[simp]
theorem e1_sq : e1 * e1 = 1 := by
  rw [e1, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

@[simp]
theorem e2_sq : e2 * e2 = 1 := by
  rw [e2, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

/-- The homogeneous direction is null. -/
@[simp]
theorem e3_sq : e3 * e3 = 0 := by
  rw [e3, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

/-- Bivector basis blade `e₂₃`. -/
def e23 : GA := e2 * e3
/-- Bivector basis blade `e₃₁`. -/
def e31 : GA := e3 * e1
/-- Bivector basis blade `e₁₂`. -/
def e12 : GA := e1 * e2

end D2

/-! ## The three-dimensional algebra `Cl(3,0,1)` -/

namespace D3

/-- Coefficient vectors for the 3D algebra. -/
abbrev V : Type := Fin 4 → ℝ

/-- The degenerate quadratic form of `Cl(3,0,1)`: `x² + y² + z²`; the fourth
coordinate is the null homogeneous direction. -/
def quad : QuadraticForm ℝ V :=
  QuadraticMap.ofPolar (fun v => v 0 * v 0 + v 1 * v 1 + v 2 * v 2)
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
theorem quad_apply (v : V) : quad v = v 0 * v 0 + v 1 * v 1 + v 2 * v 2 := rfl

/-- The 3D rigid geometric algebra. -/
abbrev GA : Type := CliffordAlgebra quad

/-- Embed a coefficient vector. -/
def iota (v : V) : GA := CliffordAlgebra.ι quad v

/-- The `i`-th basis vector. -/
def e (i : Fin 4) : GA := iota (Pi.single i 1)

/-- `e₁`. -/
def e1 : GA := e 0
/-- `e₂`. -/
def e2 : GA := e 1
/-- `e₃`. -/
def e3 : GA := e 2
/-- `e₄`, the null homogeneous basis vector. -/
def e4 : GA := e 3

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

/-- The homogeneous direction is null. -/
@[simp]
theorem e4_sq : e4 * e4 = 0 := by
  rw [e4, e, iota, CliffordAlgebra.ι_sq_scalar, quad_apply]
  simp [Pi.single]

/-- Bivector basis blade `e₄₁`. -/
def e41 : GA := e4 * e1
/-- Bivector basis blade `e₄₂`. -/
def e42 : GA := e4 * e2
/-- Bivector basis blade `e₄₃`. -/
def e43 : GA := e4 * e3
/-- Bivector basis blade `e₂₃`. -/
def e23 : GA := e2 * e3
/-- Bivector basis blade `e₃₁`. -/
def e31 : GA := e3 * e1
/-- Bivector basis blade `e₁₂`. -/
def e12 : GA := e1 * e2

/-- Trivector basis blade `e₂₃₄`. -/
def e234 : GA := e2 * e3 * e4
/-- Trivector basis blade `e₃₁₄`. -/
def e314 : GA := e3 * e1 * e4
/-- Trivector basis blade `e₁₂₄`. -/
def e124 : GA := e1 * e2 * e4
/-- Trivector basis blade `e₃₂₁`. -/
def e321 : GA := e3 * e2 * e1

/-- The pseudoscalar `e₁₂₃₄` (the antiscalar coordinate of a motor). -/
def e1234 : GA := e1 * e2 * e3 * e4

end D3

/-! ## The named classes -/

/-- The underlying 2D rigid geometric algebra `Cl(2,0,1)`. -/
abbrev PGA2 : Type := D2.GA
/-- The underlying 3D rigid geometric algebra `Cl(3,0,1)`. -/
abbrev PGA3 : Type := D3.GA

/-- A 2D flat point `x e₁ + y e₂ + z e₃`. -/
abbrev FlatPoint2D : Type := D2.GA
/-- A 2D line, a bivector of `Cl(2,0,1)`. -/
abbrev Line2D : Type := D2.GA
/-- A 2D motor (even/odd mixed component representation of Terathon). -/
abbrev Motor2D : Type := D2.GA
/-- A 2D flector (reflection operator). -/
abbrev Flector2D : Type := D2.GA

/-- A 3D flat point `x e₁ + y e₂ + z e₃ + w e₄`. -/
abbrev FlatPoint3D : Type := D3.GA
/-- A 3D line, a bivector with direction and moment. -/
abbrev Line3D : Type := D3.GA
/-- A 3D plane, a trivector. -/
abbrev Plane3D : Type := D3.GA
/-- A 3D motor (dual-quaternion-like motion operator). -/
abbrev Motor3D : Type := D3.GA
/-- A 3D flector (point + plane reflection operator). -/
abbrev Flector3D : Type := D3.GA

/-! ### Constructors -/

/-- A 2D Euclidean point, homogenized as `x e₁ + y e₂ + e₃`. -/
def flatPoint2 (x y : ℝ) : FlatPoint2D :=
  x • D2.e1 + y • D2.e2 + D2.e3

/-- A general 2D flat point with homogeneous weight. -/
def flatPoint2WithWeight (x y z : ℝ) : FlatPoint2D :=
  x • D2.e1 + y • D2.e2 + z • D2.e3

/-- The origin of the 2D affine plane. -/
def origin2 : FlatPoint2D := D2.e3

/-- A 2D line `x e₂₃ + y e₃₁ + z e₁₂`. -/
def line2 (x y z : ℝ) : Line2D :=
  x • D2.e23 + y • D2.e31 + z • D2.e12

/-- A 2D motor with Terathon's four components
`x e₁ + y e₂ + z e₃ + w 1`. -/
def motor2 (x y z w : ℝ) : Motor2D :=
  x • D2.e1 + y • D2.e2 + z • D2.e3 + w • (1 : D2.GA)

/-- The identity 2D motor. -/
def identityMotor2 : Motor2D := 1

/-- A 2D flector `x e₂₃ + y e₃₁ + z e₁₂ + w 1`. -/
def flector2 (x y z w : ℝ) : Flector2D :=
  x • D2.e23 + y • D2.e31 + z • D2.e12 + w • (1 : D2.GA)

/-- A 3D Euclidean point, homogenized as `x e₁ + y e₂ + z e₃ + e₄`. -/
def flatPoint3 (x y z : ℝ) : FlatPoint3D :=
  x • D3.e1 + y • D3.e2 + z • D3.e3 + D3.e4

/-- A general 3D flat point with homogeneous weight. -/
def flatPoint3WithWeight (x y z w : ℝ) : FlatPoint3D :=
  x • D3.e1 + y • D3.e2 + z • D3.e3 + w • D3.e4

/-- The origin of 3D affine space. -/
def origin3 : FlatPoint3D := D3.e4

/-- A 3D line with direction `(vx, vy, vz)` and moment `(mx, my, mz)`:
`vx e₄₁ + vy e₄₂ + vz e₄₃ + mx e₂₃ + my e₃₁ + mz e₁₂`. -/
def line3 (vx vy vz mx my mz : ℝ) : Line3D :=
  vx • D3.e41 + vy • D3.e42 + vz • D3.e43 +
    mx • D3.e23 + my • D3.e31 + mz • D3.e12

/-- A 3D plane `a e₂₃₄ + b e₃₁₄ + c e₁₂₄ + d e₃₂₁`. -/
def plane3 (a b c d : ℝ) : Plane3D :=
  a • D3.e234 + b • D3.e314 + c • D3.e124 + d • D3.e321

/-- A 3D motor with Terathon's eight components:
`vx e₄₁ + vy e₄₂ + vz e₄₃ + vw 1 + mx e₂₃ + my e₃₁ + mz e₁₂ + mw e₁₂₃₄`. -/
def motor3 (vx vy vz vw mx my mz mw : ℝ) : Motor3D :=
  vx • D3.e41 + vy • D3.e42 + vz • D3.e43 + vw • (1 : D3.GA) +
    mx • D3.e23 + my • D3.e31 + mz • D3.e12 + mw • D3.e1234

/-- The identity 3D motor. -/
def identityMotor3 : Motor3D := 1

/-- A 3D flector with point coordinates on `e₁, e₂, e₃, e₄` and plane
coordinates on `e₂₃₄, e₃₁₄, e₁₂₄, e₃₂₁`. -/
def flector3 (px py pz pw gx gy gz gw : ℝ) : Flector3D :=
  px • D3.e1 + py • D3.e2 + pz • D3.e3 + pw • D3.e4 +
    gx • D3.e234 + gy • D3.e314 + gz • D3.e124 + gw • D3.e321

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

/-- The sandwich action `Q p Q̰`.  This is Terathon's `Transform(p, Q)`. -/
def sandwich {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (q p : CliffordAlgebra Q) : CliffordAlgebra Q :=
  q * p * CliffordAlgebra.reverse q

@[simp]
theorem reverse_reverse {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (x : CliffordAlgebra Q) :
    reverse (reverse x) = x :=
  CliffordAlgebra.reverse_reverse x

/-- The identity motor acts trivially. -/
@[simp]
theorem sandwich_one {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (p : CliffordAlgebra Q) : sandwich 1 p = p := by
  simp [sandwich]

/-- The sandwich action is a right action of the algebra on itself. -/
theorem sandwich_mul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {Q : QuadraticForm R M} (q r p : CliffordAlgebra Q) :
    sandwich q (sandwich r p) = sandwich (q * r) p := by
  simp [sandwich, mul_assoc]

/-- Transform a 2D flat point by a motor. -/
def transform2 (p : FlatPoint2D) (Q : Motor2D) : FlatPoint2D := sandwich Q p

/-- Transform a 3D flat point by a motor. -/
def transform3 (p : FlatPoint3D) (Q : Motor3D) : FlatPoint3D := sandwich Q p

/-- Transform a 3D line by a motor. -/
def transformLine3 (l : Line3D) (Q : Motor3D) : Line3D := sandwich Q l

/-- Transform a 3D plane by a motor. -/
def transformPlane3 (g : Plane3D) (Q : Motor3D) : Plane3D := sandwich Q g

/-- Reflect a 3D flat point with a flector. -/
def reflectPoint3 (p : FlatPoint3D) (F : Flector3D) : FlatPoint3D := sandwich F p

/-! ## The generic bracket engine

Terathon's `TSAlgebra` is a C++ template layer that expands products of
basis blades at compile time.  In Lean the Clifford algebra *is* symbolic,
so the generic engine is just `CliffordAlgebra` itself.  This alias records
the correspondence; there is no runtime lookup table to port. -/

/-- Generic Clifford-algebra engine corresponding to Terathon's `TSAlgebra`. -/
abbrev TSAlgebra (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (Q : QuadraticForm R M) : Type _ :=
  CliffordAlgebra Q

end PGA
end Brane
