import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.DualNumber
import Brane.DifferentialGeometry
import Brane.PGA
import Brane.CGA

/-!
# Terathon compatibility surface

A single import that exposes the classes of the
[Terathon Math Library](https://github.com/EricLengyel/Terathon-Math-Library)
under the names used by the C++ headers.

The core linear-algebra classes are aliases for the corresponding Mathlib
types (the TODO table maps them this way); the rigid and conformal
geometric-algebra classes are the real port in `Brane.PGA` and `Brane.CGA`.
Nothing here introduces a new implementation: it is a naming layer so that
Lean code can be written in Terathon vocabulary without losing the Mathlib
API.

Namespace: `Brane.Terathon`.
-/

noncomputable section

namespace Brane
namespace Terathon

/-! ## Core linear algebra and numbers -/

/-- A 2D vector. -/
abbrev Vector2D : Type := Fin 2 → ℝ
/-- A 3D vector, using the ambient space of `Brane.DiffGeom`. -/
abbrev Vector3D : Type := DiffGeom.Vec3
/-- A 4D vector. -/
abbrev Vector4D : Type := Fin 4 → ℝ

/-- A 2D affine point `(x, y)`. -/
abbrev Point2D : Type := DiffGeom.Point2
/-- A 3D affine point. -/
abbrev Point3D : Type := DiffGeom.Point3

/-- A 2×2 matrix. -/
abbrev Matrix2D : Type := Matrix (Fin 2) (Fin 2) ℝ
/-- A 3×3 matrix. -/
abbrev Matrix3D : Type := Matrix (Fin 3) (Fin 3) ℝ
/-- A 4×4 matrix. -/
abbrev Matrix4D : Type := Matrix (Fin 4) (Fin 4) ℝ

/-- A 2D affine transform, represented by a 3×3 matrix. -/
abbrev Transform2D : Type := Matrix (Fin 3) (Fin 3) ℝ
/-- A 3D affine transform, represented by a 4×4 matrix. -/
abbrev Transform3D : Type := Matrix (Fin 4) (Fin 4) ℝ

/-- Terathon's quaternion, supplied by Mathlib. -/
abbrev Quaternion : Type := _root_.Quaternion ℝ
/-- Terathon's dual number `s + tε`, supplied by Mathlib. -/
abbrev DualNum : Type := _root_.DualNumber ℝ

/-! ## Rigid geometric algebra -/

abbrev FlatPoint2D : Type := PGA.FlatPoint2D
abbrev Line2D : Type := PGA.Line2D
abbrev Motor2D : Type := PGA.Motor2D
abbrev Flector2D : Type := PGA.Flector2D

abbrev FlatPoint3D : Type := PGA.FlatPoint3D
abbrev Line3D : Type := PGA.Line3D
abbrev Plane3D : Type := PGA.Plane3D
abbrev Motor3D : Type := PGA.Motor3D
abbrev Flector3D : Type := PGA.Flector3D

abbrev TSAlgebra := PGA.TSAlgebra

/-! ## Conformal geometric algebra -/

abbrev RoundPoint2D : Type := CGA.RoundPoint2D
abbrev Dipole2D : Type := CGA.Dipole2D
abbrev Circle2D : Type := CGA.Circle2D

abbrev RoundPoint3D : Type := CGA.RoundPoint3D
abbrev Dipole3D : Type := CGA.Dipole3D
abbrev Circle3D : Type := CGA.Circle3D
abbrev Sphere3D : Type := CGA.Sphere3D

end Terathon
end Brane
