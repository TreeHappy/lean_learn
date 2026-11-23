/-
Copyright (c) 2026 Brane contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brane contributors
-/
import Brane.DifferentialGeometry

/-!
# Affine connections, Christoffel symbols, and curvature

This file develops the infinitesimal side of the graph-surface geometry of
`Brane.DiffGeom`: a connection on the parameter plane `M = ℝ²`, its
Christoffel symbols, the Levi-Civita connection of the induced metric, and
the torsion and curvature tensors. It also packages a connection on a
vector bundle, of which an affine connection is the tangent-bundle special
case.

Everything is *unbundled and coordinate-based*: the manifold is the
parameter plane `Point2 = ℝ × ℝ`, a vector field is a function
`ParamField = Point2 → Vel2`, and the metric is the first fundamental form
`gramMatrix h` of `Brane.DiffGeom`. This keeps the definitions elementary
(`deriv`, `fderiv`, `Matrix`) while matching the Wikipedia definitions
point for point.

## The dictionary

* a **parameter vector field** is `X : ParamField`, i.e. `X p : Vel2`;
* the **directional derivative** of `Y` along `X` at `p` is `dirDeriv Y p (X p)`;
* an **affine connection** is a bilinear operation `∇ : ParamField → ParamField → ParamField`
  that is `C∞`-linear in the first argument and satisfies the Leibniz rule
  in the second (`AffineConnection`);
* the **flat connection** `flatConn` is ordinary directional differentiation;
* the **Christoffel symbols** of a metric `g` are `christoffel g`, and
  `covOfChristoffel` turns symbols into a connection;
* the **Levi-Civita connection** of the graph is `leviCivita h`, built from
  `gramMatrix h`;
* the **torsion** and **curvature** of a connection are `torsion` and
  `curvature`.

## Main definitions

* `Brane.Conn.ParamField`, `ScalarField`, `velToDir`, `dirDeriv`,
  `dirDerivScalar`;
* `Brane.Conn.AffineConnection` (with the two Wikipedia axioms);
* `Brane.Conn.flatConn`;
* `Brane.Conn.metricPartial`, `christoffel`, `christoffelCorr`,
  `covOfChristoffel`, `leviCivita`;
* `Brane.Conn.lieBracketParam`, `torsion`, `curvature`;
* `Brane.Conn.VectorBundleConnection`, `affineAsVectorBundle`,
  `vbcCurvature`.

## Status of proofs

The algebraic lemmas (directional-derivative linearity, Christoffel
symmetry, the axioms of `flatConn` and `covOfChristoffel`) are proved.
The geometric bridges — torsion-freeness and metric compatibility of the
Levi-Civita connection, tensoriality of torsion and curvature, the
induced-connection product rules — are stated and left as `sorry`, in the
same spirit as `Brane.GADiffGeom`.

## Tags

affine connection, Christoffel symbols, Levi-Civita connection, torsion,
curvature, vector bundle connection
-/

namespace Brane
namespace Conn

open DiffGeom
open Matrix

noncomputable section

/-! ## Parameter-plane vector fields

The parameter plane `Point2 = ℝ × ℝ` is the manifold. A vector field on it
is a function `Point2 → Vel2`; a scalar field is a height function
`ℝ → ℝ → ℝ`, i.e. `HeightFun`. -/

/-- A vector field on the parameter plane: a `Vel2`-valued function on `Point2`. -/
abbrev ParamField : Type := Point2 → Vel2

/-- A scalar field on the parameter plane: a height function `ℝ → ℝ → ℝ`. -/
abbrev ScalarField : Type := HeightFun

/-- The direction in the parameter plane represented by a velocity:
`velToDir v = (v₀, v₁)`. -/
def velToDir (v : Vel2) : Point2 := (v 0, v 1)

@[simp]
theorem velToDir_add (v w : Vel2) : velToDir (v + w) = velToDir v + velToDir w := rfl

@[simp]
theorem velToDir_smul (a : ℝ) (v : Vel2) : velToDir (a • v) = a • velToDir v := by
  simp [velToDir, smul_eq_mul]

/-- The directional derivative of a parameter vector field `Y` at `p` along
the velocity `v`: the Fréchet derivative of `Y` at `p` applied to the
direction `velToDir v`. -/
def dirDeriv (Y : ParamField) (p : Point2) (v : Vel2) : Vel2 :=
  fderiv ℝ Y p (velToDir v)

/-- The directional derivative of a scalar field `f` at `p` along `v`. -/
def dirDerivScalar (f : ScalarField) (p : Point2) (v : Vel2) : ℝ :=
  fderiv ℝ (fun q : Point2 => f q.1 q.2) p (velToDir v)

/-! ### Linearity of the directional derivative

The directional derivative is linear in the direction for *every* field
(no smoothness needed), and linear in the field once the field is
differentiable. These are the algebraic lemmas used by the connection
axioms. -/

theorem dirDeriv_add_direction (Y : ParamField) (p : Point2) (v w : Vel2) :
    dirDeriv Y p (v + w) = dirDeriv Y p v + dirDeriv Y p w := by
  simp [dirDeriv]

theorem dirDeriv_smul_direction (Y : ParamField) (p : Point2) (a : ℝ) (v : Vel2) :
    dirDeriv Y p (a • v) = a • dirDeriv Y p v := by
  simp [dirDeriv]

theorem dirDeriv_add_Y (Y Y' : ParamField) (p : Point2) (v : Vel2)
    (hY : DifferentiableAt ℝ Y p) (hY' : DifferentiableAt ℝ Y' p) :
    dirDeriv (fun q => Y q + Y' q) p v = dirDeriv Y p v + dirDeriv Y' p v := by
  simp only [dirDeriv]
  rw [show (fun q => Y q + Y' q) = Y + Y' from rfl, fderiv_add hY hY']
  simp

theorem dirDeriv_smul_Y (a : ℝ) (Y : ParamField) (p : Point2) (v : Vel2)
    (hY : DifferentiableAt ℝ Y p) :
    dirDeriv (fun q => a • Y q) p v = a • dirDeriv Y p v := by
  simp only [dirDeriv]
  rw [show (fun q => a • Y q) = a • Y from rfl, fderiv_const_smul hY a]
  simp

theorem dirDeriv_smul_scalar (f : ScalarField) (Y : ParamField) (p : Point2) (v : Vel2)
    (hf : DifferentiableAt ℝ (fun q : Point2 => f q.1 q.2) p) (hY : DifferentiableAt ℝ Y p) :
    dirDeriv (fun q => f q.1 q.2 • Y q) p v =
      dirDerivScalar f p v • Y p + f p.1 p.2 • dirDeriv Y p v := by
  simp only [dirDeriv, dirDerivScalar]
  rw [fderiv_fun_smul hf hY]
  simp
  abel

/-! ## The affine connection axioms

An affine connection is a bilinear operation on vector fields that is
`C∞`-linear in the first argument and satisfies the Leibniz rule in the
second. This is the differential-operator definition from the Wikipedia
page. The differentiability side conditions are exactly what is needed to
make the Leibniz rule meaningful. -/

/-- An **affine connection** on the parameter plane: a map
`∇ : ParamField → ParamField → ParamField` that is `C∞`-linear in the
first argument and satisfies the Leibniz rule in the second.

For a smooth scalar field `f` and vector fields `X`, `Y`:

* `∇_(fX) Y = f ∇_X Y` (`cov_smul_left`, with `cov_add_left`);
* `∇_X (fY) = (∂_X f) Y + f ∇_X Y` (`cov_leibniz`, with `cov_add_right`
  and `cov_smul_right`). -/
structure AffineConnection where
  /-- The covariant derivative `∇_X Y`. -/
  cov : ParamField → ParamField → ParamField
  /-- `∇` is additive in the first argument. -/
  cov_add_left : ∀ X X' Y,
    cov (fun p => X p + X' p) Y = fun p => cov X Y p + cov X' Y p
  /-- `∇` is `C∞`-linear in the first argument. -/
  cov_smul_left : ∀ (f : ScalarField) X Y,
    cov (fun p => f p.1 p.2 • X p) Y = fun p => f p.1 p.2 • cov X Y p
  /-- `∇` is additive in the second argument. -/
  cov_add_right : ∀ X Y Y', Differentiable ℝ Y → Differentiable ℝ Y' →
    cov X (fun p => Y p + Y' p) = fun p => cov X Y p + cov X Y' p
  /-- `∇` is `ℝ`-linear in the second argument. -/
  cov_smul_right : ∀ (a : ℝ) X Y, Differentiable ℝ Y →
    cov X (fun p => a • Y p) = fun p => a • cov X Y p
  /-- `∇` satisfies the Leibniz rule in the second argument. -/
  cov_leibniz : ∀ (f : ScalarField) X Y,
    Differentiable ℝ (fun p : Point2 => f p.1 p.2) → Differentiable ℝ Y →
    cov X (fun p => f p.1 p.2 • Y p) =
      fun p => dirDerivScalar f p (X p) • Y p + f p.1 p.2 • cov X Y p

/-! ## The flat connection

The canonical connection on the parameter plane: differentiate a vector
field by ordinary directional differentiation. All four axioms are proved
directly from the linearity lemmas above. -/

/-- The **flat (Euclidean) connection** on the parameter plane:
`∇_X Y = dY(X)`, the directional derivative of `Y` along `X`. -/
def flatConn : AffineConnection where
  cov X Y := fun p => dirDeriv Y p (X p)
  cov_add_left := by
    intro X X' Y
    funext p
    rw [dirDeriv_add_direction]
  cov_smul_left := by
    intro f X Y
    funext p
    rw [dirDeriv_smul_direction]
  cov_add_right := by
    intro X Y Y' hY hY'
    funext p
    rw [dirDeriv_add_Y Y Y' p (X p) hY.differentiableAt hY'.differentiableAt]
  cov_smul_right := by
    intro a X Y hY
    funext p
    rw [dirDeriv_smul_Y a Y p (X p) hY.differentiableAt]
  cov_leibniz := by
    intro f X Y hf hY
    funext p
    rw [dirDeriv_smul_scalar f Y p (X p) hf.differentiableAt hY.differentiableAt]

/-! ## Christoffel symbols and the Levi-Civita connection

A metric on the parameter plane is a smoothly varying `2×2` matrix
`g : Point2 → Mat22`; for the graph surface this is the first fundamental
form `gramMatrix h`. The Christoffel symbols of the second kind are

`Γ^k_ij = ½ (g⁻¹)^kl (∂_i g_jl + ∂_j g_il − ∂_l g_ij)`,

and they determine a connection by adding the correction
`Γ^k_ij X^i Y^j` to the flat directional derivative. -/

/-- The partial derivative `∂_i g_jl` of a metric, in the `i`-th coordinate
direction (`i = 0` is `x`, `i = 1` is `y`). -/
def metricPartial (g : Point2 → Mat22) (i j l : Fin 2) (p : Point2) : ℝ :=
  if i = 0 then deriv (fun t : ℝ => g (t, p.2) j l) p.1
  else deriv (fun t : ℝ => g (p.1, t) j l) p.2

/-- The **Christoffel symbols of the second kind** of a metric `g`:
`christoffel g p k` is the matrix `(i, j) ↦ Γ^k_ij`. -/
noncomputable def christoffel (g : Point2 → Mat22) (p : Point2) (k : Fin 2) : Mat22 :=
  Matrix.of fun i j =>
    ∑ l : Fin 2,
      (g p)⁻¹ k l * (metricPartial g i j l p + metricPartial g j i l p -
        metricPartial g l i j p) / 2

/-- The Christoffel correction term: the `Vel2` with components
`Γ^k_ij X^i Y^j`. -/
def christoffelCorr (Γ : Point2 → Fin 2 → Mat22) (p : Point2) (X Y : Vel2) : Vel2 :=
  fun k => ∑ i : Fin 2, ∑ j : Fin 2, (Γ p k) i j * X i * Y j

@[simp]
theorem christoffelCorr_add_left (Γ : Point2 → Fin 2 → Mat22) (p : Point2)
    (X X' Y : Vel2) :
    christoffelCorr Γ p (X + X') Y =
      christoffelCorr Γ p X Y + christoffelCorr Γ p X' Y := by
  funext k
  simp only [christoffelCorr, Pi.add_apply, Fin.sum_univ_two]
  ring

@[simp]
theorem christoffelCorr_smul_left (Γ : Point2 → Fin 2 → Mat22) (p : Point2)
    (a : ℝ) (X Y : Vel2) :
    christoffelCorr Γ p (a • X) Y = a • christoffelCorr Γ p X Y := by
  funext k
  simp only [christoffelCorr, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  ring

@[simp]
theorem christoffelCorr_add_right (Γ : Point2 → Fin 2 → Mat22) (p : Point2)
    (X Y Y' : Vel2) :
    christoffelCorr Γ p X (Y + Y') =
      christoffelCorr Γ p X Y + christoffelCorr Γ p X Y' := by
  funext k
  simp only [christoffelCorr, Pi.add_apply, Fin.sum_univ_two]
  ring

@[simp]
theorem christoffelCorr_smul_right (Γ : Point2 → Fin 2 → Mat22) (p : Point2)
    (a : ℝ) (X Y : Vel2) :
    christoffelCorr Γ p X (a • Y) = a • christoffelCorr Γ p X Y := by
  funext k
  simp only [christoffelCorr, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
  ring

/-- The connection determined by Christoffel symbols:
`∇_X Y = dY(X) + Γ(X, Y)`. -/
def covOfChristoffel (Γ : Point2 → Fin 2 → Mat22) : AffineConnection where
  cov X Y := fun p => dirDeriv Y p (X p) + christoffelCorr Γ p (X p) (Y p)
  cov_add_left := by
    intro X X' Y
    funext p
    rw [dirDeriv_add_direction, christoffelCorr_add_left]
    abel
  cov_smul_left := by
    intro f X Y
    funext p
    rw [dirDeriv_smul_direction, christoffelCorr_smul_left]
    rw [smul_add]
  cov_add_right := by
    intro X Y Y' hY hY'
    funext p
    rw [dirDeriv_add_Y Y Y' p (X p) hY.differentiableAt hY'.differentiableAt,
      christoffelCorr_add_right]
    abel
  cov_smul_right := by
    intro a X Y hY
    funext p
    rw [dirDeriv_smul_Y a Y p (X p) hY.differentiableAt, christoffelCorr_smul_right]
    rw [smul_add]
  cov_leibniz := by
    intro f X Y hf hY
    funext p
    rw [dirDeriv_smul_scalar f Y p (X p) hf.differentiableAt hY.differentiableAt,
      christoffelCorr_smul_right, smul_add]
    abel

/-- The **Levi-Civita connection** of a height function `h`: the connection
whose Christoffel symbols are those of the first fundamental form
`gramMatrix h`. It is torsion-free and metric-compatible
(`leviCivita_torsion_free`, `leviCivita_metric_compatible`, both `sorry`). -/
def leviCivita (h : HeightFun) : AffineConnection :=
  covOfChristoffel (christoffel (gramMatrix h))

/-- The Christoffel symbols of a symmetric metric are symmetric in the two
lower indices: `Γ^k_ij = Γ^k_ji`. -/
theorem christoffel_symm (g : Point2 → Mat22) (hsym : ∀ p a b, g p a b = g p b a)
    (p : Point2) (k i j : Fin 2) :
    christoffel g p k i j = christoffel g p k j i := by
  simp only [christoffel, Matrix.of_apply]
  have h : ∀ l : Fin 2, metricPartial g l i j p = metricPartial g l j i p := by
    intro l
    unfold metricPartial
    split_ifs <;> simp [hsym]
  simp [h]
  ring

/-! ## Torsion and curvature

The two invariants of an affine connection. Torsion measures the failure of
`∇_X Y - ∇_Y X` to recover the Lie bracket of vector fields; curvature
measures the failure of second covariant derivatives to commute. -/

/-- The **Lie bracket** of two parameter vector fields:
`[X, Y] = dY(X) - dX(Y)`. -/
def lieBracketParam (X Y : ParamField) : ParamField :=
  fun p => dirDeriv Y p (X p) - dirDeriv X p (Y p)

/-- The **torsion** of an affine connection:
`T(X, Y) = ∇_X Y - ∇_Y X - [X, Y]`. -/
def torsion (D : AffineConnection) (X Y : ParamField) : ParamField :=
  fun p => D.cov X Y p - D.cov Y X p - lieBracketParam X Y p

/-- The **curvature** of an affine connection:
`R(X, Y) Z = ∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_[X,Y] Z`. -/
def curvature (D : AffineConnection) (X Y Z : ParamField) : ParamField :=
  fun p => D.cov X (D.cov Y Z) p - D.cov Y (D.cov X Z) p -
    D.cov (lieBracketParam X Y) Z p

/-- The Levi-Civita connection is torsion-free. -/
theorem leviCivita_torsion_free (h : HeightFun) (X Y : ParamField) :
    torsion (leviCivita h) X Y = 0 := by
  sorry

/-- The Levi-Civita connection is compatible with the induced metric:
`X⟨Y, Z⟩ = ⟨∇_X Y, Z⟩ + ⟨Y, ∇_X Z⟩`. -/
theorem leviCivita_metric_compatible (h : HeightFun) (X Y Z : ParamField)
    (p : Point2) :
    dirDerivScalar (fun x y => Y (x, y) ⬝ᵥ (gramMatrix h (x, y) *ᵥ Z (x, y))) p (X p) =
      (leviCivita h).cov X Y p ⬝ᵥ (gramMatrix h p *ᵥ Z p) +
        Y p ⬝ᵥ (gramMatrix h p *ᵥ (leviCivita h).cov X Z p) := by
  sorry

/-- The torsion is tensorial (alternating in `X`, `Y`). -/
theorem torsion_anti (D : AffineConnection) (X Y : ParamField) :
    torsion D X Y = -torsion D Y X := by
  sorry

/-- The curvature is tensorial in `X`, `Y`, `Z`. -/
theorem curvature_tensorial (D : AffineConnection) (X Y Z : ParamField) :
    curvature D X Y Z = -curvature D Y X Z := by
  sorry

/-- The fundamental theorem of Riemannian geometry: the Levi-Civita
connection is the unique torsion-free metric connection. -/
theorem leviCivita_unique (h : HeightFun) (D : AffineConnection)
    (htorsion : ∀ X Y, torsion D X Y = 0)
    (hmetric : ∀ X Y Z p,
      dirDerivScalar (fun x y => Y (x, y) ⬝ᵥ (gramMatrix h (x, y) *ᵥ Z (x, y))) p (X p) =
        D.cov X Y p ⬝ᵥ (gramMatrix h p *ᵥ Z p) +
          Y p ⬝ᵥ (gramMatrix h p *ᵥ D.cov X Z p)) :
    D = leviCivita h := by
  sorry

/-! ## Vector-bundle connections

A connection on a vector bundle `E → M` is the same kind of operation, but
on sections of an arbitrary fiber `F`. An affine connection is the special
case `F = Vel2` (the tangent bundle). -/

/-- A **connection on the trivial vector bundle** `Point2 × F`: a map
`∇ : ParamField → (Point2 → F) → Point2 → F` that is `C∞`-linear in the
vector field and satisfies the Leibniz rule in the section. -/
structure VectorBundleConnection (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- The covariant derivative `∇_X σ`. -/
  cov : ParamField → (Point2 → F) → (Point2 → F)
  /-- `C∞`-linearity in the vector field. -/
  cov_add_left : ∀ X X' σ,
    cov (fun p => X p + X' p) σ = fun p => cov X σ p + cov X' σ p
  cov_smul_left : ∀ (f : ScalarField) X σ,
    cov (fun p => f p.1 p.2 • X p) σ = fun p => f p.1 p.2 • cov X σ p
  /-- `ℝ`-linearity in the section. -/
  cov_add_right : ∀ X σ σ', Differentiable ℝ σ → Differentiable ℝ σ' →
    cov X (fun p => σ p + σ' p) = fun p => cov X σ p + cov X σ' p
  cov_smul_right : ∀ (a : ℝ) X σ, Differentiable ℝ σ →
    cov X (fun p => a • σ p) = fun p => a • cov X σ p
  /-- Leibniz rule in the section. -/
  cov_leibniz : ∀ (f : ScalarField) X σ,
    Differentiable ℝ (fun p : Point2 => f p.1 p.2) → Differentiable ℝ σ →
    cov X (fun p => f p.1 p.2 • σ p) =
      fun p => dirDerivScalar f p (X p) • σ p + f p.1 p.2 • cov X σ p

/-- An affine connection is a vector-bundle connection on the tangent
bundle `Point2 × Vel2`. -/
def affineAsVectorBundle (D : AffineConnection) : VectorBundleConnection Vel2 where
  cov := D.cov
  cov_add_left := D.cov_add_left
  cov_smul_left := D.cov_smul_left
  cov_add_right := D.cov_add_right
  cov_smul_right := D.cov_smul_right
  cov_leibniz := D.cov_leibniz

/-- The **curvature** of a vector-bundle connection:
`F(X, Y) σ = ∇_X ∇_Y σ - ∇_Y ∇_X σ - ∇_[X,Y] σ`. -/
def vbcCurvature {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : VectorBundleConnection F) (X Y : ParamField)
    (σ : Point2 → F) : Point2 → F :=
  fun p => D.cov X (D.cov Y σ) p - D.cov Y (D.cov X σ) p -
    D.cov (lieBracketParam X Y) σ p

/-- The dual connection on `F →L[ℝ] ℝ` exists and is characterized by the
product rule `⟨∇*_X ξ, σ⟩ = X⟨ξ, σ⟩ - ⟨ξ, ∇_X σ⟩`. -/
theorem dualConn_exists {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : VectorBundleConnection F) :
    ∃ D' : VectorBundleConnection (F →L[ℝ] ℝ),
      ∀ (X : ParamField) (ξ : Point2 → F →L[ℝ] ℝ) (σ : Point2 → F) (p : Point2),
        (D'.cov X ξ p) (σ p) =
          dirDerivScalar (fun x y => (ξ (x, y)) (σ (x, y))) p (X p) -
            (ξ p) (D.cov X σ p) := by
  sorry

/-- The tensor-product connection on `F × G` exists and satisfies the
product rule. -/
theorem tensorConn_exists {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (D₁ : VectorBundleConnection F) (D₂ : VectorBundleConnection G) :
    ∃ D' : VectorBundleConnection (F × G),
      ∀ (X : ParamField) (σ : Point2 → F) (τ : Point2 → G) (p : Point2),
        D'.cov X (fun q => (σ q, τ q)) p =
          (D₁.cov X σ p, D₂.cov X τ p) := by
  sorry

/-- The endomorphism connection on `F →L[ℝ] F` exists and satisfies
`∇_X (u σ) = (∇^End_X u) σ + u (∇_X σ)`. -/
theorem endConn_exists {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : VectorBundleConnection F) :
    ∃ D' : VectorBundleConnection (F →L[ℝ] F),
      ∀ (X : ParamField) (u : Point2 → F →L[ℝ] F) (σ : Point2 → F) (p : Point2),
        D'.cov X u p (σ p) =
          D.cov X (fun q => u q (σ q)) p - u p (D.cov X σ p) := by
  sorry

end

end Conn
end Brane
