/-
Copyright (c) 2026 Brane contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brane contributors
-/
import Brane.DifferentialGeometry
import Brane.Shooting
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Parameterized chart mappings around a point

This file turns the ideas in `docs/chart-mapping.md` into Lean definitions.
A chart around a point `p` of a graph surface is a 2D parameterized map from a
flat UV domain into the surface. The file separates three concerns:

* **chart data**: a parameter-domain map `φ : Point2 → Point2` composed with
  `graph h`;
* **distortion**: the pullback of the graph metric through `φ`, measured like a
  texture-map Jacobian / first fundamental form;
* **projection families**: azimuthal radial profiles inspired by map
  projections, used to reparameterize a normal/exponential chart around `p`.

The exponential map itself is represented computationally by shooting a
geodesic with `Brane.Shoot.geoAccel`; the analytic existence/regularity bridge
is left as `sorry` where it would require ODE theory beyond this file.

## Main definitions

* `Brane.ChartMap.ParamChart`, `SurfaceChart`, `toSurface`;
* `Brane.ChartMap.chartJacobian`, `pullbackGram`;
* `Brane.ChartMap.areaScale`, `isConformalAt`, `isEqualAreaAt`;
* `Brane.ChartMap.RadialProfile` and standard azimuthal profiles;
* `Brane.ChartMap.azimuthalUV`, `azimuthalParamChart`;
* `Brane.ChartMap.expShoot`, `normalParamChart`.

## References

* `docs/chart-mapping.md`
* Wikipedia, [List of map projections](https://en.wikipedia.org/wiki/List_of_map_projections)
-/

@[expose] public section

namespace Brane
namespace ChartMap

open DiffGeom
open Matrix
open scoped Matrix RealInnerProductSpace

noncomputable section

/-! ## Charts

A parameter chart maps UV coordinates to parameter-plane coordinates. Composing
with `graph h` gives a surface chart in ambient `ℝ³`. This keeps the graph
parameterization explicit while allowing normal/exponential charts to be
expressed in the same parameter domain. -/

/-- A local chart expressed in graph parameter coordinates. -/
abbrev ParamChart : Type := Point2 → Point2

/-- A local chart into ambient `ℝ³`. -/
abbrev SurfaceChart : Type := Point2 → Point3

/-- The graph-surface chart induced by a parameter chart. -/
def toSurface (h : HeightFun) (φ : ParamChart) : SurfaceChart :=
  fun u => graph h (φ u)

/-- The identity parameter chart: the ordinary graph coordinates. -/
def idParamChart : ParamChart := fun u => u

@[simp]
theorem toSurface_id (h : HeightFun) : toSurface h idParamChart = fun u => graph h u := rfl

/-! ## Pullback metric / distortion

The differential of a parameter chart is a `2×2` matrix. Its pullback of the
graph metric is `Jᵀ * G * J`, the same object used to measure texture stretch. -/

/-- Jacobian of a parameter chart `φ = (φ₁, φ₂)` with respect to UV
coordinates `(u,v)`. Rows are target parameter components, columns are UV
partials. -/
def chartJacobian (φ : ParamChart) (u : Point2) : Mat22 :=
  !![deriv (fun t => (φ (t, u.2)).1) u.1, deriv (fun t => (φ (u.1, t)).1) u.2;
     deriv (fun t => (φ (t, u.2)).2) u.1, deriv (fun t => (φ (u.1, t)).2) u.2]

/-- Pullback of the graph metric `gramMatrix h` by a parameter chart. -/
def pullbackGram (h : HeightFun) (φ : ParamChart) (u : Point2) : Mat22 :=
  (chartJacobian φ u)ᵀ * gramMatrix h (φ u) * chartJacobian φ u

/-- Local area scale of a chart, as in texture-map texel footprint area. -/
def areaScale (h : HeightFun) (φ : ParamChart) (u : Point2) : ℝ :=
  (pullbackGram h φ u).det

/-- A chart is conformal at `u` when its pullback metric is a scalar multiple of
the identity. -/
def isConformalAt (h : HeightFun) (φ : ParamChart) (u : Point2) : Prop :=
  ∃ scale : ℝ, pullbackGram h φ u = scale • (1 : Mat22)

/-- A chart is equal-area at `u` when its pullback area scale is `1`. -/
def isEqualAreaAt (h : HeightFun) (φ : ParamChart) (u : Point2) : Prop :=
  areaScale h φ u = 1

/-- A chart is locally isometric at `u` when it pulls the surface metric back to
the Euclidean UV metric. -/
def isIsometricAt (h : HeightFun) (φ : ParamChart) (u : Point2) : Prop :=
  pullbackGram h φ u = 1

theorem isIsometricAt.isConformalAt {h : HeightFun} {φ : ParamChart} {u : Point2}
    (hi : isIsometricAt h φ u) : isConformalAt h φ u := by
  refine ⟨1, ?_⟩
  simpa [isIsometricAt] using hi

theorem isIsometricAt.isEqualAreaAt {h : HeightFun} {φ : ParamChart} {u : Point2}
    (hi : isIsometricAt h φ u) : isEqualAreaAt h φ u := by
  change (pullbackGram h φ u).det = 1
  rw [hi]
  simp

/-! ## Azimuthal radial profiles

Map projections centered at a point can be seen as radial reparameterizations of
an azimuthal chart. On a general manifold, we use them as profile functions
composed with a geodesic/exponential direction field. -/

/-- A radial profile maps a UV radius to the geodesic radius used by an
azimuthal chart. `radius 0 = 0` keeps the center fixed. -/
structure RadialProfile where
  /-- Profile name, e.g. "equidistant". -/
  name : String
  /-- Radius reparameterization. -/
  radius : ℝ → ℝ
  /-- The center is fixed. -/
  radius_zero : radius 0 = 0

/-- Azimuthal equidistant profile: radial geodesic distance is preserved. -/
def equidistantProfile : RadialProfile where
  name := "equidistant"
  radius := fun r => r
  radius_zero := rfl

/-- Gnomonic-style profile on a sphere of radius `R`: `R * tan(r/R)`.
On a general manifold this is used as a radial reparameterization analogue. -/
def gnomonicProfile (R : ℝ) : RadialProfile where
  name := "gnomonic"
  radius := fun r => R * Real.tan (r / R)
  radius_zero := by simp

/-- Stereographic-style profile on a sphere of radius `R`: `2R * tan(r/(2R))`. -/
def stereographicProfile (R : ℝ) : RadialProfile where
  name := "stereographic"
  radius := fun r => 2 * R * Real.tan (r / (2 * R))
  radius_zero := by simp

/-- Lambert-azimuthal-equal-area-style profile on a sphere of radius `R`:
`2R * sin(r/(2R))`. -/
def lambertEqualAreaProfile (R : ℝ) : RadialProfile where
  name := "lambert-azimuthal-equal-area"
  radius := fun r => 2 * R * Real.sin (r / (2 * R))
  radius_zero := by simp

/-- Orthographic-style profile on a sphere of radius `R`: `R * sin(r/R)`. -/
def orthographicProfile (R : ℝ) : RadialProfile where
  name := "orthographic"
  radius := fun r => R * Real.sin (r / R)
  radius_zero := by simp

/-! ## Azimuthal UV coordinates

A local azimuthal chart can be described in polar UV coordinates `(r,θ)` or in
Cartesian UV coordinates `(u,v')` with `r = sqrt(u^2+v'^2)`. The profile acts on
`r`; the direction is the UV direction. -/

/-- Euclidean radius of a UV point. -/
def uvRadius (u : Point2) : ℝ := Real.sqrt (u.1 * u.1 + u.2 * u.2)

/-- Unit direction of a UV point; returns `(0,0)` at the origin. -/
def uvDir (u : Point2) : Point2 :=
  let r := uvRadius u
  if r = 0 then (0, 0) else (u.1 / r, u.2 / r)

/-- Apply an azimuthal radial profile to a Cartesian UV coordinate. -/
def azimuthalUV (P : RadialProfile) (u : Point2) : Point2 :=
  let r := uvRadius u
  let d := uvDir u
  let ρ := P.radius r
  (ρ * d.1, ρ * d.2)

@[simp]
theorem azimuthalUV_zero (P : RadialProfile) : azimuthalUV P (0, 0) = (0, 0) := by
  simp [azimuthalUV, uvRadius, uvDir, P.radius_zero]

/-! ## Parameter-frame azimuthal charts

On a graph surface, the parameter-plane velocity `Vel2` pushes forward by the
graph differential. A centered chart can therefore be specified by a center
parameter point and two parameter basis directions. -/

/-- An azimuthal chart in parameter coordinates, centered at `p`, using two
parameter directions `e1 e2 : Vel2` as the UV basis. The radial profile is
applied to the UV radius before combining directions. -/
def azimuthalParamChart (P : RadialProfile) (p : Point2) (e1 e2 : Vel2) : ParamChart :=
  fun u =>
    let a := azimuthalUV P u
    (p.1 + a.1 * e1 0 + a.2 * e2 0, p.2 + a.1 * e1 1 + a.2 * e2 1)

@[simp]
theorem azimuthalParamChart_zero (P : RadialProfile) (p : Point2) (e1 e2 : Vel2) :
    azimuthalParamChart P p e1 e2 (0, 0) = p := by
  simp [azimuthalParamChart]

/-! ## Computational exponential map by shooting

For a graph surface, geodesics in parameter space are given by `Shoot.geoAccel`.
Shooting a geodesic for unit time from `(p,v)` is a computational exponential
map in parameter coordinates. This uses the abstract `Shoot` kernel over `ℝ`. -/

/-- Initial shot state at parameter point `p` with parameter velocity `v`. -/
def shootState (p : Point2) (v : Vel2) : Shoot.ShotState ℝ where
  pos := p
  vel := v

/-- Computational exponential map in graph parameter coordinates: shoot a
geodesic with initial velocity `v` for `n` RK4 steps of size `dt`. -/
def expShoot (h : HeightFun) (p : Point2) (v : Vel2) (dt : ℝ) (n : ℕ) : Point2 :=
  (Shoot.rk4Trajectory h (shootState p v) dt n).pos

/-- Normal/azimuthal parameter chart built from the computational exponential
map. The UV coordinates select a parameter-plane tangent velocity in the chosen
frame; the profile rescales the UV radius before shooting. -/
def normalParamChart (h : HeightFun) (P : RadialProfile) (p : Point2)
    (e1 e2 : Vel2) (dt : ℝ) (n : ℕ) : ParamChart :=
  fun u =>
    let a := azimuthalUV P u
    let v : Vel2 := ![a.1 * e1 0 + a.2 * e2 0, a.1 * e1 1 + a.2 * e2 1]
    expShoot h p v dt n

/-- The center of a normal chart is the base point, assuming a zero-velocity
geodesic stays at `p`. This is the intended computational contract; the analytic
ODE proof is left as a bridge. -/
theorem normalParamChart_zero (h : HeightFun) (P : RadialProfile) (p : Point2)
    (e1 e2 : Vel2) (dt : ℝ) (n : ℕ) :
    normalParamChart h P p e1 e2 dt n (0, 0) = p := by
  -- This should follow from `azimuthalUV P (0,0)=0`, `v=0`, and the geodesic
  -- ODE with zero initial velocity. The shooting integrator bridge is not yet
  -- proved in this repository.
  sorry

/-! ## Projection-family chart specification

A projection family is a named radial profile plus the intended distortion
property. The property is stated as a predicate so sphere-exact invariants can
be distinguished from general Riemannian approximations. -/

/-- A named chart/projection choice around a point. -/
structure ProjectionFamily where
  /-- Human-readable name. -/
  name : String
  /-- Radial profile used to reparameterize UV radius. -/
  profile : RadialProfile
  /-- Intended distortion objective, e.g. conformal or equal-area. -/
  objective : String

def equidistantAzimuthal : ProjectionFamily where
  name := "azimuthal-equidistant"
  profile := equidistantProfile
  objective := "preserve radial geodesic distance from center"

def gnomonicAzimuthal (R : ℝ) : ProjectionFamily where
  name := "gnomonic"
  profile := gnomonicProfile R
  objective := "map radial geodesics straight; sphere geodesics straight in constant curvature"

def stereographicAzimuthal (R : ℝ) : ProjectionFamily where
  name := "stereographic"
  profile := stereographicProfile R
  objective := "conformal in the spherical azimuthal model"

def lambertAzimuthal (R : ℝ) : ProjectionFamily where
  name := "lambert-azimuthal-equal-area"
  profile := lambertEqualAreaProfile R
  objective := "equal-area in the spherical azimuthal model"

def orthographicAzimuthal (R : ℝ) : ProjectionFamily where
  name := "orthographic"
  profile := orthographicProfile R
  objective := "perspective/tangent-plane projection in the spherical model"

end

end ChartMap
end Brane
