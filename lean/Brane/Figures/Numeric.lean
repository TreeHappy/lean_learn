/-
Figures/Numeric.lean: a computable Float mirror of the geodesic pipeline.

The mathematical definitions in `Brane.DiffGeom` / `Brane.Shoot` live over
`ℝ` (they use `deriv` and Mathlib matrices) and sit in a `noncomputable
section`, so they cannot be executed by `lake exe gen-figures`. This module
re-implements *the same formulas* over `Float` so the figures are actually
computed from the mathematics the documentation describes, not hand-drawn:

  `DiffGeom.partialX/Y`      ↦ `partialXF` / `partialYF`   (central differences)
  `DiffGeom.gramMatrix`      ↦ `gramF`                     (G = JᵀJ, expanded)
  `Shoot.hessQuad`           ↦ `hessQuadF`                 (vᵀ H v)
  `Shoot.geoAccel`           ↦ `geoAccelF`                 (-G⁻¹ ((vᵀHv) ∇h))
  `Shoot.field`              ↦ `fieldF`
  `Shoot.eulerStep/rk4Step`  ↦ `eulerStepF` / `rk4StepF`
  `Shoot.shoot`              ↦ `shootF`
  `DiffGeom.bowlHeight` etc. ↦ `hBowlF`, `hSaddleF`, `hPlaneF`

Each definition cites its noncomputable counterpart; consult
`docs/shooting-method.md` for the derivations.
-/

namespace Brane.Figures.Numeric

/-- A height function over the plane, computable version of `HeightFun`. -/
def HeightFunF := Float → Float → Float

/-- Finite-difference step for the derivative approximations. -/
def eps : Float := 0.0001

/-! ## Height functions (mirrors of the DiffGeom examples) -/

/-- Mirror of `DiffGeom.bowlHeight`: `z = x² + y²`. -/
def hBowlF (x y : Float) : Float := x * x + y * y

/-- Mirror of `DiffGeom.saddleHeight`: `z = x² - y²`. -/
def hSaddleF (x y : Float) : Float := x * x - y * y

/-- Mirror of `DiffGeom.planeHeight`: `z = a·x + b·y + c`. -/
def hPlaneF (a b c : Float) : HeightFunF := fun x y => a * x + b * y + c

/-! ## Partials (central differences; mirrors of `partialX`, `partialY`, …) -/

/-- Mirror of `DiffGeom.partialX h`. -/
def partialXF (h : HeightFunF) (x y : Float) : Float :=
  (h (x + eps) y - h (x - eps) y) / (2 * eps)

/-- Mirror of `DiffGeom.partialY h`. -/
def partialYF (h : HeightFunF) (x y : Float) : Float :=
  (h x (y + eps) - h x (y - eps)) / (2 * eps)

/-- Mirror of `DiffGeom.partialXX h`. -/
def partialXXF (h : HeightFunF) (x y : Float) : Float :=
  (partialXF h (x + eps) y - partialXF h (x - eps) y) / (2 * eps)

/-- Mirror of `DiffGeom.partialXY h`. -/
def partialXYF (h : HeightFunF) (x y : Float) : Float :=
  (partialXF h x (y + eps) - partialXF h x (y - eps)) / (2 * eps)

/-- Mirror of `DiffGeom.partialYY h`. -/
def partialYYF (h : HeightFunF) (x y : Float) : Float :=
  (partialYF h x (y + eps) - partialYF h x (y - eps)) / (2 * eps)

/-! ## The geodesic equation over Float -/

/-- Mirror of `Shoot.gradientVec`: `∇h = (∂ₓh, ∂ᵧh)`. -/
def gradientF (h : HeightFunF) (x y : Float) : Float × Float :=
  (partialXF h x y, partialYF h x y)

/-- Mirror of `Shoot.hessQuad`: `vᵀ H v`, with
`H = [[∂ₓₓh, ∂ₓᵧh], [∂ₓᵧh, ∂ᵧᵧh]]`. -/
def hessQuadF (h : HeightFunF) (x y : Float) (v₁ v₂ : Float) : Float :=
  let a := partialXXF h x y
  let b := partialXYF h x y
  let c := partialYYF h x y
  v₁ * (a * v₁ + b * v₂) + v₂ * (b * v₁ + c * v₂)

/-- Mirror of `DiffGeom.gramMatrix`, expanded: since the coordinate tangents
are `(1, 0, ∂ₓh)` and `(0, 1, ∂ᵧh)`, `G = JᵀJ = [[1+∂ₓh², ∂ₓh∂ᵧh], [∂ₓh∂ᵧh,
1+∂ᵧh²]]` (compare `det_gramMatrix_eq`: `det G = 1 + |∇h|² ≥ 1`). -/
def gramF (h : HeightFunF) (x y : Float) : Float × Float × Float :=
  let fx := partialXF h x y
  let fy := partialYF h x y
  (1 + fx * fx, fx * fy, 1 + fy * fy)

/-- Mirror of `Shoot.geoAccel`: `-G⁻¹ ((vᵀHv) ∇h)`, with the 2×2 inverse in
closed form. -/
def geoAccelF (h : HeightFunF) (x y : Float) (v₁ v₂ : Float) : Float × Float :=
  let (g11, g12, g22) := gramF h x y
  let det := g11 * g22 - g12 * g12
  let (fx, fy) := gradientF h x y
  let k := hessQuadF h x y v₁ v₂
  let m₁ := k * fx
  let m₂ := k * fy
  (-(g22 * m₁ - g12 * m₂) / det, -(-g12 * m₁ + g11 * m₂) / det)

/-! ## Integrators (mirrors of `Shoot.field`, `eulerStep`, `rk4Step`, `shoot`) -/

/-- The state of a shot, computable: position `(x, y)` and velocity
`(vx, vy)`. Mirror of `Shoot.ShotState`. -/
structure StateF where
  x : Float
  y : Float
  vx : Float
  vy : Float

/-- Coordinatewise addition. Mirror of `Shoot.addShotState`. -/
def addStateF (a b : StateF) : StateF :=
  ⟨a.x + b.x, a.y + b.y, a.vx + b.vx, a.vy + b.vy⟩

/-- Coordinatewise scalar multiplication. Mirror of `Shoot.smulShotState`. -/
def smulStateF (r : Float) (a : StateF) : StateF :=
  ⟨r * a.x, r * a.y, r * a.vx, r * a.vy⟩

/-- Mirror of `Shoot.field`: velocity plus geodesic acceleration. -/
def fieldF (h : HeightFunF) (s : StateF) : StateF :=
  let a := geoAccelF h s.x s.y s.vx s.vy
  ⟨s.vx, s.vy, a.1, a.2⟩

/-- Mirror of `Shoot.eulerStep`: `s + dt • field h s`. -/
def eulerStepF (h : HeightFunF) (s : StateF) (dt : Float) : StateF :=
  addStateF s (smulStateF dt (fieldF h s))

/-- Mirror of `Shoot.rk4Step`: `s + dt/6 • (k₁ + 2k₂ + 2k₃ + k₄)`. -/
def rk4StepF (h : HeightFunF) (s : StateF) (dt : Float) : StateF :=
  let k₁ := fieldF h s
  let k₂ := fieldF h (addStateF s (smulStateF (dt / 2) k₁))
  let k₃ := fieldF h (addStateF s (smulStateF (dt / 2) k₂))
  let k₄ := fieldF h (addStateF s (smulStateF dt k₃))
  let w := dt / 6
  addStateF s <|
    smulStateF w (addStateF k₁ <| addStateF (smulStateF 2 k₂) <|
      addStateF (smulStateF 2 k₃) k₄)

/-- Mirror of `Shoot.shoot`: iterate a stepper `n` times, returning every
sampled position `(x, y)` along the way (including the start). -/
def shootPositions (step : HeightFunF → StateF → Float → StateF)
    (h : HeightFunF) (s₀ : StateF) (dt : Float) (n : Nat) : Array (Float × Float) :=
  let rec go : Nat → StateF → Array (Float × Float) → Array (Float × Float)
    | 0, s, acc => acc.push (s.x, s.y)
    | (k + 1), s, acc => go k (step h s dt) (acc.push (s.x, s.y))
  go n s₀ #[] |>.reverse

end Brane.Figures.Numeric
