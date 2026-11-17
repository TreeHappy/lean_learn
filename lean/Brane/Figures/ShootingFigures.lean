/-
Figures/ShootingFigures.lean: the nine figures referenced by
`docs/shooting-method.md`, built with Vizagrams prims.

Wherever a figure shows mathematics, the geometry is *computed* by the very
definitions documented in `docs/shooting-method.md`, instantiated at the
computable number type `Float` (the `GeoKernel Float` instance of
`Brane.Shoot`: central finite differences):

  * `height-function`, `parameter-plane` — the example surface `bowlHeight`;
  * `heightmap-lift` — the graph map `(x, y) ↦ (x, y, h(x, y))`;
  * `tangents`, `normal` — the partials `partialX` / `partialY` of the
    same kernel, evaluated at a point of the bowl;
  * `distorted-map`, `euler-drift` — real trajectories via `Shoot.rk4Step`
    and `Shoot.eulerStep` (so Euler's drift is Euler's actual error, not an
    illustration);
  * `rk4-slopes` — the actual `rk4Step` slope probes `k₁ … k₄`;
  * `geodesic-rule` — the only purely schematic figure.

Canvas convention: figures are authored in y-up math coordinates;
`Gen.lean` flips y and writes the SVG files.
-/

import Brane.Figures.Basic
import Brane.Shooting

namespace Brane.Figures

open GraphicalPrimitive Sty LinearAlgebra
open Brane.DiffGeom (bowlHeight saddleHeight planeHeight)
open Brane.Shoot (ShotState field eulerStep rk4Step shootPositions partialX partialY)
open scoped Matrix

/-! ## Palette (Catppuccin Latte, per the Catppuccin style guide) -/

def overlay  := "#9499bb"
def subtext  := "#6c6f85"
def text     := "#4c4f69"
def red      := "#d20f39"
def peach    := "#fe640b"
def yellow   := "#df8e1d"
def green    := "#40a02b"
def teal     := "#179299"
def blue     := "#1e66f5"
def mauve    := "#8839ef"

/-! ## Helpers -/

/-- A dashed line, drawn as alternating segments (Vizagrams' `Style` has no
dash attribute). -/
def dashedSeg (a b : Vec2) (hex : String) (w : Float) : Array Prim :=
  let d := b - a
  let len := vec_norm d
  let u := normalize d
  let step := 9.0
  (List.range ((len / step).toUInt32.toNat + 1)).foldl (init := #[]) fun acc i =>
    let s := i.toFloat * step
    let e := min (s + 4.5) len
    if s ≥ len then acc
    else acc ++ #[primLine (a + s • u) (a + e • u) hex w]

/-- Sample a quadratic Bézier curve as a polyline. -/
def qbezierPts (p0 ctrl p1 : Vec2) (n : Nat) : Array Vec2 :=
  (List.range (n + 1)).toArray.map fun i =>
    let t := i.toFloat / n.toFloat
    (1 - t) • p0 + (2 * t * (1 - t)) • ctrl + (t * t) • p1

/-- Map parameter-plane coordinates `(x, y) ∈ [0,4] × [0,3]` into a 720×290
canvas (y-up). -/
def planeMap (x y : Float) : Vec2 := ![80 + 120 * x, 60 + 70 * y]

/-- The rectangle of the parameter plane `[0,4] × [0,3]` on the canvas. -/
def planeQuad : Array Vec2 :=
  #[planeMap 0 0, planeMap 4 0, planeMap 4 3, planeMap 0 3]

/-- Grid lines over `[0,4] × [0,3]`. -/
def planeGrid : Array Prim :=
  ((List.range' 1 3).toArray.map fun i =>
      #[primLine (planeMap i.toFloat 0) (planeMap i.toFloat 3) overlay 0.8])
    ++ ((List.range' 1 2).toArray.map fun j =>
      #[primLine (planeMap 0 j.toFloat) (planeMap 4 j.toFloat) overlay 0.8])
    |>.flatten

/-- Grid lines over `[0,4] × [0,3]` mapped through a projection. -/
def uvGridOf (q : Float → Float → Vec2) (N M : Float) : Array Prim :=
  ((List.range' 1 3).toArray.map fun i =>
      #[primLine (q i.toFloat 0) (q i.toFloat M) overlay 0.8])
    ++ ((List.range' 1 2).toArray.map fun j =>
      #[primLine (q 0 j.toFloat) (q N j.toFloat) overlay 0.8])
    |>.flatten

/-! ## 1. height-function: a real number above every point of the plane -/

def figHeightFunction : Array Prim :=
  let sx (x : Float) := 360 + 120 * x
  let sy (z : Float) := 60 + 40 * z
  let curve : Array Vec2 :=
    (List.range 89).toArray.map fun i =>
      let x := -2.2 + i.toFloat * (4.4 / 88)
      ![sx x, sy (bowlHeight x 0)]
  -- vertical stems: the height h above each sampled point
  let stems : Array Prim :=
    (List.range 5).toArray.flatMap fun i =>
      let x := -2 + i.toFloat
      if x == 0 then #[] else #[primLine ![sx x, 60] ![sx x, sy (bowlHeight x 0)] blue 1.0]
  #[
    primLine ![sx (-2.2), 60] ![sx 2.2, 60] overlay 1.5,
    primText ![sx 2.35, 55] "the plane (x, y)" overlay 12,
    primPolyline curve teal 2.5,
    primText ![sx 0, sy 4.9] "h(x, y) = x² + y²" text 14
  ] ++ stems

/-! ## 2. parameter-plane: the domain of h -/

def figParameterPlane : Array Prim := #[
  primPolygon #[![40, 45], ![310, 45], ![310, 205], ![40, 205]] blue blue 0.15 2
] ++ ((List.range' 1 9).toArray.map fun i =>
      primLine ![40 + 30 * i.toFloat, 45] ![40 + 30 * i.toFloat, 205] overlay 0.8)
  ++ ((List.range' 1 5).toArray.map fun j =>
      primLine ![40, 45 + 30 * j.toFloat] ![310, 45 + 30 * j.toFloat] overlay 0.8)
  ++ #[
  primCircle ![175, 125] 5.5 red,
  primText ![175, 95] "p = (x, y)" text 14,
  primText ![175, 25] "the parameter plane ℝ²: every point is a pair of coordinates" subtext 13
]

/-! ## 3. heightmap-lift: UV plane → mesh graph -/

def figHeightmapLift : Array Prim :=
  -- bump used by the previous generator, kept for continuity
  let hb (x y : Float) := 1.15 * Float.exp (-(((x - 2) ^ 2) + ((y - 1.5) ^ 2)) / 1.1)
  -- oblique projections (y-up): UV plane on the left, graph on the right
  let q (x y : Float) : Vec2 := ![40 + 40 * x + 18 * y, 100 + 16 * y]
  let p (x y z : Float) : Vec2 := ![380 + 40 * x + 18 * y, 58 + 16 * y + 30 * z]
  let N : Float := 4
  let M : Float := 3
  -- mesh quads, painted back-to-front
  let mesh : Array Prim :=
    (List.range 3).toArray.flatMap fun jj =>
      let j := M - 1 - jj.toFloat
      (List.range 4).toArray.flatMap fun i =>
        let i := i.toFloat
        #[primPolygon
          #[p i (j + 1) (hb i (j + 1)), p (i + 1) (j + 1) (hb (i + 1) (j + 1)),
            p (i + 1) j (hb (i + 1) j), p i j (hb i j)] blue blue 0.14 1.1]
  #[
    primPolygon #[q 0 0, q N 0, q N M, q 0 M] blue blue 0.12 2
  ] ++ uvGridOf q N M ++ mesh ++ #[
    primLine (p 2 1.5 0) (p 2 1.5 (hb 2 1.5)) red 1.2,
    primCircle (p 2 1.5 (hb 2 1.5)) 5.5 red,
    primCircle (q 2 1.5) 5.5 red,
    primText ![150, 62] "UV / parameter plane (x, y)" subtext 13,
    primText ![150, 44] "the bullet's position lives here" overlay 11,
    primText ![520, 28] "the graph h: (x, y) ↦ (x, y, h(x,y))" subtext 13,
    primText ![520, 10] "same red point, now displaced along +z" overlay 11
  ] ++ primArrow ![268, 160] ![340, 160] subtext 2

/-! ## 4/5. Shared bowl mesh for the `tangents` / `normal` figures -/

private def bowlMesh (proj : Float → Float → Float → Vec2) : Array Prim :=
  (List.range 5).toArray.flatMap fun jj =>
    let j := 4 - jj.toFloat
    (List.range 5).toArray.flatMap fun i =>
      let x := -1.2 + i.toFloat * 0.6
      let y := -1.2 + j * 0.6
      #[primPolygon
        #[proj x y (bowlHeight x y), proj (x + 0.8) y (bowlHeight (x + 0.8) y),
          proj (x + 0.8) (y + 0.8) (bowlHeight (x + 0.8) (y + 0.8)),
          proj x (y + 0.8) (bowlHeight x (y + 0.8))] blue blue 0.14 1.0]

/-! ## 4. tangents: the derivatives of σ in the x- and y-directions -/

def figTangents : Array Prim :=
  let P : Float → Float → Float → Vec2 := fun x y z => ![400 + 55 * x + 20 * y, 190 - 20 * y - 21 * z]
  let px := 0.8
  let py := 0.6
  let fx := partialX bowlHeight px py
  let fy := partialY bowlHeight px py
  let base := P px py (bowlHeight px py)
  let tx := P (px + 0.6) py (bowlHeight px py + 0.6 * fx)
  let ty := P px (py + 0.6) (bowlHeight px py + 0.6 * fy)
  let arrows := primArrow base tx blue 3 ++ primArrow base ty green 3
  bowlMesh P ++ arrows ++ #[
    primCircle base 5 peach,
    primText (base + ![10, 18]) "p" text 13,
    primText (tx + ![-60, 16]) "∂ₓσ(p) = (1, 0, ∂ₓh)" blue 13,
    primText (ty + ![16, 0]) "∂ᵧσ(p) = (0, 1, ∂ᵧh)" green 13,
    primText ![360, 28] "the coordinate tangents span the tangent plane" subtext 13
  ]

/-! ## 5. normal: orthogonal to both tangents, by construction -/

def figNormal : Array Prim :=
  let P : Float → Float → Float → Vec2 := fun x y z => ![400 + 55 * x + 20 * y, 190 - 20 * y - 21 * z]
  let px := 0.8
  let py := 0.6
  let fx := partialX bowlHeight px py
  let fy := partialY bowlHeight px py
  let base := P px py (bowlHeight px py)
  -- normal = (-∂ₓh, -∂ᵧh, 1), scaled 0.5 for display
  let nx : Float := px - 0.5 * fx
  let ny : Float := py - 0.5 * fy
  let nrm := P nx ny (bowlHeight px py + 0.5)
  let tArr := primArrow (P (px + 0.6) py (bowlHeight px py + 0.6 * fx)) base blue 2
    ++ primArrow (P px (py + 0.6) (bowlHeight px py + 0.6 * fy)) base green 2
  let nArr := primArrow base nrm mauve 3
  bowlMesh P ++ tArr ++ nArr ++ #[
    primCircle base 5 peach,
    primText (nrm + ![14, 0]) "normal = (-∂ₓh, -∂ᵧh, 1)" mauve 13,
    primText ![360, 28] "⟪tangentX, normal⟫ = ⟪tangentY, normal⟫ = 0" subtext 13
  ]

/-! ## 6. geodesic-rule: acceleration only along the surface normal
     (the one schematic figure) -/

def figGeodesicRule : Array Prim :=
  let surf : Array Vec2 := #[![60, 220], ![360, 220], ![500, 110], ![200, 110]]
  let p0 : Vec2 := ![110, 205]
  let ctrl : Vec2 := ![260, 130]
  let p1 : Vec2 := ![430, 140]
  let curve := qbezierPts p0 ctrl p1 40
  let pt := curve[curve.size - 1]!
  let velArr := primArrow pt (pt + ![75, -20]) blue 3
  let nrmArr := primArrow pt (pt + ![22, 60]) mauve 3
  #[
    primPolygon surf teal teal 0.15 2,
    primPolyline curve red 3,
    primCircle pt 6 peach
  ] ++ velArr ++ nrmArr ++ #[
    primText (pt + ![90, -28]) "velocity v (in the surface)" blue 13,
    primText (pt + ![36, 74]) "acceleration ⟂ surface (along normal)" mauve 13,
    primText ![300, 240] "a geodesic: the 3D acceleration is purely normal" subtext 13
  ]

/-! ## 7. distorted-map: the geodesic bends in the plane
     (computed: an rk4Step trajectory on the bowl) -/

def figDistortedMap : Array Prim :=
  let s₀ : ShotState Float := ⟨(0.4, 0.4), ![1, 0.35]⟩
  let pts := (shootPositions rk4Step bowlHeight s₀ 0.05 90).map fun q =>
    planeMap q.1 q.2
  let start := pts[0]!
  let stop := pts[pts.size - 1]!
  let dash := dashedSeg start stop subtext 1.5
  #[
    primPolygon planeQuad blue blue 0.08 2
  ] ++ planeGrid ++ dash ++ #[
    primPolyline pts red 2.5,
    primCircle start 4.5 green,
    primCircle stop 4.5 red,
    primText (planeMap 0.1 3.25) "geodesic in the parameter plane (computed via rk4Step)" text 13,
    primText (planeMap 0.1 (-0.7)) "dashed: the straight chord — bending keeps the path straight on the surface" overlay 12
  ]

/-! ## 8. euler-drift: Euler vs RK4 on the bowl (computed) -/

def figEulerDrift : Array Prim :=
  let s₀ : ShotState Float := ⟨(0.4, 0.4), ![1, 0.35]⟩
  let rk4 := (shootPositions rk4Step bowlHeight s₀ 0.05 60).map fun q =>
    planeMap q.1 q.2
  let euler := (shootPositions eulerStep bowlHeight s₀ 0.25 60).map fun q =>
    planeMap q.1 q.2
  #[
    primPolygon planeQuad blue blue 0.08 1.5,
    primPolyline rk4 green 2.5,
    primPolyline euler red 2,
    primCircle (planeMap 0.4 0.4) 4.5 text,
    primText (planeMap 0.15 3.25) "eulerStep (dt = 0.25) drifts off the geodesic" red 13,
    primText (planeMap 0.15 (-0.7)) "rk4Step (dt = 0.05) hugs the true geodesic" green 13
  ]

/-! ## 9. rk4-slopes: the four slope probes, weighted 1:2:2:1 (computed) -/

def figRk4Slopes : Array Prim :=
  let s₀ : ShotState Float := ⟨(0.4, 0.4), ![1, 0.35]⟩
  let s₁ := rk4Step bowlHeight s₀ 0.25
  let s₂ := rk4Step bowlHeight s₁ 0.25
  let s₃ := rk4Step bowlHeight s₂ 0.25
  let s₄ := rk4Step bowlHeight s₃ 0.25
  let pos (s : ShotState Float) := planeMap s.pos.1 s.pos.2
  let path := (shootPositions rk4Step bowlHeight s₀ 0.25 4).map fun q =>
    planeMap q.1 q.2
  -- direction probes k₁ … k₄ (velocity part of each field evaluation)
  let kvec (s : ShotState Float) : Vec2 := ![s.vel 0, s.vel 1]
  let probe (s : ShotState Float) (hex : String) (w : Float) : Array Prim :=
    primArrow (pos s) (pos s + 30.0 • normalize (kvec s)) hex w
  let a₁ := probe s₀ yellow 2
  let a₂ := probe s₁ green 3.5
  let a₃ := probe s₂ teal 3.5
  let a₄ := probe s₃ blue 2
  #[
    primPolyline path teal 2.5,
    primCircle (pos s₀) 4.5 peach
  ] ++ a₁ ++ a₂ ++ a₃ ++ a₄ ++ #[
    primText (pos s₀ + ![-20, 30]) "k₁ (×1)" yellow 13,
    primText (pos s₁ + ![-20, 30]) "k₂ (×2)" green 13,
    primText (pos s₂ + ![-20, 30]) "k₃ (×2)" teal 13,
    primText (pos s₃ + ![-20, -25]) "k₄ (×1)" blue 13,
    primText ![370, 28] "one rk4Step: slope probes averaged 1:2:2:1" subtext 13,
    primCircle (pos s₄) 4.5 red
  ]

end Brane.Figures
