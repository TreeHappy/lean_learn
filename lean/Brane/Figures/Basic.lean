/-
Figures/Basic.lean: shared style and drawing helpers for the figure
generator (`Brane.Figures.Gen`, run with `lake exe gen-figures`).

Everything here is built on Vizagrams' `Prim` layer: a `Prim` is a geometric
shape (`Geom`) plus a `Style` (`fillColor`, `strokeColor`, `strokeWidth`).
We deliberately stay below Vizagrams' free-monad mark layer and work with
plain `Array Prim` — the figures are static diagrams, and the array is
exactly what `Brane.Figures.Gen` serializes to SVG.

Coordinate convention: figures are authored in *mathematical* coordinates
(y grows upwards). The serializer in `Gen.lean` flips the y-axis into SVG
screen coordinates. The palette is Catppuccin Mocha, matching the previous
`gen-figures.mjs` generator.
-/

import Vizagrams

namespace Brane.Figures

open GeometricPrimitive GraphicalPrimitive Sty LinearAlgebra

/-! ## Catppuccin Mocha palette -/

/-- Background of the figures (Catppuccin Latte `base`). -/
def baseHex : String := "#eff1f5"

/-- Parse one hex digit. -/
def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Parse a two-character hex byte like `"3f"` into a 0–255 float
(ProofWidgets SVG colors store channels on a 0–255 scale). -/
def byteOf (cs : List Char) : Float :=
  match cs with
  | [a, b] => ((16 * hexVal a + hexVal b : Nat)).toFloat
  | _ => 0

/-- `rgb "#89b4fa"` — hex color string to a ProofWidgets SVG color. -/
def rgb (hex : String) : ProofWidgets.Svg.Color :=
  let h := hex.toList
  { r := byteOf (h.drop 1 |>.take 2)
    g := byteOf (h.drop 3 |>.take 2)
    b := byteOf (h.drop 5 |>.take 2) }

/-- Linear blend of two colors; `t = 0` gives `a`, `t = 1` gives `b`. -/
def blend (a b : ProofWidgets.Svg.Color) (t : Float) : ProofWidgets.Svg.Color :=
  let f (x y : Float) := x + t * (y - x)
  { r := f a.r b.r, g := f a.g b.g, b := f a.b b.b }

/-- Simulate `fill-opacity` over the figure background: pre-blend the fill
color towards `baseHex` (Vizagrams' `Style` has no opacity attribute). -/
def faded (hex : String) (t : Float) : ProofWidgets.Svg.Color :=
  blend (rgb baseHex) (rgb hex) t

/-! ## Style shorthands -/

/-- Stroke style with a pixel width. -/
def strokeSty (hex : String) (w : Float) : Style where
  stroke_color := some (rgb hex)
  stroke_width := some (StyleSize.px w.round.toUInt32.toNat)

/-- Fill style (solid). -/
def fillSty (hex : String) : Style where
  fill_color := some (rgb hex)

/-- Fill style with simulated opacity over the background. -/
def fillFadeSty (hex : String) (t : Float) : Style where
  fill_color := some (faded hex t)

/-! ## Primitive shorthands -/

/-- A stroked line segment. -/
def primLine (a b : Vec2) (hex : String) (w : Float) : Prim :=
  ⟨Geom.line a b, strokeSty hex w⟩

/-- A filled-and-stroked polygon. -/
def primPolygon (pts : Array Vec2) (fillHex strokeHex : String)
    (op w : Float) : Prim :=
  ⟨Geom.polygon pts,
    fillFadeSty fillHex op ++ strokeSty strokeHex w⟩

/-- A stroked polyline (open path through the given points). -/
def primPolyline (pts : Array Vec2) (hex : String) (w : Float) : Prim :=
  ⟨Geom.polyline pts, strokeSty hex w⟩

/-- A filled circle. -/
def primCircle (c : Vec2) (r : Float) (hex : String) : Prim :=
  ⟨Geom.circle r c, fillSty hex⟩

/-- A text label. The serializer renders all text centered on `pos`. -/
def primText (pos : Vec2) (s : String) (hex : String) (size : Float) : Prim :=
  ⟨Geom.text pos s size, fillSty hex⟩

/-- An arrow from `a` to `b`: shaft plus a triangular head. -/
def primArrow (a b : Vec2) (hex : String) (w : Float) : Array Prim :=
  let u := LinearAlgebra.normalize (b - a)
  let n := ![-u 1, u 0]
  let hl := 3 * w + 3   -- head length
  let hw := 1.5 * w + 2 -- half head width
  let tip := b
  let b1 := b - hl • u + hw • n
  let b2 := b - hl • u - hw • n
  #[Prim.line a (b - hl • u) (strokeSty hex w),
    ⟨Geom.polygon #[tip, b1, b2], fillSty hex⟩]

/-! ## 3D → 2D projection -/

/-- Oblique (cavalier) projection of a 3D point `(x, y, z)` anchored at an
origin offset `(x₀, y₀)` — the same projection the previous generator used:
x and y become slanted plane coordinates, z lifts vertically. -/
def projAt (x₀ y₀ : Float) (x y z : Float) : Vec2 :=
  ![x₀ + 40 * x + 18 * y, y₀ - 16 * y - 30 * z]

end Brane.Figures
