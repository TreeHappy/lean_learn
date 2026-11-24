/-
Figures/Widget.lean: reusable pieces for showing the document's Vizagrams
figures as ProofWidgets SVG widgets in the Lean infoview.

`Brane.Figures.Gen.figures` is the single source of truth: `lake exe
gen-figures` serializes those same `Fig` values to `docs/figures/*.svg`, and
this module renders them live through `VizBackend.draw_svg` for editing.
-/
import Brane.Figures.Basic
import Brane.Figures.Gen
import Vizagrams

namespace Brane.Figures.Widget

open ProofWidgets
open VizBackend
open GeometricPrimitive GraphicalPrimitive Sty LinearAlgebra

open scoped ProofWidgets.Jsx

/-- `Brane.Figures.rgb` produces 0–255 channels for the standalone SVG
serializer, while `ProofWidgets.Svg.Color` expects 0–1 for `#html`. -/
private def pwColor (c : ProofWidgets.Svg.Color) : ProofWidgets.Svg.Color :=
  { r := c.r / 255, g := c.g / 255, b := c.b / 255 }

/-- Rescale a primitive's colors for infoview rendering. -/
def forInfoview (p : Prim) : Prim :=
  { p with style :=
      { p.style with
        fill_color := p.style.fill_color.map pwColor
        stroke_color := p.style.stroke_color.map pwColor } }

/-- A y-up frame for a `Gen.Fig`. `scale = 2` draws at half size so a
720-pixel-wide document figure fits comfortably in the infoview. -/
def frameOf (f : Gen.Fig) (scale : Nat := 2) : ProofWidgets.Svg.Frame where
  xmin := 0
  ymin := 0
  xSize := f.width
  width := (f.width.toUInt64.toNat / scale).max 1
  height := (f.height.toUInt64.toNat / scale).max 1

/-- Render one document figure as labelled HTML, ready for `#html`. -/
def figToHtml (f : Gen.Fig) (scale : Nat := 2) : ProofWidgets.Html :=
  <div>
    <b>{Html.text f.name}</b>
    <br/>
    {draw_svg (f.prims.map forInfoview) (frameOf f scale)}
  </div>

/-- Every figure used by `docs/shooting-method.md`, stacked in one widget. -/
def allFiguresHtml (scale : Nat := 2) : ProofWidgets.Html :=
  Html.element "div" #[] (Gen.figures.map (figToHtml · scale))

end Brane.Figures.Widget
