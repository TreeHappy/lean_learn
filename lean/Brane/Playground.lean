import Brane.Basic
import Brane.Figures.Basic
import Brane.Figures.Gen
import Vizagrams

open VizBackend Brane.Figures
open GeometricPrimitive GraphicalPrimitive Sty LinearAlgebra

/-!
# Playground

Scratch space for experiments. Nothing here is imported by `Brane.lean`, so
feel free to add `sorry` or delete everything.

The `#html` draws a little vector diagram in the infoview; the `#eval` below
also writes the same diagram to `docs/figures/playground-vectors.svg`.
-/

#check Brane.hello
#check Brane.double

example : Brane.double 3 = 6 := by
  decide

/-! ## Drawing vectors with a ProofWidgets SVG widget

`Brane.Figures.primArrow`/`primCircle`/… build Vizagrams `Prim`s, and
`VizBackend.draw_svg` turns them into an SVG element inside `#html`.
The one wrinkle is color scale: `Brane.Figures.rgb` parses hex into 0–255
channels for `Gen.lean`'s standalone SVG files, but `ProofWidgets.Svg.Color`
expects 0–1, so `fixColors` rescales before rendering in the infoview.
-/

private def pwColor (c : ProofWidgets.Svg.Color) : ProofWidgets.Svg.Color :=
  { r := c.r / 255, g := c.g / 255, b := c.b / 255 }

private def fixColors (p : Prim) : Prim :=
  { p with style :=
      { p.style with
        fill_color := p.style.fill_color.map pwColor
        stroke_color := p.style.stroke_color.map pwColor } }

/-- 1 Vizagrams unit = 1 px, y up; `Point.abs` handles the SVG y-flip. -/
private def vizFrame : ProofWidgets.Svg.Frame where
  xmin := 0
  ymin := 0
  xSize := 400
  width := 400
  height := 400

private def vecDemo : Array Prim :=
  let pt : Float → Float → Float → Vec2 := projAt 220 210
  let o  := pt 0 0 0
  let ex := pt 1 0 0
  let ey := pt 0 1 0
  let ez := pt 0 0 1
  let n  := pt 0.5 0.5 1
  #[primLine (pt (-1.3) 0 0) (pt 1.5 0 0) "#7f849c" 1,
    primLine (pt 0 (-1.3) 0) (pt 0 1.5 0) "#7f849c" 1,
    primText (pt (-1.15) 0 0) "u" "#a6adc8" 14,
    primText (pt 0 (-1.15) 0) "v" "#a6adc8" 14,
    primCircle o 4 "#cdd6f4"]
    ++ primArrow o ex "#a6e3a1" 2
    ++ primArrow o ey "#89b4fa" 2
    ++ primArrow o ez "#cba6f7" 2
    ++ primArrow o n "#fab387" 2
    ++ #[primText (pt 1.05 0 0) "∂x" "#a6e3a1" 14,
         primText (pt 0.05 0.95 0) "∂y" "#89b4fa" 14,
         primText (pt 0 0 0.95) "n" "#cba6f7" 14]

#html draw_svg (vecDemo.map fixColors) vizFrame

/-! ## The same diagram as a standalone SVG file

`Brane.Figures.Gen.figToSvg` serializes `Array Prim` directly and keeps the
0–255 hex colors, which is what standalone SVG wants — no `fixColors` here.
Run this module from `lean/` (`lake env lean Brane/Playground.lean`) to write
`../docs/figures/playground-vectors.svg`.
-/

private def vecFig : Brane.Figures.Gen.Fig :=
  { name := "playground-vectors.svg"
    width := 400
    height := 400
    prims := vecDemo }

#eval do
  let path := "../docs/figures/" ++ vecFig.name
  IO.FS.writeFile path (Brane.Figures.Gen.figToSvg vecFig)
  IO.println s!"wrote {path}"
