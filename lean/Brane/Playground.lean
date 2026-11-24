import Brane.Basic
import Brane.Figures.Basic
import Brane.Figures.Gen
import Brane.Figures.Widget
import Vizagrams

open VizBackend Brane.Figures Brane.Figures.Widget
open GeometricPrimitive GraphicalPrimitive Sty LinearAlgebra

/-!
# Playground

Scratch space for experiments. Nothing here is imported by `Brane.lean`, so
feel free to add `sorry` or delete everything.

The `#html` commands draw a vector diagram and every figure used by
`docs/shooting-method.md` in the infoview; the `#eval` below also writes the
vector diagram to `docs/figures/playground-vectors.svg`.
-/

#check Brane.hello
#check Brane.double

example : Brane.double 3 = 6 := by
  decide

/-! ## Drawing vectors with a ProofWidgets SVG widget

`Brane.Figures.primArrow`/`primCircle`/… build Vizagrams `Prim`s, and
`VizBackend.draw_svg` turns them into an SVG element inside `#html`.
The color-scale fix lives in `Brane.Figures.Widget.forInfoview` so the same
helper can render the document figures below.
-/

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

#html draw_svg (vecDemo.map forInfoview) vizFrame

/-! ## The same diagram as a standalone SVG file

`Brane.Figures.Gen.figToSvg` serializes `Array Prim` directly and keeps the
0–255 hex colors, which is what standalone SVG wants — no `forInfoview` here.
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

/-! ## Every figure from `docs/shooting-method.md` as a widget

`Brane.Figures.Gen.figures` is the array serialized by `lake exe gen-figures`
into `docs/figures/*.svg`. Each `#html` below wraps one entry with
`Brane.Figures.Widget.figToHtml`, so moving the cursor between these commands
in the infoview shows the very figure the markdown references. The default
`scale := 2` keeps the wide figures inside a narrow infoview; pass `scale := 1`
to `figToHtml` for full size.
-/

#html figToHtml (Brane.Figures.Gen.figures[0])
#html figToHtml (Brane.Figures.Gen.figures[1])
#html figToHtml (Brane.Figures.Gen.figures[2])
#html figToHtml (Brane.Figures.Gen.figures[3])
#html figToHtml (Brane.Figures.Gen.figures[4])
#html figToHtml (Brane.Figures.Gen.figures[5])
#html figToHtml (Brane.Figures.Gen.figures[6])
#html figToHtml (Brane.Figures.Gen.figures[7])
#html figToHtml (Brane.Figures.Gen.figures[8])
