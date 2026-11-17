/-
Figures/Gen.lean: SVG serialization and the `gen-figures` executable.

Vizagrams renders to ProofWidgets HTML for the infoview; for file output we
serialize Vizagrams' `Array Prim` (its `Geom` + `Style` model) directly to
standalone SVG. This keeps the output deterministic and dependency-free at
runtime.

Run from the `lean/` directory (e.g. via `make figures`):

    lake exe gen-figures

writes `docs/figures/*.svg`, the figures referenced by
`docs/shooting-method.md`.
-/

import Brane.Figures.ShootingFigures
import Brane.Figures.Basic

namespace Brane.Figures.Gen

open GeometricPrimitive GraphicalPrimitive Sty LinearAlgebra

/-! ## Serialization -/

/-- Format a float compactly (no trailing `.0`-noise beyond one decimal,
no `NaN`). -/
def fmt (x : Float) : String :=
  if x.isNaN || x.isInf then "0"
  else let s := x.toString
       if s.endsWith ".000000" then (s.dropEnd 7).toString else s

/-- Escape the handful of characters that must not appear raw in SVG text. -/
def esc (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

/-- The color of an optional style slot, or `none` for "unset". -/
def colorAttr (name : String) (c : Option ProofWidgets.Svg.Color) : String :=
  match c with
  | none => ""
  | some col =>
    let h (x : Float) := toString (x.round.toUInt32.toNat)
    s!" {name}=\"rgb({h col.r},{h col.g},{h col.b})\""

/-- Stroke width attribute. -/
def widthAttr (w : Option StyleSize) : String :=
  match w with
  | none => ""
  | some (.px n) => s!" stroke-width=\"{n}\""
  | some (.abs f) => s!" stroke-width=\"{fmt f}\""

/-- Serialize a Vizagrams `Geom` to an SVG element string in a canvas of
height `H`. Vizagrams coordinates are y-up; SVG is y-down, so `y ↦ H - y`.
Béziers and arcs are not needed by the figures and are skipped. -/
def geomToSvg (H : Float) (g : Geom) : String :=
  let Y (y : Float) := fmt (H - y)
  let pt (v : Vec2) := s!"{fmt (v 0)},{Y (v 1)}"
  let pts (vs : Array Vec2) := (vs.map pt).toList |> String.intercalate " "
  match g with
  | .line a b => s!"<line x1=\"{fmt (a 0)}\" y1=\"{Y (a 1)}\" x2=\"{fmt (b 0)}\" y2=\"{Y (b 1)}\"/>\n"
  | .polyline vs => s!"<polyline points=\"{pts vs}\" fill=\"none\"/>\n"
  | .polygon vs => s!"<polygon points=\"{pts vs}\"/>\n"
  | .circle r c => s!"<circle cx=\"{fmt (c 0)}\" cy=\"{Y (c 1)}\" r=\"{fmt r}\"/>\n"
  | .ellipse rx ry c =>
      s!"<ellipse cx=\"{fmt (c 0)}\" cy=\"{Y (c 1)}\" rx=\"{fmt rx}\" ry=\"{fmt ry}\"/>\n"
  | .rect corner w h =>
      s!"<rect x=\"{fmt (corner 0)}\" y=\"{Y (corner 1 + h)}\" width=\"{fmt w}\" height=\"{fmt h}\"/>\n"
  | .path d => s!"<path d=\"{esc d}\" fill=\"none\"/>\n"
  | .text pos content size =>
      s!"<text x=\"{fmt (pos 0)}\" y=\"{Y (pos 1)}\" font-size=\"{fmt size}\" text-anchor=\"middle\">{esc content}</text>\n"
  | .arc .. | .qbezier .. | .cbezier .. => ""  -- unused by the figures

/-- Serialize one primitive with its style. -/
def primToSvg (H : Float) (p : Prim) : String :=
  let attrs := colorAttr "fill" p.style.fill_color
      ++ colorAttr "stroke" p.style.stroke_color
      ++ widthAttr p.style.stroke_width
  (geomToSvg H p.geom).replace "/>" s!"{attrs}/>"

/-- A complete figure: canvas size plus its primitives. -/
structure Fig where
  /-- File name inside `docs/figures/`. -/
  name : String
  /-- Canvas width in px. -/
  width : Float
  /-- Canvas height in px. -/
  height : Float
  /-- The drawing, in y-up coordinates. -/
  prims : Array Prim

/-- Serialize a whole figure to a standalone SVG document. -/
def figToSvg (f : Fig) : String :=
  let header :=
    s!"<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 {fmt f.width} {fmt f.height}\" " ++
    "font-family=\"sans-serif\">\n"
  let bg := s!"<rect x=\"0\" y=\"0\" width=\"{fmt f.width}\" height=\"{fmt f.height}\" fill=\"{baseHex}\"/>\n"
  header ++ bg ++ (f.prims.map (primToSvg f.height) |>.toList |> String.intercalate "") ++ "</svg>\n"

/-! ## The figure list (matches the image references in
     docs/shooting-method.md) -/

def figures : Array Fig := #[
  { name := "height-function.svg",  width := 720, height := 290, prims := figHeightFunction },
  { name := "parameter-plane.svg",  width := 420, height := 250, prims := figParameterPlane },
  { name := "heightmap-lift.svg",   width := 720, height := 290, prims := figHeightmapLift },
  { name := "tangents.svg",         width := 720, height := 290, prims := figTangents },
  { name := "normal.svg",           width := 720, height := 290, prims := figNormal },
  { name := "geodesic-rule.svg",    width := 560, height := 270, prims := figGeodesicRule },
  { name := "distorted-map.svg",    width := 720, height := 290, prims := figDistortedMap },
  { name := "euler-drift.svg",      width := 720, height := 290, prims := figEulerDrift },
  { name := "rk4-slopes.svg",       width := 720, height := 260, prims := figRk4Slopes }
]

end Brane.Figures.Gen

/-- Write all figures into `docs/figures/` (relative to the working
directory; run from `lean/`, e.g. `lake exe gen-figures`).
NOTE: must be a *top-level* `def main` — Lake only links an executable
when the root module defines `main` outside any namespace. -/
def main : IO Unit := do
  let dir := "../docs/figures"
  for f in Brane.Figures.Gen.figures do
    let path := s!"{dir}/{f.name}"
    IO.FS.writeFile path (Brane.Figures.Gen.figToSvg f)
    IO.println s!"wrote {path}"
