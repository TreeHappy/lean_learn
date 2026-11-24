# Parameterized chart mapping around a point

> [!NOTE]
> Idea note. This sketches a connection between 2D texture/chart
> parameterization in graphics and normal-coordinate charts on a Riemannian
> manifold. It is not yet formalized in Lean.

## Motivation

The project already treats a graph surface as a map from a 2D parameter plane
into `ℝ³`:

```text
graph h (x, y) = (x, y, h x y)
```

That is a global chart in the usual graph-surface setting: the parameter
domain is `Point2 = ℝ × ℝ`, and `h` lifts it to the manifold. The question
behind this note is the local inverse-facing version:

> Given a point `p` on a Riemannian manifold `M`, how do we build a useful 2D
> parameterized chart around `p`?

The answer should be geometric, not just coordinate bookkeeping. The chart
should say where a tangent direction goes, how distances and angles distort,
and how a 2D patch of "texture coordinates" sits on the curved surface.

## Texture-mapping analogy

In 2D texture mapping, a surface patch is parameterized by coordinates
`(u, v)` in a flat domain. A texture lookup evaluates a function

```text
T : U ⊂ ℝ² → Color
```

while the surface embedding evaluates

```text
φ : U ⊂ ℝ² → M ⊂ ℝ³.
```

The useful graphics questions map directly to differential geometry:

| Texture mapping | Riemannian chart |
| --- | --- |
| UV domain `U ⊂ ℝ²` | coordinate domain around `p` |
| chart / parameterization `φ(u,v)` | local chart or normal chart |
| tangent vectors `∂φ/∂u`, `∂φ/∂v` | coordinate basis of `T_pM` pushed along the chart |
| Jacobian / first fundamental form | metric pullback `φ* g`, area and angle distortion |
| texel footprint / anisotropy | eigenvalues of the metric in chart coordinates |
| seam / singular parameterization | chart boundary, cut locus, or non-injective exponential map |

The texture-mapping viewpoint suggests treating the chart as data we can sample,
differentiate, and measure for distortion. The Riemannian viewpoint supplies the
canonical construction around a point.

## Normal coordinates via the exponential map

For a Riemannian manifold `(M, g)` and point `p ∈ M`, the exponential map sends
a tangent vector to the endpoint of a geodesic:

```text
exp_p : V ⊂ T_pM → M
exp_p(v) = γ_v(1),
```

where `γ_v` is the geodesic with `γ_v(0) = p` and `γ_v'(0) = v`.

If we choose an orthonormal basis `(e₁, e₂)` of `T_pM`, then every tangent
vector can be written as

```text
v = u e₁ + v' e₂,   (u, v') ∈ ℝ²,
```

and the normal chart is

```text
Φ_p(u, v') = exp_p(u e₁ + v' e₂).
```

This is a 2D parameterized mapping around `p`: the flat UV-like domain is a disk
in `ℝ²`, and the image is a geodesic patch on the manifold.

Important properties:

* `Φ_p(0,0) = p`.
* Straight lines through the origin in parameter space map to geodesics through
  `p`.
* The metric at the origin is Euclidean in normal coordinates, so first-order
  length and angle distortion vanishes at `p`.
* The chart is generally valid only up to the injectivity radius / cut locus;
  beyond that, `exp_p` can stop being a good parameterization, much like a UV
  map can fold or overlap.

## Distortion as a "texture quality" metric

Texture mapping cares about how much a flat texel is stretched on the surface.
The same quantity is measured by the pullback metric. For a chart
`Φ : U → M`, let

```text
G_{ij}(u,v) = g(DΦ_u e_i, DΦ_u e_j).
```

Then:

* `det(G)` controls local area scaling.
* The singular values / eigenvalues of `G` control anisotropic stretch.
* Conformal distortion measures angle error; isometric distortion measures
  length error.
* In normal coordinates, `G_{ij}(0) = δ_{ij}` and the first derivatives of the
  metric vanish at the origin; curvature appears in higher-order distortion.

This gives a concrete bridge: a "good" local texture patch around a point is a
chart with controlled metric distortion, and the exponential map is the
canonical curvature-aware starting point.

## Connection to brane

The existing graph-surface code already provides most of the ingredients for a
prototype on `M = graph h`:

* **Point and tangent frame.** `Brane.DiffGeom` defines `graph`, `tangentX`,
  `tangentY`, `normal`, and `gramMatrix`. An orthonormal tangent basis at `p`
  can be obtained from the tangent frame.
* **Geodesics.** `Brane.Shooting` and `Brane.ParallelTransport` evolve geodesics
  in parameter space. The shooting method is the computational form of
  `exp_p`: choose an initial velocity and integrate for unit time. Eberly's
  *Riemannian Geodesics* notes are a useful computational reference for this
  view: they derive the geodesic ODE from the metric/Christoffel symbols and
  treat geodesic tracing as numerical evolution of that ODE, which is the same
  bridge needed for an exponential-map chart.
* **Parallel transport.** Transporting a tangent basis along geodesics gives a
  moving frame, related to Fermi/parallel normal coordinates.
* **Distortion.** `gramMatrix h` is already the first fundamental form in the
  graph parameterization. For a normal chart `Φ_p`, the pullback metric can be
  sampled numerically by finite differences of `Φ_p`.

A small prototype could pick a point `(x₀, y₀)`, build an orthonormal basis in
`T_p(graph h)`, shoot geodesics for a grid of tangent vectors
`(u, v') ∈ [-r, r]²`, and render the resulting patch. Coloring the patch by
`det(G)` or stretch eigenvalues would visualize chart distortion exactly like a
texture-mapping debug view.

## Possible Lean formalization path

1. **Abstract exponential map interface.** State the minimal data needed:
   tangent vectors, geodesic flow, and `exp_p(v) = γ_v(1)`.
2. **Graph-surface specialization.** Use existing geodesic ODE/shooting
   definitions to define a computational exponential map on `graph h`.
3. **Normal chart.** Package an orthonormal basis of `T_pM` and define
   `Φ_p(u,v')`.
4. **Metric pullback.** Prove or numerically evaluate `G = DΦᵀ DΦ` / `φ* g`.
5. **Distortion lemmas.** Show `G(0)=I` in normal coordinates and relate
   higher-order terms to curvature.

## Map-projection families as local chart choices

[Map projections](https://en.wikipedia.org/wiki/List_of_map_projections) are
conventions for mapping a curved surface to a flat parameter domain. Most are
formulated for the sphere/Earth, but their distortion properties are exactly the
properties we care about when choosing a local chart `Φ_p : U ⊂ ℝ² → M` around
a point.

The cartographic convention is usually "surface to plane"; the exponential-map
view is often "plane/tangent to surface". For chart design it is useful to keep
both directions in mind:

```text
parameter domain U ⊂ ℝ²  <->  local patch Φ_p(U) ⊂ M
          coordinates                manifold point
          texture UV                 surface location
```

### Azimuthal projections around a center

Azimuthal projections are the closest cartographic analogue of a point-centered
Riemannian chart. They place a chosen center `p` at the origin of the plane and
assign directions around `p` to angles in the parameter domain.

| Map projection | Preserved property | Riemannian / chart analogue | Notes for `Φ_p` |
| --- | --- | --- | --- |
| Azimuthal equidistant | distances from center along radials | geodesic polar / normal coordinates | `exp_p` preserves radial geodesic distance: `d(p, exp_p(v)) = |v|` before cut locus. The natural "measure from p" chart. |
| Gnomonic | geodesics as straight lines (sphere) | normal coordinates, radial geodesics | In normal coordinates, geodesics through `p` are straight parameter lines. On general manifolds this does not make all geodesics straight; constant curvature is special. |
| Stereographic | angles / conformal | conformal normal coordinates / isothermal local chart | Preserves local shape but not area. Useful when texture/debugging should keep angles faithful near `p`. |
| Lambert azimuthal equal-area | area | equal-area local parameterization | Preserves `det(G)` in the idealized target sense; useful when sampling density or physical area matters. |
| Orthographic | perspective view | tangent-plane projection / graph projection | Projects along a normal/eye direction. For an embedded surface this is close to "lift the tangent plane" or to the graph chart after local linearization. |
| Vertical perspective | finite-distance perspective | camera/pin-hole projection of a patch | Relevant to rendering: a visible patch is parameterized by view rays, not intrinsic geodesic distance. |

The azimuthal family suggests making the chart choice explicit as

```text
Φ_p(r, θ) = E_p(ρ(r) e_θ),   or   Φ_p(u,v) = E_p(σ(u,v)),
```

where `E_p` is the exponential/geodesic map, `e_θ` is a direction in `T_pM`,
and `ρ`/`σ` selects the radial metric: identity for equidistant, tangent for
gnomonic-like, sine/stereographic scalings for area/conformal variants on
spheres. On a general Riemannian manifold, the same radial rescalings can be
used as chart reparameterizations, but their global cartographic invariants may
only hold approximately away from `p`.

### Cylindrical, conic, and strip charts

Cylindrical and conic projections are less "around a point" and more "around an
axis or along a strip". They become relevant when the local patch is organized
around a curve, direction field, or boundary rather than a single center.

| Projection family | Cartographic idea | Chart analogue |
| --- | --- | --- |
| Cylindrical (Mercator, Lambert cylindrical equal-area, equirectangular) | unwrap around an axis; meridians/parallels form a grid | coordinates along a geodesic/flow and a transverse coordinate; Fermi or tube-like charts |
| Conic (Lambert conformal conic, Albers equal-area) | unwrap over a cone tangent/secant to a latitude band | charts adapted to a ring/band around a point or curve, with one or two low-distortion parallels |
| Pseudocylindrical (sinusoidal, Mollweide, Robinson, Equal Earth) | compromise global shapes with curved meridians | nonlinear parameter remappings that trade area, angle, and distance distortion over a larger patch |

For brane, a Fermi coordinate chart along a geodesic is the natural "cylindrical"
counterpart: one coordinate is arc length along the curve, the other is a normal
offset transported along it.

### Distortion properties as chart objectives

The projection classification by property translates directly into chart
selection criteria:

| Property | Map-projection term | Chart metric condition | Use when |
| --- | --- | --- | --- |
| Conformal | conformal / orthomorphic | `G(u,v) = λ(u,v) I` | preserving angles, local shape, or grid orthogonality matters |
| Equal-area | equal-area / authalic | `det(G(u,v)) = const` | sampling density, mass, or texture texel area should be uniform |
| Equidistant | equidistant | distances preserved along selected lines | radial distance from `p`, or distances along a curve/grid family, matter |
| Compromise | compromise | no single invariant; minimize combined distortion | visualization or texture mapping over a larger patch |

No single chart on a curved manifold can be simultaneously isometric everywhere.
The map-projection analogy makes this a design choice rather than a failure:
pick the invariant that the downstream computation needs.

### Polyhedral/globular charts and atlases

Polyhedral projections (e.g. Cahill butterfly, Lee conformal tetrahedron) and
quincuncial/tiled conformal maps suggest an atlas view: cover a manifold with
several low-distortion charts rather than forcing one chart to cover a large
region. This connects to texture atlases and to the cut locus/injectivity limit
of normal coordinates.

```text
atlas = { (U_i, Φ_i) }  with small distortion per chart
seams/cut boundaries    <-> chart transitions / overlap maps
```

## Open questions

* Should the primary object be a chart into parameter space `(x,y)` or directly
  into the embedded surface `graph h (x,y)`?
* For graph surfaces, how does the graph chart `(x,y)` compare to the normal
  chart around `p` as a texture parameterization?
* What is the right Lean representation of `T_pM`: a subtype of `ℝ³` tangent to
  the graph, or the parameter-plane velocity space pushed forward by `d(graph h)`?
* How should cut locus / injectivity radius be represented in a computational
  prototype?
* Can the existing `ParallelTransport` code produce a stable frame for Fermi
  coordinates along a curve, not just around a point?
* Which projection invariants survive as exact properties on general Riemannian
  manifolds, and which are only sphere/constant-curvature analogues?
* Can we define a "projection family" API: a radial/profile function composed
  with `exp_p`, with distortion measured by the pullback metric?

## References

* Manfredo do Carmo, *Riemannian Geometry*, chapters on geodesics, exponential
  map, and normal coordinates.
* John M. Lee, *Introduction to Riemannian Manifolds*, normal coordinates and
  metric expansion.
* Texture mapping / parameterization surveys for the graphics-side vocabulary:
  UV charts, Jacobians, conformal and isometric distortion.
* David Eberly, [Riemannian Geodesics](https://www.geometrictools.com/Documentation/RiemannianGeodesics.pdf),
  Geometric Tools Documentation — computational treatment of Riemannian metrics,
  Christoffel symbols, geodesic equations, and geodesic evolution; useful
  background for implementing `exp_p` by shooting.
* Wikipedia, [List of map projections](https://en.wikipedia.org/wiki/List_of_map_projections)
  — catalog of projection families and distortion properties used as chart
  analogies.