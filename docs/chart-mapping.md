# Parameterized Charts Around a Point

A chart is to a Riemannian manifold what a UV map is to a textured triangle: a
way to label a curved patch with flat coordinates, plus a way to measure how
badly the labelling stretches and shears. This note builds that dictionary for
the graph surfaces of [`shooting-method.md`](shooting-method.md), and turns it
into the Lean definitions of `lean/Brane/ChartMap.lean` (namespace
`Brane.ChartMap`).

The ideas here are now formalized computationally: charts, pullback metrics,
distortion predicates, azimuthal profiles, and a shooting-based exponential map
are all real declarations. The analytic bridges — for example, that the
computational normal chart fixes its base point — are left as `sorry`. The only
background you need is: partial derivatives, matrix multiplication, and the
idea of a UV coordinate.

> [!NOTE]
> **The question.** Given a point $p$ on a Riemannian manifold $M$, how do we
> build a useful 2D parameterized chart around $p$?
>
> The answer should be geometric, not just coordinate bookkeeping. The chart
> should say where a tangent direction goes, how distances and angles
> distort, and how a 2D patch of "texture coordinates" sits on the curved
> surface.

The companions are [`connections.md`](connections.md) for the covariant
derivative and [`lie-algebra.md`](lie-algebra.md) for the algebraic layer.

---

## 1. The surface is already a chart

The project already treats a graph surface as a map from a 2D parameter plane
into $\mathbb{R}^3$:

```lean
def graph (h : HeightFun) (p : Point2) : Point3 :=
  vec3 p.1 p.2 (h p.1 p.2)
```

That is a global chart in the usual graph-surface setting: the parameter
domain is `Point2` $= \mathbb{R} \times \mathbb{R}$, and $h$ lifts it to the
manifold. In the notation of the shooting note,

```math
\sigma := \mathrm{graph}\thinspace h, \qquad
\sigma(x,y) = (x, y, h(x,y)).
```

> [!IMPORTANT]
> **The local, inverse-facing question.** The graph chart goes *parameter
> plane → surface*. The interesting chart question goes the other way: given
> $p \in M$, produce a flat domain $U \subset \mathbb{R}^2$ and a map
> $\Phi : U \to M$ whose image is a small patch around $p$. This is the chart
> a texture map, a local simulation, or a numerical scheme would actually use.

---

## 2. Texture mapping ↔ Riemannian charts

In 2D texture mapping, a surface patch is parameterized by coordinates
$(u,v)$ in a flat domain. A texture lookup evaluates a function

```math
T : U \subset \mathbb{R}^2 \to \mathrm{Color}
```

while the surface embedding evaluates

```math
\varphi : U \subset \mathbb{R}^2 \to M \subset \mathbb{R}^3.
```

The useful graphics questions map directly to differential geometry:

| Texture mapping | Riemannian chart |
| --- | --- |
| UV domain $U \subset \mathbb{R}^2$ | coordinate domain around $p$ |
| chart / parameterization $\varphi(u,v)$ | local chart or normal chart |
| tangent vectors $\partial\varphi/\partial u$, $\partial\varphi/\partial v$ | coordinate basis of $T_pM$ pushed along the chart |
| Jacobian / first fundamental form | metric pullback $\varphi^* g$, area and angle distortion |
| texel footprint / anisotropy | eigenvalues of the metric in chart coordinates |
| seam / singular parameterization | chart boundary, cut locus, or non-injective exponential map |

The texture-mapping viewpoint suggests treating the chart as data we can
sample, differentiate, and measure for distortion. The Riemannian viewpoint
supplies the canonical construction around a point.

---

## 3. Normal coordinates via the exponential map

> [!IMPORTANT]
> **Definition (exponential map).** For a Riemannian manifold $(M,g)$ and
> point $p \in M$, the exponential map sends a tangent vector to the endpoint
> of a geodesic:
>
> ```math
> \exp_p : V \subset T_pM \to M,
> \qquad \exp_p(v) = \gamma_v(1),
> ```
>
> where $\gamma_v$ is the geodesic with $\gamma_v(0) = p$ and
> $\gamma_v'(0) = v$.

If we choose an orthonormal basis $(e_1,e_2)$ of $T_pM$, then every tangent
vector can be written as

```math
v = u\,e_1 + v'\,e_2, \qquad (u,v') \in \mathbb{R}^2,
```

and the normal chart is

```math
\Phi_p(u,v') = \exp_p(u\,e_1 + v'\,e_2).
```

This is a 2D parameterized mapping around $p$: the flat UV-like domain is a
disk in $\mathbb{R}^2$, and the image is a geodesic patch on the manifold.

> [!NOTE]
> **Properties of the normal chart.**
>
> * $\Phi_p(0,0) = p$.
> * Straight lines through the origin in parameter space map to geodesics
>   through $p$.
> * The metric at the origin is Euclidean in normal coordinates, so
>   first-order length and angle distortion vanishes at $p$.
> * The chart is generally valid only up to the injectivity radius / cut
>   locus; beyond that, $\exp_p$ can stop being a good parameterization, much
>   like a UV map can fold or overlap.

> [!WARNING]
> **Where the chart stops being a chart.** Normal coordinates are only local.
> Past the cut locus, $\exp_p$ can identify different tangent directions with
> the same surface point, exactly as a UV map can fold over itself. Any
> computational chart needs a radius bound, or a test for injectivity.

---

## 4. Distortion is texture quality

Texture mapping cares about how much a flat texel is stretched on the surface.
The same quantity is measured by the pullback metric. For a chart
$\Phi : U \to M$, let

```math
G_{ij}(u,v) = g(D\Phi_u e_i,\, D\Phi_u e_j).
```

Then:

* $\det(G)$ controls local area scaling.
* The singular values / eigenvalues of $G$ control anisotropic stretch.
* Conformal distortion measures angle error; isometric distortion measures
  length error.
* In normal coordinates, $G_{ij}(0) = \delta_{ij}$ and the first derivatives
  of the metric vanish at the origin; curvature appears in higher-order
  distortion.

This gives a concrete bridge: a "good" local texture patch around a point is a
chart with controlled metric distortion, and the exponential map is the
canonical curvature-aware starting point.

### The Lean distortion API

A chart is represented as a map on graph parameter coordinates. Its Jacobian
is a $2 \times 2$ matrix, and its pullback metric is
$J^{\mathsf T} G\thinspace  J$:

```lean
abbrev ParamChart : Type := Point2 → Point2
abbrev SurfaceChart : Type := Point2 → Point3

def chartJacobian (φ : ParamChart) (u : Point2) : Mat22 :=
  !![deriv (fun t => (φ (t, u.2)).1) u.1, deriv (fun t => (φ (u.1, t)).1) u.2;
     deriv (fun t => (φ (t, u.2)).2) u.1, deriv (fun t => (φ (u.1, t)).2) u.2]

def pullbackGram (h : HeightFun) (φ : ParamChart) (u : Point2) : Mat22 :=
  (chartJacobian φ u)ᵀ * gramMatrix h (φ u) * chartJacobian φ u
```

The distortion objectives become predicates on `pullbackGram`:

```lean
def areaScale (h : HeightFun) (φ : ParamChart) (u : Point2) : ℝ :=
  (pullbackGram h φ u).det

def isConformalAt (h : HeightFun) (φ : ParamChart) (u : Point2) : Prop :=
  ∃ scale : ℝ, pullbackGram h φ u = scale • (1 : Mat22)

def isEqualAreaAt (h : HeightFun) (φ : ParamChart) (u : Point2) : Prop :=
  areaScale h φ u = 1

def isIsometricAt (h : HeightFun) (φ : ParamChart) (u : Point2) : Prop :=
  pullbackGram h φ u = 1
```

Two implications are proved outright: an isometric chart is both conformal and
equal-area.

```lean
theorem isIsometricAt.isConformalAt {h : HeightFun} {φ : ParamChart} {u : Point2}
    (hi : isIsometricAt h φ u) : isConformalAt h φ u := by
  refine ⟨1, ?_⟩
  simpa [isIsometricAt] using hi

theorem isIsometricAt.isEqualAreaAt {h : HeightFun} {φ : ParamChart} {u : Point2}
    (hi : isIsometricAt h φ u) : isEqualAreaAt h φ u := by
  change (pullbackGram h φ u).det = 1
  rw [hi]
  simp
```

> [!TIP]
> **Reading the pullback.** `chartJacobian φ u` is the derivative of the
> chart; `gramMatrix h (φ u)` is the surface metric at the chart's image
> point; and `pullbackGram` is the metric a texture would actually feel. This
> is exactly the $J^{\mathsf T} G\thinspace J$ of the shooting note, with $J$ now the
> chart Jacobian rather than the graph Jacobian.

---

## 5. The chart API

### What the existing code already supplies

> [!NOTE]
> **The ingredients, and where they live.**
>
> * **Point and tangent frame.** `Brane.DiffGeom` defines `graph`, `tangentX`,
>   `tangentY`, `normal`, and `gramMatrix`. An orthonormal tangent basis at
>   $p$ can be obtained from the tangent frame.
> * **Geodesics.** `Brane.Shooting` and `Brane.ParallelTransport` evolve
>   geodesics in parameter space. The shooting method is the computational
>   form of $\exp_p$: choose an initial velocity and integrate for unit time.
>   Eberly's *Riemannian Geodesics* notes derive the geodesic ODE from the
>   metric/Christoffel symbols and treat geodesic tracing as numerical
>   evolution of that ODE — the same bridge used by `expShoot`.
> * **Parallel transport.** Transporting a tangent basis along geodesics gives
>   a moving frame, related to Fermi/parallel normal coordinates.
> * **Distortion.** `gramMatrix h` is already the first fundamental form in
>   the graph parameterization. For a normal chart $\Phi_p$, the pullback
>   metric is sampled numerically by finite differences of $\Phi_p$ — in Lean,
>   `chartJacobian` uses `deriv` and `pullbackGram` composes it with
>   `gramMatrix h`.

### Surface charts

The surface chart is the graph chart composed with a parameter chart:

```lean
def toSurface (h : HeightFun) (φ : ParamChart) : SurfaceChart :=
  fun u => graph h (φ u)

def idParamChart : ParamChart := fun u => u

@[simp]
theorem toSurface_id (h : HeightFun) : toSurface h idParamChart = fun u => graph h u := rfl
```

So the ordinary graph coordinates are the identity chart, and every other
chart is a reparameterization layered on top.

### A computational exponential map

On a graph surface, geodesics in parameter space are computed by the shooting
method. Shooting for unit time from $(p,v)$ is the computational exponential
map in parameter coordinates:

```lean
def shootState (p : Point2) (v : Vel2) : Shoot.ShotState ℝ where
  pos := p
  vel := v

def expShoot (h : HeightFun) (p : Point2) (v : Vel2) (dt : ℝ) (n : ℕ) : Point2 :=
  (Shoot.rk4Trajectory h (shootState p v) dt n).pos
```

The normal/azimuthal chart selects a tangent velocity from UV coordinates and
shoots it:

```lean
def normalParamChart (h : HeightFun) (P : RadialProfile) (p : Point2)
    (e1 e2 : Vel2) (dt : ℝ) (n : ℕ) : ParamChart :=
  fun u =>
    let a := azimuthalUV P u
    let v : Vel2 := ![a.1 * e1 0 + a.2 * e2 0, a.1 * e1 1 + a.2 * e2 1]
    expShoot h p v dt n
```

> [!NOTE]
> **The one `sorry` in the chart layer.** The center of a normal chart should
> be the base point:
>
> ```lean
> theorem normalParamChart_zero (h : HeightFun) (P : RadialProfile) (p : Point2)
>     (e1 e2 : Vel2) (dt : ℝ) (n : ℕ) :
>     normalParamChart h P p e1 e2 dt n (0, 0) = p := by
>   sorry
> ```
>
> It follows from `azimuthalUV P (0,0) = 0`, zero initial velocity, and the
> geodesic ODE; the shooting-integrator bridge that would make it immediate is
> not yet proved.

> [!TIP]
> **A prototype.** Pick $(x_0,y_0)$, build an orthonormal basis in
> $T_p(\mathrm{graph}\thinspace h)$, shoot geodesics for a grid of tangent vectors
> $(u,v') \in [-r,r]^2$, and render the resulting patch. Coloring the patch by
> $\det(G)$ or stretch eigenvalues visualizes chart distortion exactly like a
> texture-mapping debug view.

---

## 6. Projection families as chart choices

[Map projections](https://en.wikipedia.org/wiki/List_of_map_projections) are
conventions for mapping a curved surface to a flat parameter domain. Most are
formulated for the sphere/Earth, but their distortion properties are exactly
the properties we care about when choosing a local chart
$\Phi_p : U \subset \mathbb{R}^2 \to M$ around a point.

The cartographic convention is usually "surface to plane"; the exponential-map
view is often "plane/tangent to surface". For chart design it is useful to
keep both directions in mind:

```math
\begin{array}{ccc}
\text{parameter domain } U \subset \mathbb{R}^2
  & \longleftrightarrow &
  \text{local patch } \Phi_p(U) \subset M \\[2pt]
\text{coordinates} && \text{manifold point} \\
\text{texture UV} && \text{surface location}
\end{array}
```

### Radial profiles

> [!IMPORTANT]
> **Definition (radial profile).** A **radial profile** maps a UV radius to
> the geodesic radius used by an azimuthal chart. The condition
> `radius 0 = 0` keeps the center fixed.

```lean
structure RadialProfile where
  name : String
  radius : ℝ → ℝ
  radius_zero : radius 0 = 0
```

The standard azimuthal profiles are one-liners on top of it:

```lean
def equidistantProfile : RadialProfile where
  name := "equidistant"
  radius := fun r => r
  radius_zero := rfl

def gnomonicProfile (R : ℝ) : RadialProfile where
  name := "gnomonic"
  radius := fun r => R * Real.tan (r / R)
  radius_zero := by simp

def stereographicProfile (R : ℝ) : RadialProfile where
  name := "stereographic"
  radius := fun r => 2 * R * Real.tan (r / (2 * R))
  radius_zero := by simp

def lambertEqualAreaProfile (R : ℝ) : RadialProfile where
  name := "lambert-azimuthal-equal-area"
  radius := fun r => 2 * R * Real.sin (r / (2 * R))
  radius_zero := by simp

def orthographicProfile (R : ℝ) : RadialProfile where
  name := "orthographic"
  radius := fun r => R * Real.sin (r / R)
  radius_zero := by simp
```

The UV coordinates themselves are converted from Cartesian to polar and back:

```lean
def uvRadius (u : Point2) : ℝ := Real.sqrt (u.1 * u.1 + u.2 * u.2)

def uvDir (u : Point2) : Point2 :=
  let r := uvRadius u
  if r = 0 then (0, 0) else (u.1 / r, u.2 / r)

def azimuthalUV (P : RadialProfile) (u : Point2) : Point2 :=
  let r := uvRadius u
  let d := uvDir u
  let ρ := P.radius r
  (ρ * d.1, ρ * d.2)
```

A centered parameter chart is then a center plus two parameter directions
used as the UV basis:

```lean
def azimuthalParamChart (P : RadialProfile) (p : Point2) (e1 e2 : Vel2) : ParamChart :=
  fun u =>
    let a := azimuthalUV P u
    (p.1 + a.1 * e1 0 + a.2 * e2 0, p.2 + a.1 * e1 1 + a.2 * e2 1)

@[simp]
theorem azimuthalParamChart_zero (P : RadialProfile) (p : Point2) (e1 e2 : Vel2) :
    azimuthalParamChart P p e1 e2 (0, 0) = p := by
  simp [azimuthalParamChart]
```

The azimuthal family suggests making the chart choice explicit as

```math
\Phi_p(r,\theta) = E_p\bigl(\rho(r)\,e_\theta\bigr),
\qquad\text{or}\qquad
\Phi_p(u,v) = E_p\bigl(\sigma(u,v)\bigr),
```

where $E_p$ is the exponential/geodesic map, $e_\theta$ is a direction in
$T_pM$, and $\rho$/$\sigma$ selects the radial metric: identity for
equidistant, tangent for gnomonic-like, sine/stereographic scalings for
area/conformal variants on spheres. On a general Riemannian manifold, the same
radial rescalings can be used as chart reparameterizations, but their global
cartographic invariants may only hold approximately away from $p$.

### Azimuthal projections around a center

Azimuthal projections are the closest cartographic analogue of a point-centered
Riemannian chart. They place a chosen center $p$ at the origin of the plane
and assign directions around $p$ to angles in the parameter domain.

| Map projection | Preserved property | Riemannian / chart analogue | Notes for $\Phi_p$ |
| --- | --- | --- | --- |
| Azimuthal equidistant | distances from center along radials | geodesic polar / normal coordinates | $\exp_p$ preserves radial geodesic distance: $d(p,\exp_p(v)) = \lVert v\rVert$ before cut locus. The natural "measure from $p$" chart. |
| Gnomonic | geodesics as straight lines (sphere) | normal coordinates, radial geodesics | In normal coordinates, geodesics through $p$ are straight parameter lines. On general manifolds this does not make all geodesics straight; constant curvature is special. |
| Stereographic | angles / conformal | conformal normal coordinates / isothermal local chart | Preserves local shape but not area. Useful when texture/debugging should keep angles faithful near $p$. |
| Lambert azimuthal equal-area | area | equal-area local parameterization | Preserves $\det(G)$ in the idealized target sense; useful when sampling density or physical area matters. |
| Orthographic | perspective view | tangent-plane projection / graph projection | Projects along a normal/eye direction. For an embedded surface this is close to "lift the tangent plane" or to the graph chart after local linearization. |
| Vertical perspective | finite-distance perspective | camera/pin-hole projection of a patch | Relevant to rendering: a visible patch is parameterized by view rays, not intrinsic geodesic distance. |

### Cylindrical, conic, and strip charts

Cylindrical and conic projections are less "around a point" and more "around
an axis or along a strip". They become relevant when the local patch is
organized around a curve, direction field, or boundary rather than a single
center.

| Projection family | Cartographic idea | Chart analogue |
| --- | --- | --- |
| Cylindrical (Mercator, Lambert cylindrical equal-area, equirectangular) | unwrap around an axis; meridians/parallels form a grid | coordinates along a geodesic/flow and a transverse coordinate; Fermi or tube-like charts |
| Conic (Lambert conformal conic, Albers equal-area) | unwrap over a cone tangent/secant to a latitude band | charts adapted to a ring/band around a point or curve, with one or two low-distortion parallels |
| Pseudocylindrical (sinusoidal, Mollweide, Robinson, Equal Earth) | compromise global shapes with curved meridians | nonlinear parameter remappings that trade area, angle, and distance distortion over a larger patch |

For brane, a Fermi coordinate chart along a geodesic is the natural
"cylindrical" counterpart: one coordinate is arc length along the curve, the
other is a normal offset transported along it.

### Distortion properties as chart objectives

The projection classification by property translates directly into chart
selection criteria:

| Property | Map-projection term | Chart metric condition | Use when |
| --- | --- | --- | --- |
| Conformal | conformal / orthomorphic | $G(u,v) = \lambda(u,v)\thinspace I$ | preserving angles, local shape, or grid orthogonality matters |
| Equal-area | equal-area / authalic | $\det(G(u,v)) = \text{const}$ | sampling density, mass, or texture texel area should be uniform |
| Equidistant | equidistant | distances preserved along selected lines | radial distance from $p$, or distances along a curve/grid family, matter |
| Compromise | compromise | no single invariant; minimize combined distortion | visualization or texture mapping over a larger patch |

No single chart on a curved manifold can be simultaneously isometric
everywhere. The map-projection analogy makes this a design choice rather than
a failure: pick the invariant that the downstream computation needs.

A projection family is packaged as a name, a profile, and an intended
objective:

```lean
structure ProjectionFamily where
  name : String
  profile : RadialProfile
  objective : String

def equidistantAzimuthal : ProjectionFamily where
  name := "azimuthal-equidistant"
  profile := equidistantProfile
  objective := "preserve radial geodesic distance from center"
```

### Polyhedral/globular charts and atlases

Polyhedral projections (e.g. Cahill butterfly, Lee conformal tetrahedron) and
quincuncial/tiled conformal maps suggest an atlas view: cover a manifold with
several low-distortion charts rather than forcing one chart to cover a large
region. This connects to texture atlases and to the cut locus/injectivity
limit of normal coordinates.

```math
\text{atlas} = \{(U_i, \Phi_i)\}
\qquad\text{with small distortion per chart}
```

```math
\text{seams / cut boundaries}
\;\longleftrightarrow\;
\text{chart transitions / overlap maps}
```

---

## 7. Formalization path

The original plan, with the current status of each step:

1. **Abstract exponential map interface.** State the minimal data needed:
   tangent vectors, geodesic flow, and $\exp_p(v) = \gamma_v(1)$.
   *Status:* represented computationally by `expShoot`; the analytic interface
   is still open.
2. **Graph-surface specialization.** Use the existing geodesic ODE/shooting
   definitions to define a computational exponential map on $\mathrm{graph}\thinspace h$.
   *Status:* `expShoot`.
3. **Normal chart.** Package an orthonormal basis of $T_pM$ and define
   $\Phi_p(u,v')$.
   *Status:* `normalParamChart`, with `e1 e2` carrying the basis data.
4. **Metric pullback.** Prove or numerically evaluate
   $G = D\Phi^{\mathsf T} D\Phi$ / $\varphi^* g$.
   *Status:* `chartJacobian`, `pullbackGram`, `areaScale`.
5. **Distortion lemmas.** Show $G(0) = I$ in normal coordinates and relate
   higher-order terms to curvature.
   *Status:* the isometric ⇒ conformal/equal-area implications are proved; the
   normal-coordinate expansion is open.

---

## 8. Proven vs. declared

| Result | Lean name | Status |
| --- | --- | --- |
| Graph chart is the identity chart | `toSurface_id` | proved |
| Chart Jacobian | `chartJacobian` | definition |
| Pullback metric | `pullbackGram` | definition |
| Area scale | `areaScale` | definition |
| Conformal / equal-area / isometric predicates | `isConformalAt`, `isEqualAreaAt`, `isIsometricAt` | definition |
| Isometric ⇒ conformal | `isIsometricAt.isConformalAt` | proved |
| Isometric ⇒ equal-area | `isIsometricAt.isEqualAreaAt` | proved |
| Azimuthal profile fixes the center | `azimuthalUV_zero` | proved |
| Azimuthal parameter chart fixes the center | `azimuthalParamChart_zero` | proved |
| Computational exponential map | `expShoot` | definition |
| Normal chart fixes the center | `normalParamChart_zero` | `sorry` |

The `sorry` is the analytic bridge between the numerical integrator and the
geodesic ODE; all the chart, metric, and profile bookkeeping around it is
proved.

---

## 9. Cheat sheet: file ↔ concept

| `Brane/ChartMap.lean` | Plain-language description | Math object |
| --- | --- | --- |
| `ParamChart` | a chart in graph parameter coordinates | `Point2 → Point2` |
| `SurfaceChart` | a chart into ambient space | `Point2 → Point3` |
| `toSurface h φ` | compose a parameter chart with `graph h` | $\sigma \circ \varphi$ |
| `chartJacobian φ u` | derivative of the chart | $D\varphi$ |
| `pullbackGram h φ u` | texture-space metric | $(D\varphi)^{\mathsf T} G\thinspace (D\varphi)$ |
| `areaScale h φ u` | local texel area | $\det(\text{pullbackGram})$ |
| `isConformalAt` | angles preserved | $G = \lambda I$ |
| `isEqualAreaAt` | area preserved | $\det G = 1$ |
| `isIsometricAt` | lengths and angles preserved | $G = I$ |
| `RadialProfile` | radial reparameterization of an azimuthal chart | $\mathbb{R} \to \mathbb{R}$, fixes $0$ |
| `azimuthalUV P u` | Cartesian UV → profiled radius + direction | $(\rho(r)\cos\theta,\thinspace \rho(r)\sin\theta)$ |
| `azimuthalParamChart P p e1 e2` | centered chart in parameter coordinates | $p + a_1 e_1 + a_2 e_2$ |
| `expShoot h p v dt n` | computational $\exp_p(v)$ | RK4 geodesic shot |
| `normalParamChart h P p e1 e2` | normal chart from a UV profile | $\exp_p$ on profiled UV |
| `ProjectionFamily` | named chart choice + objective | `name`, `profile`, `objective` |

---

## 10. Open questions

* Should the primary object be a chart into parameter space $(x,y)$ or directly
  into the embedded surface $\mathrm{graph}\thinspace h\thinspace (x,y)$?
* For graph surfaces, how does the graph chart $(x,y)$ compare to the normal
  chart around $p$ as a texture parameterization?
* What is the right Lean representation of $T_pM$: a subtype of
  $\mathbb{R}^3$ tangent to the graph, or the parameter-plane velocity space
  pushed forward by $d(\mathrm{graph}\thinspace h)$?
* How should cut locus / injectivity radius be represented in a computational
  prototype?
* Can the existing `ParallelTransport` code produce a stable frame for Fermi
  coordinates along a curve, not just around a point?
* Which projection invariants survive as exact properties on general
  Riemannian manifolds, and which are only sphere/constant-curvature
  analogues?
* Can we define a "projection family" API: a radial/profile function composed
  with $\exp_p$, with distortion measured by the pullback metric?

---

## References

* Manfredo do Carmo, *Riemannian Geometry*, chapters on geodesics, exponential
  map, and normal coordinates.
* John M. Lee, *Introduction to Riemannian Manifolds*, normal coordinates and
  metric expansion.
* Texture mapping / parameterization surveys for the graphics-side vocabulary:
  UV charts, Jacobians, conformal and isometric distortion.
* David Eberly, [Riemannian Geodesics](https://www.geometrictools.com/Documentation/RiemannianGeodesics.pdf),
  Geometric Tools Documentation — computational treatment of Riemannian
  metrics, Christoffel symbols, geodesic equations, and geodesic evolution;
  useful background for implementing `exp_p` by shooting.
* Wikipedia, [List of map projections](https://en.wikipedia.org/wiki/List_of_map_projections)
  — catalog of projection families and distortion properties used as chart
  analogies.
