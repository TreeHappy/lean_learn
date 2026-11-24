# Connections, Christoffel symbols, and parallel transport

This note explains the four objects that the Lean modules
`lean/Brane/Connections.lean` and `lean/Brane/ParallelTransport.lean`
formalize:

1. an **affine connection** on the parameter plane;
2. its **Christoffel symbols** and the **Levi-Civita connection** of a
   graph surface;
3. **parallel transport** along a curve and the **holonomy** it generates;
4. a **connection on a vector bundle**, together with the dual, tensor, and
   endomorphism connections it induces.

Everything is concrete: the manifold is the parameter plane
`Point2 = ℝ × ℝ`, a vector field is a function `Point2 → Vel2`, and the
metric of a graph is the first fundamental form `gramMatrix h` from
`Brane.DiffGeom`. No abstract manifold is needed, but every definition
matches the standard one. Where useful, we read the same objects in the
vector/matrix language of [`shooting-method.md`](shooting-method.md):
`J`, `G = JᵀJ`, `H`, `∇h`, and the geodesic acceleration
`a = -G⁻¹ (vᵀHv) ∇h`.

The companion note on Lie algebras is [`lie-algebra.md`](lie-algebra.md).

---

## 1. Vector fields on the parameter plane

A **vector field** is a function that assigns a velocity `Vel2 = Fin 2 → ℝ`
to every parameter point:

```lean
abbrev ParamField : Type := Point2 → Vel2
abbrev ScalarField : Type := HeightFun   -- ℝ → ℝ → ℝ
```

The **directional derivative** of a field `Y` at `p` along the velocity `v`
is the Fréchet derivative applied to the direction `(v₀, v₁)`:

```lean
def velToDir (v : Vel2) : Point2 := (v 0, v 1)

def dirDeriv (Y : ParamField) (p : Point2) (v : Vel2) : Vel2 :=
  fderiv ℝ Y p (velToDir v)
```

`dirDerivScalar` is the scalar version, used for the Leibniz rule. The
linearity lemmas used by the connection axioms are proved in full:

* `dirDeriv_add_direction`, `dirDeriv_smul_direction` — linearity in the
  direction;
* `dirDeriv_add_Y`, `dirDeriv_smul_Y` — linearity in the field;
* `dirDeriv_smul_scalar` — the product rule
  `d(fY) = (df)Y + f dY`.

## 2. Affine connection

An **affine connection** is a rule `∇` that differentiates a vector field
`Y` along another vector field `X`. It is additive and `C∞`-linear in `X`
and satisfies the Leibniz rule in `Y`. In Lean this is the structure
`Brane.Conn.AffineConnection`:

```lean
structure AffineConnection where
  cov : ParamField → ParamField → ParamField
  cov_add_left  : ∀ X X' Y, cov (X + X') Y = cov X Y + cov X' Y
  cov_smul_left : ∀ (f : ScalarField) X Y,
    cov (fun p => f p.1 p.2 • X p) Y = fun p => f p.1 p.2 • cov X Y p
  cov_add_right : ∀ X Y Y', Differentiable ℝ Y → Differentiable ℝ Y' →
    cov X (Y + Y') = cov X Y + cov X Y'
  cov_smul_right : ∀ (a : ℝ) X Y, Differentiable ℝ Y →
    cov X (a • Y) = a • cov X Y
  cov_leibniz : ∀ (f : ScalarField) X Y,
    Differentiable ℝ (fun p => f p.1 p.2) → Differentiable ℝ Y →
    cov X (f • Y) = fun p => dirDerivScalar f p (X p) • Y p + f p.1 p.2 • cov X Y p
```

The two `C∞`-linearity laws are exactly the two Wikipedia axioms:
`∇_{fX} Y = f ∇_X Y` and `∇_X (fY) = (∂_X f) Y + f ∇_X Y`.

The simplest example is the **flat connection**, ordinary directional
differentiation. All its axioms are proved in `flatConn`:

```lean
def flatConn : AffineConnection where
  cov X Y := fun p => dirDeriv Y p (X p)
  ...
```

### Christoffel symbols

A metric on the parameter plane is a smoothly varying matrix
`g : Point2 → Mat22`; for a graph it is `gramMatrix h`. Write
`∂_i g_{jl}` for the partial derivative of the metric. The **Christoffel
symbols of the second kind** are

$$
\Gamma^k{}_{ij} = \tfrac12\,(g^{-1})^{kl}
  \bigl(\partial_i g_{jl} + \partial_j g_{il} - \partial_l g_{ij}\bigr),
$$

which is `christoffel g p k i j` in Lean. They are symmetric in the lower
indices whenever the metric is symmetric (`christoffel_symm`).

The symbols turn into a connection by adding the correction term
`Γ^k_{ij} X^i Y^j` to the flat derivative:

```lean
def covOfChristoffel (Γ : Point2 → Fin 2 → Mat22) : AffineConnection where
  cov X Y := fun p => dirDeriv Y p (X p) + christoffelCorr Γ p (X p) (Y p)
  ...
```

The **Levi-Civita connection** of the graph of `h` is the connection whose
symbols come from `gramMatrix h`:

```lean
def leviCivita (h : HeightFun) : AffineConnection :=
  covOfChristoffel (christoffel (gramMatrix h))
```

### Matrix / vector form on a graph surface

The shooting method in [`shooting-method.md`](shooting-method.md) works with
the concrete matrix objects of the graph `σ(p) = (p.1, p.2, h p.1 p.2)`.
The connection concepts above have direct matrix/vector readings in that
language.

| Connection object | Matrix / vector reading | Lean name |
| --- | --- | --- |
| tangent basis | columns of the Jacobian `J = [[1,0],[0,1],[∂ₓh,∂ᵧh]]` | `DiffGeom.jacobian` |
| metric `g` | Gram matrix `G = JᵀJ = I + ∇h ∇hᵀ` | `DiffGeom.gramMatrix` |
| metric inverse `g⁻¹` | `G⁻¹ = (1/det G) [[g₂₂,-g₁₂],[-g₁₂,g₁₁]]`, `det G = 1+|∇h|²` | `DiffGeom.det_gramMatrix_eq` |
| metric derivative `∂_i g_{jl}` | derivative of `G` entries, built from first/second partials of `h` | `Conn.metricPartial` |
| Christoffel correction | `Γ(p; X, Y)^k = ∑_{i,j} Γ^k_{ij}(p) X^i Y^j`, a velocity in `Vel2` | `Conn.christoffelCorr` |
| covariant derivative | `(∇_X Y)(p) = dY_p(X(p)) + Γ(p; X(p), Y(p))` | `covOfChristoffel` / `AffineConnection.cov` |

The key vector identity is that the Christoffel correction is bilinear in
the two velocity inputs: it behaves like a matrix-valued quadratic form
`(X, Y) ↦ Γ(X,Y)` with output in `Vel2 = Fin 2 → ℝ`. In components this is
exactly the ordinary matrix/vector contraction

```text
Γ(p; X, Y) = ![ ∑ i j Γ⁰_{ij} X^i Y^j,  ∑ i j Γ¹_{ij} X^i Y^j ].
```

For a graph surface, the metric is the familiar Gram matrix from the
shooting method,

```text
G(p) = gramMatrix h p =
  !![1 + (∂ₓh)²,    ∂ₓh ∂ᵧh;
     ∂ₓh ∂ᵧh,    1 + (∂ᵧh)²],
```

so the Levi-Civita connection of the graph is the flat directional
derivative in parameter coordinates plus a correction computed from `G` and
its first partial derivatives. The flat part is the "parameter-plane"
calculus; the Christoffel correction is the curvature compensation required
by the distorted map `G = JᵀJ`.

The two defining properties are stated as the `sorry`ed geometric bridges
`leviCivita_torsion_free` and `leviCivita_metric_compatible`, and the
uniqueness statement is `leviCivita_unique` — the fundamental theorem of
Riemannian geometry in this coordinate model.

## 3. Torsion and curvature

The **Lie bracket** of parameter fields is
`[X, Y] = dY(X) - dX(Y)` (`lieBracketParam`). The **torsion** and
**curvature** of an affine connection are

$$
T(X,Y) = \nabla_X Y - \nabla_Y X - [X,Y],
\qquad
R(X,Y)Z = \nabla_X\nabla_Y Z - \nabla_Y\nabla_X Z - \nabla_{[X,Y]} Z,
$$

defined as `torsion` and `curvature`. Their algebraic symmetries
(`torsion_anti`, `curvature_tensorial`) are stated with `sorry`; they are
the tensoriality statements from the Wikipedia page.

## 4. Parallel transport

Fix a curve `γ : ℝ → Point2` and a field `V` along it. In the
vector/matrix language of the shooting method, `γ(t)` is a parameter-plane
position and `V(t)` is a `Vel2` — a two-component vector
`![V₀(t), V₁(t)]`. The curve velocity and componentwise acceleration are

```lean
def curveVelocity (γ : Curve) (t : ℝ) : Vel2 :=
  ![deriv (fun s => (γ s).1) t, deriv (fun s => (γ s).2) t]

def curveAccel (γ : Curve) (t : ℝ) : Vel2 :=
  fun k => deriv (fun s => curveVelocity γ s k) t
```

The **covariant derivative along `γ`** is the ordinary componentwise time
derivative plus the Christoffel correction:

$$
\frac{DV}{dt} = \dot V + \Gamma(\dot\gamma, V),
\qquad
\left(\frac{DV}{dt}\right)^k = \dot V^k + \sum_{i,j} \Gamma^k{}_{ij}(\gamma)\, \dot\gamma^i\, V^j.
$$

This is exactly `covAlongChristoffel`: `V̇` is the vector derivative, and
`christoffelCorr Γ (γ t) (curveVelocity γ t) (V t)` is the same
matrix/vector contraction as in §2.

```lean
def covAlongChristoffel (Γ : Point2 → Fin 2 → Mat22) (γ : Curve)
    (V : FieldAlong γ) (t : ℝ) : Vel2 :=
  fun k => deriv (fun s => V s k) t +
    christoffelCorr Γ (γ t) (curveVelocity γ t) (V t) k
```

The field is **parallel** when this vanishes for every `t`:

```lean
def isParallel (Γ : Point2 → Fin 2 → Mat22) (γ : Curve)
    (V : FieldAlong γ) : Prop :=
  ∀ t : ℝ, covAlongChristoffel Γ γ V t = 0
```

In matrix terms, parallel transport is the linear first-order ODE

```text
V̇(t) = - Γ(γ(t); γ̇(t), V(t)),
V(t₀) = v₀.
```

Existence and uniqueness are the Picard–Lindelöf theorem; they are stated
as `parallelTransport_exists` (a documented `sorry`) and the transport
field is built from it with `Classical.choose`:

```lean
noncomputable def parallelTransport (Γ) (γ) (t₀) (v₀) : FieldAlong γ :=
  Classical.choose (parallelTransport_exists Γ γ t₀ v₀)
```

The initial condition and the parallel equation are immediate from the
choice (`parallelTransport_initial`, `parallelTransport_isParallel`). The
transport map `transportMap Γ γ s t` is linear (`transportMap_linear`,
`sorry`), and transporting forward then back along the reversed curve is
the identity (`transportMap_reverse`, `sorry`). These two facts say that
parallel transport is a linear isomorphism between fibres.

**Holonomy** is what happens when you transport a vector around a closed
loop. The set of all such transport maps based at `p` is
`holonomyGroup Γ p`; that the identity belongs to it is
`id_mem_holonomyGroup`.

### Geodesics as parallel velocity

A **geodesic** is a curve that is parallel to itself:

```lean
def isGeodesic (Γ : Point2 → Fin 2 → Mat22) (γ : Curve) : Prop :=
  isParallel Γ γ (curveVelocity γ)
```

Unfolding the definition gives the coordinate geodesic ODE

```text
γ̈^k + ∑_{i,j} Γ^k_{ij}(γ) γ̇^i γ̇^j = 0,
i.e.  curveAccel γ t + Γ(γ t; γ̇(t), γ̇(t)) = 0.
```

On the graph surface, the Levi-Civita symbols are those of
`G = gramMatrix h`. The shooting-method derivation solves the same equation
in matrix form by projecting the lifted 3D acceleration onto the tangent
plane:

```text
G a + (vᵀ H v) ∇h = 0,
a = -G⁻¹ (vᵀ H v) ∇h = geoAccel h p v,
```

where `G = JᵀJ`, `H` is the Hessian of `h`, `v = γ̇`, and
`vᵀHv = hessQuad h p v` (`Shoot.hessQuad`). The bridge theorem states that
these two geodesic descriptions are the same:

```lean
theorem isGeodesic_leviCivita_iff_Shoot (h : HeightFun) (γ : Curve) :
    isGeodesic (christoffel (gramMatrix h)) γ ↔
      ∀ t : ℝ, curveAccel γ t = Shoot.geoAccel h (γ t) (curveVelocity γ t)
```

This is the concrete link between the connection picture and the code that
actually integrates trajectories: `Shoot.field` stores `(v, a)` with
`a = geoAccel h p v`, so the RK4/Euler shooters are numerical integrators
of the Levi-Civita geodesic ODE.

## 5. Connections on vector bundles

An affine connection is the tangent-bundle case of a **connection on a
vector bundle**. For the trivial bundle `Point2 × F`, the structure
`VectorBundleConnection F` has the same two axioms, but the section takes
values in an arbitrary normed space `F`:

```lean
structure VectorBundleConnection (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] where
  cov : ParamField → (Point2 → F) → (Point2 → F)
  ...
```

Every affine connection is a vector-bundle connection on the tangent bundle
(`affineAsVectorBundle`). The curvature of a vector-bundle connection is
`vbcCurvature`. The standard induced connections are stated as existence
theorems with `sorry`:

* `dualConn_exists` — the dual connection on `F →L[ℝ] ℝ`, characterized by
  `⟨∇*_X ξ, σ⟩ = X⟨ξ, σ⟩ - ⟨ξ, ∇_X σ⟩`;
* `tensorConn_exists` — the tensor-product connection on `F × G`;
* `endConn_exists` — the endomorphism connection on `F →L[ℝ] F`, with
  `(∇_X u) σ = ∇_X (u σ) - u (∇_X σ)`.

These are exactly the constructions listed on the Wikipedia page
*Connection (vector bundle)*, specialized to a trivial bundle over the
parameter plane.

---

## Proof status

| Result | Lean name | Status |
| --- | --- | --- |
| Directional-derivative linearity | `dirDeriv_*` | proved |
| Flat connection axioms | `flatConn` | proved |
| Christoffel correction bilinearity | `christoffelCorr_*` | proved |
| Christoffel symmetry | `christoffel_symm` | proved |
| `covOfChristoffel` axioms | `covOfChristoffel` | proved |
| Levi-Civita torsion-free | `leviCivita_torsion_free` | `sorry` |
| Levi-Civita metric compatibility | `leviCivita_metric_compatible` | `sorry` |
| Torsion antisymmetry | `torsion_anti` | `sorry` |
| Curvature antisymmetry | `curvature_tensorial` | `sorry` |
| Uniqueness of Levi-Civita | `leviCivita_unique` | `sorry` |
| Parallel transport exists | `parallelTransport_exists` | `sorry` |
| Transport linearity | `transportMap_linear` | `sorry` |
| Reverse-curve inverse | `transportMap_reverse` | `sorry` |
| Geodesic ↔ shooting | `isGeodesic_leviCivita_iff_Shoot` | `sorry` |
| Dual / tensor / end connections | `*Conn_exists` | `sorry` |

The `sorry`s are deliberate: they are the geometric bridges that need ODE
theory or a metric computation, while the algebraic infrastructure around
them is proved.

---

## References

### Primary encyclopedia articles

* Wikipedia, [Affine connection](https://en.wikipedia.org/wiki/Affine_connection)
* Wikipedia, [Parallel transport](https://en.wikipedia.org/wiki/Parallel_transport)
* Wikipedia, [Connection (vector bundle)](https://en.wikipedia.org/wiki/Connection_(vector_bundle))
* Wikipedia, [Covariant derivative](https://en.wikipedia.org/wiki/Covariant_derivative)
* Wikipedia, [Levi-Civita connection](https://en.wikipedia.org/wiki/Levi-Civita_connection)
* Wikipedia, [Christoffel symbols](https://en.wikipedia.org/wiki/Christoffel_symbols)
* Wikipedia, [Torsion tensor](https://en.wikipedia.org/wiki/Torsion_tensor)
* Wikipedia, [Curvature form](https://en.wikipedia.org/wiki/Curvature_form)
* Wikipedia, [Holonomy](https://en.wikipedia.org/wiki/Holonomy)

### Wolfram MathWorld

* [Affine Connection](https://mathworld.wolfram.com/AffineConnection.html)
* [Christoffel Symbol of the Second Kind](https://mathworld.wolfram.com/ChristoffelSymboloftheSecondKind.html)
* [Connection](https://mathworld.wolfram.com/Connection.html)
* [Parallel Transport](https://mathworld.wolfram.com/ParallelTransport.html)
* [Levi-Civita Connection](https://mathworld.wolfram.com/Levi-CivitaConnection.html)
* [Holonomy Group](https://mathworld.wolfram.com/HolonomyGroup.html)

### nLab

* [affine connection](https://ncatlab.org/nlab/show/affine+connection)
* [parallel transport](https://ncatlab.org/nlab/show/parallel+transport)
* [connection on a vector bundle](https://ncatlab.org/nlab/show/connection+on+a+vector+bundle)
* [holonomy group](https://ncatlab.org/nlab/show/holonomy+group)

### Encyclopedia of Mathematics

* [Connections on a manifold](https://encyclopediaofmath.org/wiki/Connections_on_a_manifold)
* [Parallel transport](https://encyclopediaofmath.org/wiki/Parallel_transport)
* [Riemannian connection](https://encyclopediaofmath.org/wiki/Riemannian_connection)

### Free books and lecture notes

* C. Wendl, *Lecture Notes on Bundles and Connections* —
  <https://www.mathematik.hu-berlin.de/~wendl/connections.html>
* D. Eberly, *Riemannian Geodesics* (Geometric Tools Documentation) —
  <https://www.geometrictools.com/Documentation/RiemannianGeodesics.pdf> —
  computational companion for the geodesic equation, Christoffel symbols, and
  geodesic evolution on Riemannian manifolds, complementing the connection and
  parallel-transport view developed here.
* M. Taylor, *Connections and Curvature* (Appendix C) —
  <https://mtaylor.web.unc.edu/wp-content/uploads/sites/16915/2018/04/appendc.pdf>
* L. Nicolaescu, *Lectures on the Geometry of Manifolds* —
  <https://academicweb.nd.edu/~lnicolae/Lectures.pdf>
* V. V. Datar, *Lectures on Riemannian Geometry* —
  <https://math.iisc.ac.in/~vvdatar/Lecture_Notes/RG_Lectures_typesett_published.pdf>
* M. Taylor, *Riemannian Geometry* (Imperial College notes) —
  <https://www.ma.imperial.ac.uk/~mtaylor5/rgnotes.pdf>
* W. Merry, *Differential Geometry* (ETH, 2021) —
  <https://www2.math.ethz.ch/will-merry/files/Merry%20-%20Differential%20Geometry%20%282021%29.pdf>
* D. Wilkins, *A Course in Riemannian Geometry* —
  <https://www.maths.tcd.ie/~dwilkins/Courses/425/RiemGeom.pdf>
* E. Solé-Farré, *Lecture Notes on Riemannian Geometry and Holonomy* —
  <https://enric-sf.github.io/courses/HSM/ln-draft.pdf>
* M. Reyes-Reyes, *Affine Connections* —
  <https://reyes-reyes.com/wp-content/uploads/2009/01/affineconnections.pdf>

### Papers

* J. L. Koszul, "Homologie et cohomologie des algèbres de Lie",
  *Bull. Soc. Math. France* **78** (1950), 65–127.
* C. Ehresmann, "Les connexions infinitésimales dans un espace fibré
  différentiable", *Colloque de topologie* (Bruxelles, 1950), 1951.
* W. Ambrose and I. M. Singer, "A theorem on holonomy",
  *Trans. Amer. Math. Soc.* **75** (1953), 428–443.
* M. S. Knebelman, "Spaces of conformally flat manifolds",
  *Proc. Amer. Math. Soc.* **2** (1951), 831–832.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*,
  Vol. I, Interscience, 1963.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer,
  2018.
* R. W. Sharpe, *Differential Geometry: Cartan's Generalization of Klein's
  Erlangen Program*, Springer, 1997.
* F. Dumitrescu, "Connections and Parallel Transport", arXiv:0903.0121 —
  <https://arxiv.org/abs/0903.0121>
* A. Marsh, "Riemannian Geometry: Definitions, Pictures, and Results",
  arXiv:1412.2393 — <https://arxiv.org/abs/1412.2393>
* B. Iliev, "The Meaning of the Christoffel Symbols", arXiv:math-ph/0510004
  — <https://arxiv.org/abs/math-ph/0510004>

See [`../bibtex.md`](../bibtex.md) for the human-readable link list and
[`../references.bib`](../references.bib) for the BibTeX entries.
