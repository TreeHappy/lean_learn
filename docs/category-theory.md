# Category Theory: A Working Dictionary

Category theory is a language for *structure-preserving maps*. It is useful
here not because the code needs another layer of abstraction, but because the
existing notes already contain the same patterns under different names: a
chart is a map, a reparameterization is a map between charts, a bundle is a
family of fibres, a section is a choice of point in each fibre, parallel
transport is a path-dependent linear map, and a numerical integrator is a
stateful step.

This note has two parts.

* **Part I** is the minimum vocabulary: category, functor, natural
  transformation, adjunction, limit and colimit, monad, groupoid, enrichment,
  and Yoneda.
* **Part II** is the dictionary: each concept is matched to a concrete object
  in [`shooting-method.md`](shooting-method.md),
  [`connections.md`](connections.md),
  [`chart-mapping.md`](chart-mapping.md), or
  [`lie-algebra.md`](lie-algebra.md), and to a declaration in the Lean
  modules.

The new Lean companion is
[`lean/Brane/CategoryTheory.lean`](../lean/Brane/CategoryTheory.lean)
(namespace `Brane.Cat`). The snippets below are quoted from it. Part I does
not depend on the rest of the repository; Part II does not depend on category
theory beyond Part I.

> [!NOTE]
> **The one-sentence version.** A category records objects and
> structure-preserving maps; a functor records a construction that respects
> those maps; a natural transformation records a comparison that is compatible
> with those maps; a limit or colimit records gluing; a monad records a notion
> of computation; a groupoid records invertible paths. Every one of these has
> a concrete instance in this repository.

| Symbol | Meaning |
| --- | --- |
| $\mathcal{C}, \mathcal{D}$ | categories |
| $X, Y, Z$ | objects of a category |
| $X \to Y$ | a morphism from $X$ to $Y$ |
| $\mathrm{Hom}(X,Y)$ | the collection of morphisms from $X$ to $Y$ |
| $F : \mathcal{C} \to \mathcal{D}$ | a functor |
| $F \dashv G$ | $F$ is left adjoint to $G$ |
| $\mathbf{1}$ | a terminal object |
| $\mathbf{Type}$ | the category of types and functions |
| $\mathbf{Vect}_{\mathbb{R}}$ | real vector spaces and linear maps |
| $\mathbf{Set}$ | sets and functions |

---

# Part I. The toolkit

## 1. Categories

> [!IMPORTANT]
> **Definition (category).** A **category** $\mathcal{C}$ consists of
>
> * a collection of **objects** $\mathrm{Ob}(\mathcal{C})$;
> * for each pair of objects $X, Y$, a collection of **morphisms**
>   $\mathrm{Hom}(X,Y)$;
> * an **identity** $\mathrm{id}_X : X \to X$ for each object;
> * a **composition** operation
>   $\circ : \mathrm{Hom}(Y,Z) \times \mathrm{Hom}(X,Y) \to \mathrm{Hom}(X,Z)$,
>
> such that composition is associative and the identities act as neutral
> elements.

The definition is deliberately thin. It says what a *map* is, not what the
objects are made of. That is why the same definition covers functions,
linear maps, paths, and reparameterizations.

The examples that matter here:

| Category | Objects | Morphisms |
| --- | --- | --- |
| $\mathbf{Type}$ | types | functions |
| $\mathbf{Vect}_{\mathbb{R}}$ | real vector spaces | linear maps |
| $\mathbf{Over}(X)$ | maps $Y \to X$ | commuting triangles |
| $\mathbf{SingleObj}(M)$ | one object | elements of a monoid $M$ |
| $\Pi_1(X)$ | points of $X$ | paths up to homotopy |

The **slice category** $\mathbf{Over}(X)$ is the first one to internalize. An
object is a map $p : Y \to X$; a morphism from $p : Y \to X$ to
$q : Z \to X$ is a map $f : Y \to Z$ with $q \circ f = p$. In a diagram:

```math
\begin{array}{ccc}
Y & \xrightarrow{f} & Z \\
 & {\scriptstyle p}\searrow & \downarrow{\scriptstyle q} \\
 & & X
\end{array}
```

A **groupoid** is a category in which every morphism is invertible. The
fundamental groupoid $\Pi_1(X)$ is the groupoid of points and homotopy
classes of paths; the path groupoid is the same construction before quotienting
by homotopy.

### The chart category in Lean

The new module makes the category of parameter charts explicit. A morphism
from $\varphi$ to $\psi$ is a reparameterization $f$ with
$\varphi = \psi \circ f$:

```lean
structure ParamChartHom (φ ψ : ParamChart) where
  f : ParamChart
  comm : φ = ψ ∘ f

instance : CategoryStruct ParamChart where
  Hom := ParamChartHom
  id φ := ⟨id, rfl⟩
  comp := fun {φ ψ χ} f g => ⟨g.f ∘ f.f, by
    calc φ = ψ ∘ f.f := f.comm
      _ = (χ ∘ g.f) ∘ f.f := congrArg (fun k => k ∘ f.f) g.comm
      _ = χ ∘ (g.f ∘ f.f) := Function.comp_assoc χ g.f f.f⟩
```

The proof field `comm` is the only non-computational part. The category laws
are proved by cases and `rfl`, because composition is ordinary function
composition and the commuting proofs are propositions.

## 2. Functors

> [!IMPORTANT]
> **Definition (functor).** A **functor** $F : \mathcal{C} \to \mathcal{D}$
> sends each object $X$ to an object $F X$, each morphism $f : X \to Y$ to a
> morphism $F f : F X \to F Y$, and satisfies
>
> ```math
> F(\mathrm{id}_X) = \mathrm{id}_{F X}, \qquad
> F(g \circ f) = F g \circ F f.
> ```

A functor is a *translation of structure*. It is the precise sense in which
one construction "is the same" in two different categories.

The main example is the graph-surface construction. A parameter chart
$\varphi$ is a map from UV coordinates to the parameter plane; the surface
chart is $\mathrm{graph}\thinspace h \circ \varphi$. The Lean functor is:

```lean
def toSurfaceFunctor (h : HeightFun) : ParamChart ⥤ Over Point3 where
  obj φ := chartObject h φ
  map f := chartTransition (h := h) f.f (by
    intro u
    exact congrArg (graph h) (congrFun f.comm u).symm)
  map_id φ := rfl
  map_comp f g := rfl
```

The two functor laws are `rfl` because `toSurface h` is definitionally
`graph h ∘ φ`, and the transition morphism is defined by the same
composition.

Other functors in the story:

| Functor | Source | Target | Status |
| --- | --- | --- | --- |
| `toSurfaceFunctor h` | `ParamChart` | `Over Point3` | defined, laws proved |
| `chartJacobian φ` | charts | `ModuleCat ℝ` | pointwise, chain rule is functoriality |
| `transportMap Γ γ` | paths | `ModuleCat ℝ` | pointwise, functoriality is `sorry` |
| `Free` | `Type` | `ModuleCat ℝ` | Mathlib |
| `UniversalEnvelopingAlgebra` | Lie algebras | associative algebras | Mathlib |

## 3. Natural transformations

> [!IMPORTANT]
> **Definition (natural transformation).** Given functors
> $F, G : \mathcal{C} \to \mathcal{D}$, a **natural transformation**
> $\eta : F \Rightarrow G$ is a family of morphisms
> $\eta_X : F X \to G X$, one for each object $X$, such that for every
> $f : X \to Y$,
>
> ```math
> G f \circ \eta_X = \eta_Y \circ F f.
> ```

The equation is the **naturality square**:

```math
\begin{array}{ccc}
F X & \xrightarrow{\eta_X} & G X \\
{\scriptstyle F f}\big\downarrow & & \big\downarrow{\scriptstyle G f} \\
F Y & \xrightarrow{\eta_Y} & G Y
\end{array}
```

A natural transformation is a *comparison that does not depend on the route*.
It is the categorical version of "this construction is compatible with
restriction".

### The metric as a natural transformation

Let $M$ be a manifold and let $\mathrm{Open}(M)$ be its poset of open sets,
viewed as a category (one morphism $V \to U$ when $V \subseteq U$). Define

```math
T(U) = \Gamma(U, T^*M \otimes T^*M), \qquad
C(U) = C^\infty(U).
```

Both are contravariant functors to $\mathbf{Type}$: a smaller open set
restricts a tensor field or a function. A Riemannian metric is a family of
maps

```math
g_U : T(U) \to C(U),
```

and the identity $g_V(\mathrm{res}_V s) = \mathrm{res}_V(g_U s)$ is exactly
naturality. In
coordinates, the value at a point is `gramMatrix h p`; the chart
pullback `pullbackGram h φ u` is the image of $g$ under the reparameterization
$\varphi$. The chain rule is what makes the pullback natural.

This is the cleanest answer to "where is the natural transformation in this
repository?" It is not an extra layer on top of the metric; it is the
statement that the metric is local and restricts correctly.

## 4. Adjunctions

> [!IMPORTANT]
> **Definition (adjunction).** An **adjunction** $F \dashv G$ between
> functors $F : \mathcal{C} \to \mathcal{D}$ and
> $G : \mathcal{D} \to \mathcal{C}$ consists of a unit
> $\eta : \mathrm{id}_{\mathcal{C}} \Rightarrow G \circ F$ and a counit
> $\varepsilon : F \circ G \Rightarrow \mathrm{id}_{\mathcal{D}}$ satisfying
> the triangle identities
>
> ```math
> \varepsilon_{F X} \circ F\eta_X = \mathrm{id}_{F X}, \qquad
> G\varepsilon_X \circ \eta_{G X} = \mathrm{id}_{G X}.
> ```

Adjunctions are *universal recipes*. The left adjoint is the "free" or
"most general" construction; the right adjoint is the "forgetful" or
"underlying" construction.

Three adjunctions in this story:

* **Free and forgetful vector spaces.** The functor
  $\mathrm{Free} : \mathbf{Type} \to \mathbf{Vect}_{\mathbb{R}}$ is left
  adjoint to the forgetful functor. A linear map out of a free vector space is
  determined by its values on a basis.
* **Currying and state.** The adjunction
  $(S \times -) \dashv (S \Rightarrow -)$ generates the state monad. The state
  $S$ is `Shoot.ShotState K`; the Kleisli arrows are the one-step integrators.
* **Universal enveloping algebra.** The functor
  $U : \mathbf{LieAlg}_{\mathbb{R}} \to \mathbf{Alg}_{\mathbb{R}}$ is left
  adjoint to the forgetful functor that regards an associative algebra as a
  Lie algebra with the commutator bracket. Mathlib's
  `UniversalEnvelopingAlgebra.lift` is the universal property. This is the
  correct categorical statement behind [`lie-algebra.md`](lie-algebra.md).

> [!WARNING]
> **The exponential map is not an adjunction.** On a normal neighbourhood it
> is a retraction of the zero section: $\exp \circ 0 = \mathrm{id}_M$ and
> $\pi \circ 0 = \mathrm{id}_M$. Sections and retractions are morphisms in a
> slice category, not adjunctions. The distinction matters when translating
> `expShoot` into categorical language.

## 5. Limits and colimits

> [!IMPORTANT]
> **Definition (terminal object).** An object $\mathbf{1}$ is **terminal**
> when there is exactly one morphism $X \to \mathbf{1}$ for every object $X$.
>
> **Definition (pullback).** A **pullback** of $f : X \to Z$ and $g : Y \to Z$
> is an object $X \times_Z Y$ with projections to $X$ and $Y$, universal among
> all commuting squares.
>
> **Definition (colimit).** A **colimit** of a diagram is an object that
> receives a compatible family of maps from the diagram, universal among all
> such cocones.

Limits are *gluing by mapping in*; colimits are *gluing by mapping out*. The
two examples that matter here are dual:

* In $\mathbf{Over}(X)$, the identity map $\mathrm{id}_X$ is terminal. A
  **section** of a bundle $p : E \to X$ is a morphism from $\mathrm{id}_X$ to
  $p$. This is the categorical definition of "a choice of point in each
  fibre".
* An **atlas** is a colimit. The chart domains $U_i$ are glued along the
  transition maps on the overlaps $U_i \cap U_j$; the surface is the colimit
  of that diagram. A map out of the surface is the same as a compatible
  family of maps out of the charts.

The first example is already formalized. The graph of a height function is a
section of the projection that forgets the height:

```lean
def graphBundle : Over Point2 := Over.mk (TypeCat.ofHom proj2)

def basePoint : Over Point2 := Over.mk (TypeCat.ofHom (id : Point2 → Point2))

def graphSection (h : HeightFun) : basePoint ⟶ graphBundle :=
  Over.homMk (TypeCat.ofHom (graph h)) (by
    refine ConcreteCategory.hom_ext _ _ ?_
    intro p
    exact proj2_graph h p)
```

`basePoint` is the terminal object; `graphSection h` is a morphism from it.
The proof is exactly `proj2 (graph h p) = p`.

The atlas colimit is *not* formalized yet. Section 7 of
[`chart-mapping.md`](chart-mapping.md) lists the chart API; the categorical
version of that list is a gluing category and a colimit cone. Part III says
what to add.

## 6. Monads and Kleisli arrows

> [!IMPORTANT]
> **Definition (monad).** A **monad** on a category $\mathcal{C}$ is an
> endofunctor $T : \mathcal{C} \to \mathcal{C}$ with natural transformations
> $\eta : \mathrm{id} \Rightarrow T$ and $\mu : T \circ T \Rightarrow T$
> satisfying the unit and associativity laws.
>
> A **Kleisli arrow** from $X$ to $Y$ is a morphism $X \to T Y$. Kleisli
> arrows compose using $\mu$.

For programming, the important monad is the **state monad**:

```math
\mathrm{State}(S, A) = S \to A \times S.
```

A value of this type reads a state, produces an output and a new state. A
one-step integrator is the special case $A = \mathbf{1}$: it maps a state to a
new state. Iterating the step is Kleisli composition.

The Lean module makes this literal for the Euler integrator:

```lean
abbrev StepM (K : Type) := StateM (Shoot.ShotState K) Unit

def eulerK (K : Type) [Shoot.GeoKernel K] [Add K] [Mul K] [Neg K] [Sub K] [Div K]
    (h : K → K → K) (dt : K) : StepM K :=
  fun s => ((), Shoot.eulerStep h s dt)

def runSteps {K : Type} (step : StepM K) (n : ℕ) : StepM K :=
  fun s => ((), Nat.iterate (fun t => (step t).2) n s)
```

The theorem `runSteps_euler` proves that the monadic iteration is the same as
the recursive `shoot`:

```lean
theorem runSteps_euler (K : Type) [Shoot.GeoKernel K] [Add K] [Mul K] [Neg K]
    [Sub K] [Div K] (h : K → K → K) (dt : K) (n : ℕ) (s₀ : Shoot.ShotState K) :
    (runSteps (eulerK K h dt) n s₀).2 =
      Shoot.shoot Shoot.eulerStep h s₀ dt n := by
  induction n generalizing s₀ with
  | zero => rfl
  | succ n ih =>
      change (fun t => Shoot.eulerStep h t dt)^[n + 1] s₀ =
        Shoot.eulerStep h (Shoot.shoot Shoot.eulerStep h s₀ dt n) dt
      rw [Function.iterate_succ_apply']
      rw [show (fun t => Shoot.eulerStep h t dt)^[n] s₀ =
        Shoot.shoot Shoot.eulerStep h s₀ dt n by
          simpa [runSteps, eulerK] using ih s₀]
```

The same template applies to `rk4Step`: define the analogous `rk4K` with
`rk4Step` in place of `eulerStep`; the proof is unchanged, because both are
values of `StepMethod K`.

## 7. Groupoids and transport

A groupoid is the categorical home of *reversible paths*. The path groupoid
of a space $X$ has points as objects and piecewise-smooth paths as morphisms,
up to reparameterization (or in a convenient strict model); composition is
concatenation, and the inverse is path reversal. The fundamental groupoid
$\Pi_1(X)$ is the quotient by homotopy.

Parallel transport is the motivating example:

* a connection $\nabla$ assigns to each path $\gamma$ a linear map
  $\mathrm{transport}(\gamma) : E_{\gamma(0)} \to E_{\gamma(1)}$;
* `transportMap Γ γ s t` is that map in coordinates;
* `transportMap_linear` says it is a morphism in $\mathbf{Vect}_{\mathbb{R}}$;
* `transportMap_reverse` says it is invertible;
* `holonomyGroup Γ p` is the image of the loop group at $p$.

The categorical statement is:

```math
\mathrm{transport} : \mathrm{PathGroupoid}(M) \to \mathbf{Vect}_{\mathbb{R}}.
```

A connection is **flat** when this functor is invariant under homotopy, i.e.
when it factors through $\Pi_1(M)$. The curvature is the obstruction to that
factorization. This is exactly the content of
[`connections.md`](connections.md) sections 5 and 6, written without the word
"functor".

The Lean code currently proves the pointwise pieces, not the functor. The
missing step is to define the path groupoid (or a sufficient subcategory of
it) and prove that `transportMap` respects composition and identities. Part
III lists this as the next formalization target.

## 8. Enriched categories

> [!IMPORTANT]
> **Definition (enriched category).** Let $(\mathcal{V}, \otimes, I)$ be a
> monoidal category. A category **enriched over** $\mathcal{V}$ has
> hom-objects $\mathrm{Hom}(X,Y)$ in $\mathcal{V}$, an identity morphism
> $I \to \mathrm{Hom}(X,X)$, and a composition morphism
> $\mathrm{Hom}(Y,Z) \otimes \mathrm{Hom}(X,Y) \to \mathrm{Hom}(X,Z)$.

The point of enrichment is that "how far apart" or "how linear" can be part
of the structure. Two examples:

* A **Lawvere metric space** is a category enriched over the monoidal poset
  $(\mathbb{R}_{\geq 0}^{\infty}, +, 0)$: the hom-object is the distance, the
  identity is $d(x,x) = 0$, and composition is the triangle inequality
  $d(x,z) \leq d(x,y) + d(y,z)$.
* A normed vector space is a Lawvere metric space: the distance is the norm
  of the difference. A short map is an enriched functor; an isometry is an
  enriched isomorphism.

This is the right language for the distortion predicates in
[`chart-mapping.md`](chart-mapping.md). An isometry is an enriched
isomorphism: an enriched functor that preserves the hom-objects exactly, so
its inverse is also enriched. A conformal map preserves them up to a scalar;
an equal-area map preserves the induced volume form. The predicates
`isIsometricAt`, `isConformalAt`, and `isEqualAreaAt` are the three
increasingly relaxed versions of the same comparison.

## 9. Yoneda

> [!IMPORTANT]
> **Yoneda lemma.** For a functor $F : \mathcal{C}^{\mathrm{op}} \to
> \mathbf{Set}$ and an object $X$,
>
> ```math
> \mathrm{Nat}(\mathrm{Hom}(-,X), F) \cong F X.
> ```
>
> In particular, $X$ is determined up to isomorphism by its functor of points
> $\mathrm{Hom}(-,X)$.

Yoneda is the categorical version of "an object is what it does". Three
consequences are useful here:

* A **point** of a manifold $M$ is a morphism $\mathbf{1} \to M$. The set of
  points is $\mathrm{Hom}(\mathbf{1}, M)$.
* In the algebraic (synthetic) sense, a **tangent vector** at $p$ is a
  morphism
  $\mathrm{Spec}\thinspace \mathbb{R}[\varepsilon]/(\varepsilon^2) \to M$,
  where $\varepsilon^2 = 0$. The dual-number object is the algebraic
  infinitesimal; the map is the derivative.
* A **chart** $U \to M$ is an element of $\mathrm{Hom}(U,M)$, hence by Yoneda
  a natural transformation
  $\mathrm{Hom}(-,U) \Rightarrow \mathrm{Hom}(-,M)$.

The last point is the precise sense in which a chart is a *representable*
piece of the manifold. The current Lean charts are global maps
`Point2 → Point3`; a local-chart formalization would make the representable
functor explicit on the site of open sets.

---

# Part II. The dictionary

The table is the short version; the subsections explain the entries that
carry the most weight.

| Category theory | In this repository | Lean name |
| --- | --- | --- |
| Category | charts and reparameterizations | `ParamChart`, `ParamChartHom` |
| Slice category | bundles over the parameter plane | `Over Point2`, `graphBundle` |
| Terminal object | identity map | `basePoint` |
| Section | graph of a height function | `graphSection` |
| Object of a slice | chart into ambient space | `chartObject` |
| Morphism of charts | reparameterization | `chartTransition` |
| Functor | graph-surface construction | `toSurfaceFunctor` |
| Module object | tangent space | `tangentModule` |
| Module morphism | chart Jacobian | `jacobianLin` |
| One-object category | multiplicative monoid $\mathbb{R}$ | `SingleObj ℝ` |
| Groupoid | nonzero reals under multiplication | `SingleObj ℝˣ` |
| Monad and Kleisli | Euler step iteration | `StepM`, `eulerK`, `runSteps` |
| Natural transformation | metric components and pullback | `gramMatrix`, `pullbackGram` |
| Colimit | atlas gluing | not yet formalized |
| Groupoid functor | parallel transport | `transportMap` (functoriality missing) |
| Enriched category | metric and distortion | `gramMatrix`, `isIsometricAt` |
| Adjunction | universal enveloping algebra | `UniversalEnvelopingAlgebra.lift` |

## 1. Charts are a category, and `toSurface` is a functor

This is the most direct application. A parameter chart is a map
$\varphi : \mathbb{R}^2 \to \mathbb{R}^2$. A reparameterization from
$\varphi$ to $\psi$ is a map $f$ with

```math
\varphi = \psi \circ f.
```

The direction is worth reading twice. The map $f$ changes the UV coordinates
*before* the chart $\psi$ is applied; the composite $\psi \circ f$ is the old
chart $\varphi$. In the Lean category, a morphism `f : φ ⟶ ψ` stores exactly
this equation:

```lean
structure ParamChartHom (φ ψ : ParamChart) where
  f : ParamChart
  comm : φ = ψ ∘ f
```

Composition is ordinary composition of the reparameterizations. The functor
`toSurfaceFunctor h` sends $\varphi$ to the surface chart
$\mathrm{graph}\thinspace h \circ \varphi$ and sends $f$ to the same
reparameterization viewed as a morphism in the slice over $\mathbb{R}^3$:

```math
\begin{array}{ccc}
\varphi & \xrightarrow{f} & \psi \\
 & {\scriptstyle \mathrm{toSurface}}\searrow & \big\downarrow{\scriptstyle \mathrm{toSurface}} \\
 & & \mathbb{R}^3
\end{array}
```

This is a triangle, not a square: a morphism in the slice over
$\mathbb{R}^3$ is a map of the total spaces over a fixed base. The triangle
commutes because
$\mathrm{toSurface}\thinspace h\thinspace \psi \circ f
= \mathrm{toSurface}\thinspace h\thinspace \varphi$, which is
$\mathrm{graph}\thinspace h$ applied to `f.comm`.

Why this matters: it turns "chart bookkeeping" into a reusable API. A
compatible family of charts is a diagram in this category; a change of chart
is a morphism; an invariant of charts is a functor. The distortion
predicates are not attached to a single chart; they are properties of the
functor `toSurface` at a point.

## 2. The graph is a section

The graph of $h$ is a map $\mathrm{graph}\thinspace h : \mathbb{R}^2 \to
\mathbb{R}^3$. The projection

```math
\mathrm{proj}_2(x,y,z) = (x,y)
```

forgets the height. The identity $\mathrm{proj}_2 \circ \mathrm{graph}\thinspace h
= \mathrm{id}$ says that the graph is a **section** of the projection.

In the slice category $\mathbf{Over}(\mathbb{R}^2)$:

* the terminal object is $\mathrm{id} : \mathbb{R}^2 \to \mathbb{R}^2$;
* the bundle is $\mathrm{proj}_2 : \mathbb{R}^3 \to \mathbb{R}^2$;
* a section is a morphism from the terminal object to the bundle.

The Lean names are `basePoint`, `graphBundle`, and `graphSection`. The
theorem `proj2_graph` is the entire proof obligation. This is a small example,
but it is the pattern for every bundle in the repository: a vector field is a
section of the tangent bundle, a connection is a rule for differentiating
sections, and a frame is a section of the frame bundle.

## 3. Tangent spaces are modules, and the Jacobian is a morphism

The tangent space at a point is a real vector space. In Lean it is the object

```lean
def tangentModule : ModuleCat ℝ := ModuleCat.of ℝ Vel2
```

of the category of real vector spaces. A chart Jacobian is a linear map, so it
is a morphism in the same category:

```lean
noncomputable def jacobianLin (φ : ParamChart) (u : Point2) :
    tangentModule ⟶ tangentModule :=
  ModuleCat.ofHom (Matrix.toLin' (chartJacobian φ u))
```

The chain rule is the functoriality statement: the Jacobian of a composite
chart is the composite of the Jacobians. In the notation of
[`chart-mapping.md`](chart-mapping.md), the pullback metric is

```math
\varphi^* g = J^{\mathsf T} G J,
```

which is the pullback of the bilinear form $G$ along the linear map
`jacobianLin`. The predicates `isConformalAt`, `isEqualAreaAt`, and
`isIsometricAt` compare this pullback to the Euclidean metric. In categorical
language, they measure how far the chart is from being an enriched
isomorphism (Section 8 of Part I).

## 4. Parallel transport is a functor from paths to vector spaces

This is the deepest application, and the one with the clearest missing Lean
step. A connection gives a linear map for each path:

```math
\mathrm{transport}(\gamma) : E_{\gamma(0)} \to E_{\gamma(1)}.
```

The path groupoid has points as objects and piecewise-smooth paths as
morphisms, up to reparameterization (or in a convenient strict model);
composition is concatenation, and the inverse is path reversal. The
assignment $\gamma \mapsto \mathrm{transport}(\gamma)$ is a functor to
$\mathbf{Vect}_{\mathbb{R}}$ exactly when

```math
\mathrm{transport}(\gamma_2 \cdot \gamma_1)
= \mathrm{transport}(\gamma_2) \circ \mathrm{transport}(\gamma_1),
\qquad
\mathrm{transport}(\mathrm{const}_p) = \mathrm{id}_{E_p}.
```

The first equation is the concatenation law; `transportMap_linear` says each
individual transport map is a linear morphism, so it is a morphism in
$\mathbf{Vect}_{\mathbb{R}}$. The second equation is the identity law.
Reversal gives the inverse, so the functor lands in invertible linear maps.
A flat connection is one whose transport depends only on the homotopy class
of the path; then the functor factors through $\Pi_1(M)$. The curvature is
the obstruction to that factorization.

The current Lean code has the pointwise map `transportMap`, the linearity
statement, the reverse-curve statement, and the holonomy set. What it does
not have is the **category of paths** and the **functor laws**. Adding them
would turn the `sorry`s in
[`connections.md`](connections.md) section 8 into a single structural
statement: "transport is a functor".

## 5. The integrator is a Kleisli arrow

The shooting loop is a stateful computation. The state is
`Shoot.ShotState K`; one step is a Kleisli arrow for the state monad; the
trajectory is the $n$-fold Kleisli composite. The theorem `runSteps_euler`
makes the equality with the recursive `shoot` explicit.

This is a useful refactor because it separates three concerns:

* **the step**: `eulerStep` or `rk4Step`, a pure state transition;
* **the iteration**: `runSteps`, a monadic fold;
* **the trajectory**: `shoot`, the recursive list of states.

The same separation appears in [`ode-numerics.md`](ode-numerics.md): the
differential equation defines the step, and the loop is generic.

## 6. The Lie algebra story

A Lie algebra is a vector space with a bilinear, alternating bracket satisfying
Jacobi. It is a **Lie object** in $\mathbf{Vect}_{\mathbb{R}}$, not a
one-object category: the bracket is not associative, so it cannot be
composition.

The categorical statements that do apply:

* $\mathfrak{so}(3)$ and $\mathbb{R}^3$ with the cross product are isomorphic
  as Lie algebras; `so3MatrixEquiv` is that isomorphism (the final equivalence
  is still a `sorry` in `LieAlgebra.lean`).
* The universal enveloping algebra $U(L)$ is left adjoint to the forgetful
  functor from associative algebras to Lie algebras. The universal property is
  `UniversalEnvelopingAlgebra.lift`: a Lie homomorphism $L \to A$ extends
  uniquely to an algebra homomorphism $U(L) \to A$.
* The one-object category construction is for **monoids**: `SingleObj ℝ` is
  the multiplicative monoid as a category, and `SingleObj ℝˣ` is a groupoid.
  It is a useful example of the definition, but it is not the Lie algebra.

This distinction is worth keeping straight when reading
[`lie-algebra.md`](lie-algebra.md): the bracket is an operation *inside* a
category of Lie objects, not the composition of a one-object category.

## 7. The atlas is a colimit

A manifold is not a single chart; it is a compatible family of charts. The
categorical statement is a colimit:

```math
M = \mathrm{colim}_{i \in I} U_i,
```

where the diagram contains the chart domains $U_i$, the overlaps
$U_i \cap U_j$, and the transition maps between them. The universal property
says that a map $M \to X$ is the same as a family of maps $U_i \to X$ that
agree on every overlap.

This is the right formalization target for the chart API. The current code
has global charts `Point2 → Point3`; a local-chart version would define the
gluing category, the cocone, and the universal property. The payoff is that
"atlas", "transition map", and "compatible family" become one construction
instead of three ad hoc definitions.

## 8. Metric naturality and enrichment

The metric is a natural transformation on the poset of opens (Section 3 of
Part I). The pullback metric is its image under a chart. The three distortion
predicates are three levels of comparison:

| Predicate | Categorical reading |
| --- | --- |
| `isIsometricAt` | the chart is an enriched isomorphism (an isometry) |
| `isConformalAt` | the chart preserves the enriched hom up to a scalar |
| `isEqualAreaAt` | the chart preserves the induced volume form |

A Lawvere metric space is an enriched category over
$\mathbb{R}_{\geq 0}^{\infty}$. The graph metric gives a local enrichment of
the parameter plane; an isometric chart is an enriched isomorphism between
the parameter plane and the surface. This is a clean way to say "the chart
does not distort distances" without introducing a separate notion of
distortion.

## 9. Yoneda and the functor of points

A point is a morphism $\mathbf{1} \to M$. A tangent vector is a morphism
from the dual-number object. A chart is an element of $\mathrm{Hom}(U,M)$,
hence a natural transformation between representable functors. These are not
just analogies: they are the same definitions in the category of spaces.

The practical consequence is that **a chart is determined by what it does to
points**. This is why the Lean API can get away with functions
`Point2 → Point3` and still call them charts: the functor of points of
`Point2` is the set of parameter pairs, and the chart is the induced map on
those points. A local-chart formalization would make the open set $U$
explicit, but the Yoneda content is already there.

---

# Part III. What to formalize next

The following list is ordered by how much categorical structure it unlocks
per line of Lean code.

1. **The chart category and the `toSurface` functor.** *Done.*
   `ParamChart` is a category, `toSurfaceFunctor h` is a functor to
   `Over Point3`, and the functor laws are proved.
2. **The graph as a section.** *Done.* `graphSection h` is a morphism from
   the terminal object of `Over Point2` to the projection `proj2`.
3. **The state monad of the integrator.** *Done.* `runSteps_euler` proves
   that Kleisli iteration is `Shoot.shoot`.
4. **The transport functor.** *Next.* Define the path groupoid of `Point2`
   (or a subcategory closed under the curves used in the code), define
   `transportFunctor : PathGroupoid Point2 ⥤ ModuleCat ℝ`, and prove the
   functor laws from `transportMap_linear` and `transportMap_reverse`.
   Then state flatness as factorization through `FundamentalGroupoid Point2`,
   and identify `vbcCurvature` as the obstruction.
5. **The metric as a natural transformation.** *Next.* Define the poset of
   opens of `Point2`, the contravariant functors of tensor fields and smooth
   functions, and the natural transformation whose value at a point is
   `gramMatrix`. Prove that `pullbackGram` is the pullback of that natural
   transformation along a chart. The chain rule is the only analytic input.
6. **The atlas as a colimit.** *Next.* Define the gluing category of a finite
   atlas, its cocone to the surface, and the universal property. Start with
   two charts and the overlap; the general case is the same diagram with more
   indices.
7. **The Lawvere enrichment.** *Next.* Define the
   $\mathbb{R}_{\geq 0}^{\infty}$-enriched category structure on `Point2`
   using the graph metric, and prove that `isIsometricAt` is the statement
   that the chart is an enriched isomorphism. This gives the distortion
   predicates a uniform home.
8. **The Lie algebra adjunction.** *Next.* Connect
   `UniversalEnvelopingAlgebra.lift` to `Brane.Lie.crossLieAlgebra`; state
   the adjunction between Lie algebras and associative algebras, and show
   that the cross-product Lie algebra is the concrete instance.

---

# Part IV. Proven vs. declared

| Result | Lean name | Status |
| --- | --- | --- |
| Projection forgets the height | `proj2_graph` | proved |
| Graph is a section | `graphSection` | definition |
| Chart is an object of the slice | `chartObject` | definition |
| Reparameterization is a slice morphism | `chartTransition` | definition |
| Parameter charts form a category | `ParamChart` | instance, proved |
| Graph-surface construction is a functor | `toSurfaceFunctor` | definition, laws proved |
| Tangent space is a module | `tangentModule` | definition |
| Jacobian is a module morphism | `jacobianLin` | definition |
| Monoid as a one-object category | `SingleObj ℝ` | instance |
| Group as a one-object groupoid | `SingleObj ℝˣ` | instance |
| Euler step is a Kleisli arrow | `eulerK` | definition |
| Kleisli iteration is `shoot` | `runSteps_euler` | proved |
| Transport is a functor | — | not yet |
| Metric is a natural transformation | — | not yet |
| Atlas is a colimit | — | not yet |
| Isometry is an enriched isomorphism | — | not yet |

The pattern is the same as in the other notes: the algebraic and
category-theoretic infrastructure is proved; the analytic bridges (ODE
existence, chain rule for the metric, gluing) are the deliberate `sorry`s or
the next targets.

---

# Part V. Cheat sheet

| Category theory | Plain language | Where it lives |
| --- | --- | --- |
| Category | objects and composable maps | `ParamChart`, `Over Point2`, `ModuleCat ℝ` |
| Functor | a construction that respects maps | `toSurfaceFunctor`, `chartJacobian` |
| Natural transformation | a compatible family of comparisons | `gramMatrix` on opens, `pullbackGram` |
| Adjunction | a free construction and its forgetful partner | `Free ⊣ Forget`, `U ⊣ Forget` |
| Terminal object | the trivial bundle | `basePoint` |
| Section | a graph, a vector field, a frame | `graphSection` |
| Pullback | a fibre or an overlap | not yet formalized |
| Colimit | an atlas glued from charts | not yet formalized |
| Monad | a notion of stateful computation | `StepM` |
| Kleisli arrow | one step of a state machine | `eulerK`, `rk4Step` |
| Groupoid | invertible paths | `SingleObj ℝˣ`, `Π_1` |
| Enriched category | distances or norms as hom-objects | Lawvere metric, `isIsometricAt` |
| Yoneda | an object is its functor of points | points, tangent vectors, charts |

---

# Part VI. Open questions

* Should a chart be an object of `Over Point3` (a global map) or an object of
  a slice over an open subset of the parameter plane? The local version is
  more faithful, but it requires a site of opens and a sheaf condition.
* What is the right category of height functions? Reparameterizations alone
  give the chart category; adding a morphism $h \to h'$ when
  $h' \circ f = h$ would make the graph construction functorial in $h$ as
  well.
* Is the atlas a colimit in $\mathbf{Top}$, in $\mathbf{Over}
  \mathbb{R}^3$, or in a category of locally ringed spaces? The answer
  depends on how much structure the charts carry.
* Can the transport functor be defined on the path groupoid without
  quotienting by homotopy? Yes: use paths themselves as morphisms. Flatness is
  the extra statement that the functor descends to $\Pi_1$.
* Which enrichment is right for distortion? Strict isometry is an enriched
  isomorphism over $\mathbb{R}_{\geq 0}^{\infty}$; conformal maps are enriched
  up to a scalar, which is a different (weaker) structure.
* How does the state monad interact with the `GeoKernel` polymorphism? The
  monad is uniform in the number type `K`; the `Float` and `ℝ` kernels are
  two instances of the same Kleisli arrow. This is the categorical explanation
  of why the figure generator and the proofs share one pipeline.

---

## References

### Category theory

* Saunders Mac Lane, *Categories for the Working Mathematician*, 2nd ed.,
  Springer, 1998.
* Emily Riehl, *Category Theory in Context*, Dover, 2016.
* Bartosz Milewski, *Category Theory for Programmers*, 2018 — the monad and
  Kleisli chapters are the most relevant here.
* Wikipedia, [Category (mathematics)](https://en.wikipedia.org/wiki/Category_(mathematics))
* Wikipedia, [Functor](https://en.wikipedia.org/wiki/Functor)
* Wikipedia, [Natural transformation](https://en.wikipedia.org/wiki/Natural_transformation)
* Wikipedia, [Adjoint functors](https://en.wikipedia.org/wiki/Adjoint_functors)
* Wikipedia, [Limit (category theory)](https://en.wikipedia.org/wiki/Limit_(category_theory))
* Wikipedia, [Monad (category theory)](https://en.wikipedia.org/wiki/Monad_(category_theory))
* Wikipedia, [Groupoid](https://en.wikipedia.org/wiki/Groupoid)
* Wikipedia, [Enriched category](https://en.wikipedia.org/wiki/Enriched_category)
* Wikipedia, [Yoneda lemma](https://en.wikipedia.org/wiki/Yoneda_lemma)

### Mathlib

* `Mathlib.CategoryTheory.Category.Basic` — categories, functors, natural
  transformations.
* `Mathlib.CategoryTheory.Comma.Over.Basic` — slice and coslice categories.
* `Mathlib.CategoryTheory.SingleObj` — monoids and groups as one-object
  categories.
* `Mathlib.Algebra.Category.ModuleCat.Basic` — the category of modules.
* `Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic` — the fundamental
  groupoid.
* `Mathlib.Algebra.Lie.UniversalEnveloping` — the universal enveloping
  algebra and its universal property.

### This repository

* [`shooting-method.md`](shooting-method.md) — the graph surface, the
  geodesic equation, and the integrator.
* [`connections.md`](connections.md) — affine connections, Christoffel
  symbols, parallel transport, and curvature.
* [`chart-mapping.md`](chart-mapping.md) — charts, pullback metrics,
  distortion, and projection families.
* [`lie-algebra.md`](lie-algebra.md) — the cross product as a Lie algebra and
  the isomorphism with $\mathfrak{so}(3)$.
* [`lean/Brane/CategoryTheory.lean`](../lean/Brane/CategoryTheory.lean) — the
  categorical companion formalized in this note.
