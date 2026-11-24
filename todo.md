# TODO — porting the C++ / Haskell math stack to Lean

This file tracks what still needs to be imported (i.e. re-implemented in
Lean) from the two reference libraries, and the open `sorry`s in the
geometric-algebra bridge.

- Terathon Math Library — <https://github.com/EricLengyel/Terathon-Math-Library>
  (C++, MIT): vectors, matrices, quaternions, and projective / rigid /
  conformal geometric algebra.
- flex — <https://github.com/mixphix/flex> (**Haskell**, BSD-2-Clause, not
  C++): an alternative numeric hierarchy (`Num`/`Floating` replacement),
  dual numbers, quaternions, `Perplex` (perplex numbers / split-complex),
  `Minkowski` numbers, bilinear/sesquilinear forms, lenses/optics, Lawvere
  theories.

Status legend: ✅ already covered · 🟡 partially covered · ⬜ to port

## 1. Terathon Math Library → Lean

### Core linear algebra (`TSVector2D/3D/4D`, `TSMatrix2D/3D/4D`)

| Terathon class | Lean target | Status | Notes |
|---|---|---|---|
| `Vector2D/3D/4D` | `DiffGeom.vec3` / `EuclideanSpace` / `Matrix (Fin n) ℝ` | ✅ | Mathlib `PiLp` / `Fin n → ℝ` |
| swizzling (`v.yzx`, `.xy`) | n/a | ⬜ | compile-time sugar; in Lean use projection functions if ever needed |
| `Point2D/3D` (affine points, `w = 1`) | `ℝ × ℝ` params + `DiffGeom.graph` | 🟡 | we model affine points as pairs + the graph lift; a homogeneous `Point4D` type is not needed yet |
| `Matrix2D/3D/4D`, `Transform2D/3D` | `Mathlib.Matrix` | ✅ | `Mat22`, `Mat32` in `DiffGeom`; general matrices free from Mathlib |
| `TSSimd` | n/a | ⬜ | performance-only; no Lean analogue intended |

### Quaternions and dual numbers

| Terathon class | Lean target | Status | Notes |
|---|---|---|---|
| `Quaternion` | `Mathlib.Quaternion` | ✅ | Mathlib has quaternions with norm, conjugation, rotation action |
| `DualNum` (`s + tε`) | `Mathlib.DualNumber` (check exact module) | 🟡 | dual numbers exist in Mathlib for jet/tangent-line work; verify the API covers `Transform()`-style sandwich use |

### Rigid geometric algebra (`TSRigid2D/3D`, `TSFlatPoint3D`, `TSLine3D`, `TSPlane3D`, `TSMotor3D`, `TSFlector3D`)

The PGA `Cl(3,0,1)` — the biggest and most valuable port for us, since
`Shooting.lean` and the surface code want motors for placement and
reflection-based intersection.

| Terathon class | Lean target | Status | Notes |
|---|---|---|---|
| `FlatPoint2D/3D` | `Brane.PGA` | ✅ | vectors of `Cl(2,0,1)` / `Cl(3,0,1)`; `flatPoint2`, `flatPoint3`, `flatPoint3WithWeight` build the concrete blades |
| `Line2D/3D` | `Brane.PGA` | ✅ | `line2` uses `e₂₃, e₃₁, e₁₂`; `line3` uses `e₄₁, e₄₂, e₄₃` plus the same moment blades |
| `Plane3D` | `Brane.PGA` | ✅ | `plane3` on the trivector basis `e₂₃₄, e₃₁₄, e₁₂₄, e₃₂₁` |
| `Motor2D/3D` | `Brane.PGA` | ✅ | `motor2`, `motor3`, `identityMotor2/3`; the action is `Brane.PGA.sandwich Q p = Q p Q̰`, with `transform2/3` wrappers |
| `Flector2D/3D` | `Brane.PGA` | ✅ | `flector2`, `flector3`; reflections use the same sandwich (`reflectPoint3`) |
| `TSAlgebra` (the generic bracket-based GA engine) | `Brane.PGA.TSAlgebra` | ✅ | alias for `CliffordAlgebra`; Lean provides the symbolic expansion directly |

### Conformal geometric algebra (`TSConformal2D/3D`, `TSRoundPoint3D`, `TSDipole3D`, `TSCircle3D`, `TSSphere3D`)

| Terathon class | Lean target | Status | Notes |
|---|---|---|---|
| `RoundPoint2D/3D` | `Brane.CGA` | ✅ | `roundPoint2/3`; the Terathon two-null model is used (2D: `e₃²=e₄²=0`, `e₃·e₄=-1`; 3D: `e₄²=e₅²=0`, `e₄·e₅=-1`), so round points are proved null (`roundPoint2_sq`, `roundPoint3_sq`) |
| `Dipole2D/3D`, `Circle2D/3D`, `Sphere3D` | `Brane.CGA` | ✅ | concrete blade constructors `dipole2`, `dipole3`, `circle2`, `circle3`, `sphere3` matching the Terathon README components |

All of these are re-exported under the C++ spelling by
`lean/Brane/Terathon.lean` (`Brane.Terathon`), which also provides the
Mathlib aliases for `Vector2D/3D/4D`, `Point2D/3D`, `Matrix2D/3D/4D`,
`Transform2D/3D`, `Quaternion`, and `DualNum`.

### What we already have (for orientation)

- `Brane.DiffGeom`: graph surfaces, tangents, normal, Jacobian, Gram
  matrix, Hessian, gradient/divergence/curl — all proved.
- `Brane.GA`: `Cl(ℝ³)` with `embed`, `uv + vu = 2⟪u,v⟫`, anticommutation,
  pseudoscalar `I` (`I² = -1`), and `uv = ⟪u,v⟫ + (u × v)·I` — all proved.
- `Brane.GADiffGeom`: GA↔vector dictionary for the surface geometry —
  definitions real, bridge theorems `sorry` (see §3).
- `Brane.Shoot`: shooting geodesics on graphs (Euler + RK4 steppers).

## 2. flex (Haskell) → Lean

Priority items worth stealing concepts from (not code — Haskell idioms
don't map directly, and Lean/Mathlib already fixes the numeric hierarchy
problem that flex complains about):

| flex module | Lean analogue | Status | Notes |
|---|---|---|---|
| `Flex.Math.Numbers` (numeric tower fix) | Mathlib typeclasses | ✅ | Lean's `OfScientific`/`Ring`/`Field` hierarchy already solves this |
| `Dual`, `Perplex`, `Quaternion`, `Minkowski` number systems | `Mathlib` (dual numbers, quaternions), new for Perplex/Minkowski | 🟡 | `Perplex` = split-complex `ℝ[x]/(x²−1)`; `Minkowski` = the `Cl(1,1)`-style 2D algebra — both are one-line `Polynomial`/`CliffordAlgebra` instances if ever needed |
| bilinear / sesquilinear forms | `Mathlib.LinearAlgebra.BilinearForm` | ✅ | plus our `gramMatrix` usage |
| lenses / optics | none needed yet | ⬜ | skip unless we build a big tactic-heavy codebase |
| Lawvere theories (`Flex.Math.Structure`) | Mathlib `CategoryTheory` | ⬜ | very low priority |

## 3. Open `sorry`s — prove that GA diff-geo = vector diff-geo

File `lean/Brane/GADiffGeom.lean` (all definitions are real; every bridge
theorem is an empty proof waiting for you). Suggested order:

1. `dotGA_eq` — `dotGA u v = algebraMap ℝ GA3 ⟪u, v⟫`.
   Direct consequence of `GA.embed_mul_add` plus `halves_recombine`.
2. `wedgeGA_dual` — `wedgeGA u v = embed (cross u v) * I`.
   Direct consequence of `GA.embed_mul_dual` + `dotGA_eq`.
3. `dotGA_of_wedge` — recovery formula of your choice (e.g. via `I⁻¹`).
4. `bladeNormSq_eq` — `-B² = ‖normal h p‖²`; hint in the docstring
   (`B = N I`, use `GA.I_sq` and `DiffGeom.norm_sq_normal`).
5. `wedgeGA_tangentCombination` — bilinearity of `wedgeGA` +
   `wedgeGA_self`.
6. `mem_tangentSpace_iff_wedge` — combine 5 with
   `DiffGeom.mem_tangentSpace_iff`.
7. `tangentBlade_ne_zero` — via `tangentBlade_dual` +
   `DiffGeom.normal_ne_zero` + injectivity-ish of the dual.
8. `dotGA_tangent_second` — tangents ⊥ second derivatives; use
   `DiffGeom` orthogonality facts + `gprod_split`.
9. `wedgeGA_second_tangent` — the GA shape-operator input; this is the
   quantity the Gram-inverse in `Brane.Shoot.geoAccel` consumes, so it is
   the link between the shooter and GA.

## 4. Open `sorry`s — connections, transport, Lie algebras

The new modules are real definitions with the geometric bridges left open.

### `lean/Brane/Connections.lean` (`Brane.Conn`)

1. `leviCivita_torsion_free` — expand `torsion (leviCivita h)`, use
   `christoffel_symm` and symmetry of mixed partials.
2. `leviCivita_metric_compatible` — differentiate `Y ⬝ᵥ (G Z)` and use
   `christoffel` being the metric connection; this is the `∂g = Γ + Γ`
   identity.
3. `torsion_anti`, `curvature_tensorial` — unfold and use
   antisymmetry of `lieBracketParam`.
4. `leviCivita_unique` — the fundamental theorem of Riemannian geometry;
   compare two torsion-free metric connections.
5. `dualConn_exists`, `tensorConn_exists`, `endConn_exists` — construct
   the induced connections from the product rules; the formulas in the
   statements determine the definitions.

### `lean/Brane/ParallelTransport.lean` (`Brane.Trans`)

1. `parallelTransport_exists` — Picard–Lindelöf for the linear ODE
   `V̇ + Γ(γ̇, V) = 0`; uniqueness gives well-definedness.
2. `transportMap_linear` — linearity of the solution in the initial
   vector (superposition).
3. `transportMap_reverse` — the reversed curve gives the inverse
   transport; use uniqueness.
4. `id_mem_holonomyGroup` — the constant loop transports identically
   (again uniqueness).
5. `isGeodesic_leviCivita_iff_Shoot` — the Christoffel-symbol geodesic
   equation is the matrix equation `γ̈ = Shoot.geoAccel h γ γ̇`; combine
   the metric-compatibility computation with `Shoot.geoAccel_eq_matrix`.

### `lean/Brane/LieAlgebra.lean` (`Brane.Lie`)

1. `so3MatrixEquiv` — define the inverse of `hatMatrix` by reading off
   `(A₂₁, A₀₂, A₁₀)` and prove bracket preservation using
   `hatMatrix_commutator`.

## 5. Later ideas

- GA shooting: restate `Shoot.geoAccel` as a GA sandwich
  (`bladeNormSq`-normalized projection), then prove the matrix form and
  the GA form agree — this makes the "same vector math" claim concrete
  for the integrator.
- PGA motors for muzzle placement (`muzzle` in `Shooting.lean`) so shots
  can be posed by sandwich products instead of coordinate bookkeeping.
- CGA spheres for hit-detection against the surface's second-order
  curvature data.
