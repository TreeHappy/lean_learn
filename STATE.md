# Project state

A running log of where the project stands, so any session can pick up here.
Last updated: 2026-11-23.

## Repo & infrastructure

- Repo: https://github.com/TreeHappy/lean_learn (public, branch `master`).
- Two sibling Lake packages, both on Lean/Mathlib `v4.34.0`
  (downgraded from v4.35.0 for the vendored Vizagrams figure generator —
  see `docs/figures.md`):
  - `lean/` — Mathlib code package (`lakefile.toml` pins Mathlib v4.34.0;
    the `mathlib` require must stay last in the file, see comment there).
  - `notes/` — Verso Manual (subverso pinned to the Verso v4.35.0 revision;
    may need a v4.34-matching rev if the notes build breaks).
- `make lean`, `make notes`, `make serve`, `make figures` all work.
  Intentional `sorry`s: `Brane.Exercises.zero_add_exercise`, the documented
  exercise `sorry`s in `Brane/Shooting.lean`, the geometric bridges in
  `Brane/GADiffGeom.lean`, and the new inventories in
  `Brane/Connections.lean`, `Brane/ParallelTransport.lean`, and
  `Brane/LieAlgebra.lean` (listed below).
- GitHub Pages is enabled from the `gh-pages` branch:
  <https://treehappy.github.io/lean_learn/> (redirects to the interactive
  surface viewer at `/interactive/surface.html`).
- `.github/workflows/pages.yml` syncs `notes/interactive/*.html` to
  `gh-pages` on every push to `master`.

## Lean library (`lean/`)

- `Brane/Basic.lean` — intro material, quoted by the notes via anchors.
- `Brane/Exercises.lean` — exercises (contains the intentional `sorry`).
- `Brane/DifferentialGeometry.lean` — the main development so far, in
  namespace `Brane.DiffGeom`:
  - Type abbrevs: `Vec3 = EuclideanSpace ℝ (Fin 3)`, `Mat32`, `Mat22`,
    `Vel2`.
  - Graph map `graph h p = (x, y, h x y)`; tangents `tangentX/Y`, their
    second derivatives `tangentXX/XY/YX/YY`; `normal` via Mathlib
    `crossProduct` (transported across `WithLp`).
  - `tangentSpace` as `Submodule ℝ Vec3` (`finrank = 2`,
    `LinearIndependent.pair_iff`, `Submodule.span_induction`).
  - Jacobians: `jacobian`, `jacobianTangentX/Y`, `hessian`.
  - Gram matrix `gramMatrix = Jᵀ * J`; `det_gramMatrix = ‖normal‖²`
    (Lagrange identity `cross_dot_cross`); first fundamental form
    `det_gramMatrix_eq = 1 + fx² + fy²`.
  - Vector calculus: `gradient`, `directionalDerivative`, `divergence`
    (Laplacian), `curl` (mixed-partials), `curl_eq_zero_of_eq`.
  - Examples with full derivative simp sets: `planeHeight`, `bowlHeight`
    (paraboloid), `saddleHeight`.
  - Definitions are separated from proofs in the file for readability.

## Interactive viewer (`notes/interactive/surface.html`)

- Single-file Three.js (CDN) page, no build step.
- First-person walk on the height surface: `↑/↓` walk, `←/→` turn in place.
- Toggleable overlays mapping 1:1 to Lean defs: `T` tangents, `N` normal,
  `G` gradient, `S` second-derivative vectors, `W` wireframe, `O` orbit
  camera, `L` Lean reference panel, `1..n` switch surface.
- Extensible `SURFACES` registry; currently only `bowl` (paraboloid,
  matches `Brane.DiffGeom.bowlHeight`). Coordinates: three.js (x, height,
  y); HUD prints vectors in Lean order.

## Geometric algebra layer

- `lean/Brane/GeometricAlgebra.lean`, namespace `Brane.GA`, built on
  Mathlib's `CliffordAlgebra` (GA = Clifford algebra over the Euclidean
  quadratic form on `Vec3`); imports `Brane.DifferentialGeometry` and
  reuses its `Vec3`, `vec3`, `vec3_inner`, `cross`. **Done and committed:**
  1. `quadVec : QuadraticForm ℝ Vec3` via `QuadraticMap.ofPolar`
     (`Q v = ⟪v, v⟫`); `quadVec_apply`.
  2. `abbrev GA3 := CliffordAlgebra quadVec`; `embed : Vec3 → GA3` (=
     `CliffordAlgebra.ι`); `embed_add/smul/zero/neg`; `embed_sq : v² =
     ⟪v,v⟫` (via `ι_sq_scalar`).
  3. Fundamental identity `embed_mul_add : uv + vu = 2⟪u,v⟫` — proved by
     showing the defect is additive + homogeneous in `v` and vanishes on
     the orthonormal basis `e0, e1, e2` (each from `(u+e)² = ⟪u+e,u+e⟫`).
  4. Basis `e0/e1/e2` + `vec3_eq_smul`; pair inner products; anticommutation
     `embed_anti` (`vw = -uv` for orthogonal vectors).
  5. Pseudoscalar `I = e₀e₁e₂`; `I_sq : I * I = -1`; Hodge duals on the
     basis: `e0_mul_I = e1e2`, `e1_mul_I = -(e0e2)`, `e2_mul_I = e0e1`.
  6. **`embed_mul_dual` (main theorem): `uv = ⟪u,v⟫ + (u × v) · I`** —
     defect bilinear in `(u, v)`, vanishes on the nine basis pairs;
     needed `cross_add/smul` (both sides), `cross_self`, and cyclic basis
     crosses `cross_e0_e1 = e2`, `cross_e1_e2 = e0`, `cross_e2_e0 = e1`.
  7. Proof-engineering notes (for future work in this layer): GA3 is
     noncommutative — use `abel` / `noncomm_ring`, never `ring`;
     `linear_combination` needs a commutative ring, so rearrangement is
     done with explicit `rw` chains (always pass explicit args to
     `mul_assoc` — unqualified `rw` picks the outermost match);
     `add_eq_zero_iff_eq_neg.mp` converts `a + b = 0` to `b = -a`;
     `map_neg` etc. don't match plain-function `embed` (only `ι`-coe
     shapes) — use the local `embed_neg`.
- Remaining milestones (from the original plan): grade projections,
  blades as subspace carriers (`tangentX ∧ tangentY` = tangent plane,
  `‖blade‖² = det gramMatrix`), rotors/versors for camera math.

## Connections, parallel transport, and Lie algebras

- `lean/Brane/Connections.lean`, namespace `Brane.Conn` — the affine
  connection layer on the parameter plane:
  - `ParamField = Point2 → Vel2`, `dirDeriv` via `fderiv`;
  - `AffineConnection` with the two Wikipedia axioms (additive /
    `C∞`-linear in `X`, Leibniz in `Y`); `flatConn` proved;
  - `metricPartial`, `christoffel` (symbols of the second kind from a
    metric), `christoffelCorr`, `covOfChristoffel`, `leviCivita h` from
    `gramMatrix h`; `christoffel_symm` proved;
  - `lieBracketParam`, `torsion`, `curvature`;
  - `VectorBundleConnection F`, `affineAsVectorBundle`, `vbcCurvature`,
    and the dual/tensor/endomorphism connections as existence theorems.
  - Proved: directional-derivative linearity, flat-connection axioms,
    Christoffel-correction bilinearity, Christoffel symmetry, the
    `covOfChristoffel` axioms.
  - `sorry`: `leviCivita_torsion_free`, `leviCivita_metric_compatible`,
    `torsion_anti`, `curvature_tensorial`, `leviCivita_unique`,
    `dualConn_exists`, `tensorConn_exists`, `endConn_exists`.
- `lean/Brane/ParallelTransport.lean`, namespace `Brane.Trans`:
  - `Curve`, `FieldAlong`, `curveVelocity`, `covAlongChristoffel`,
    `isParallel`, `parallelTransport_exists`, `parallelTransport`,
    `transportMap`, `reverseCurve`, `holonomyGroup`, `isGeodesic`,
    `curveAccel`.
  - `parallelTransport` is `Classical.choose` from the existence theorem;
    its initial condition and parallel equation are proved.
  - `sorry`: `parallelTransport_exists`, `transportMap_linear`,
    `transportMap_reverse`, `id_mem_holonomyGroup`,
    `isGeodesic_leviCivita_iff_Shoot`.
- `lean/Brane/LieAlgebra.lean`, namespace `Brane.Lie`:
  - `Vec3` with the cross product as `Bracket`; `crossLieRing`,
    `crossLieAlgebra`; `bracket_jacobi` and `bracket_leibniz` proved
    (coordinates + `fin_cases`/`ring`); `crossAdjoint`,
    `crossAdjoint_leibniz`; `hatMatrix`, `hatMatrix_mem_so`,
    `hatMatrix_commutator`; `matrix_bracket_eq_commutator`, `mem_so_iff`,
    `mem_sl_iff`, `derivation_leibniz`.
  - `sorry`: `so3MatrixEquiv` (`Vec3 ≃ₗ⁅ℝ⁆ so(3)`).
- Docs: `docs/connections.md`, `docs/lie-algebra.md`; bibliography in
  `references.bib` with a human-readable index in `bibtex.md`.

## Conventions

- Commits: conventional short messages; push to `master` after each unit.
- Scratch/prototyping happens in `lean/Scratch.lean` (gitignored-ish: it
  must not be committed); delete or clean it before committing.
- Single-file fast check: `cd lean && ~/.elan/bin/lake env lean FILE.lean`.
- Notes quote `lean/` via Verso anchors (`-- ANCHOR: name` /
  `-- ANCHOR_END: name`), so anchor contents must match exactly.

## Next steps

1. Finish the GA scaffold (steps 1–6 above), integrate as
   `lean/Brane/GeometricAlgebra.lean`, import from `Brane.lean`.
2. Consider a `notes/Notes/` chapter for the GA layer + viewer.

## Figure pipeline (new)

- Toolchain downgraded to Lean/Mathlib v4.34.0; vendored Vizagrams
  (`lean/Vizagrams/`, upstream 68931c4, one Mathlib-import patch).
- `lean/Brane/Figures/{Basic,ShootingFigures,Gen}.lean` +
  `lake exe gen-figures` (`make figures`) generate all `docs/figures/*.svg`
  (Catppuccin Latte) — computed by the *actual* pipeline: `Shooting.lean` is
  polymorphic over a `GeoKernel` number-type class (ℝ via Mathlib `deriv`,
  Float via central differences), so the figures run the very
  `Shoot.shoot`/`eulerStep`/`rk4Step`/`bowlHeight` the docs cite. The old
  Float mirror `Figures/Numeric.lean` is deleted. Docs: `docs/figures.md`.
- Replaced the old Node generator `docs/figures/gen-figures.mjs`.
- Not yet re-verified: the `notes/` Verso build on v4.34.0.
