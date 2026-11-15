# Project state

A running log of where the project stands, so any session can pick up here.
Last updated: 2026-11-15.

## Repo & infrastructure

- Repo: https://github.com/TreeHappy/lean_learn (public, branch `master`).
- Two sibling Lake packages, both on Lean/Mathlib `v4.35.0`:
  - `lean/` — Mathlib code package (`lakefile.toml` pins Mathlib v4.35.0).
  - `notes/` — Verso Manual (subverso v4.35.0).
- `make lean`, `make notes`, `make serve` all work. Only intentional
  `sorry`: `Brane.Exercises.zero_add_exercise`.
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

## Geometric algebra layer — IN PROGRESS

- Goal: `lean/Brane/GeometricAlgebra.lean`, namespace `Brane.GA`, built on
  Mathlib's `CliffordAlgebra` (GA = Clifford algebra over the Euclidean
  quadratic form on `Vec3`). Reference: Mathlib `CliffordAlgebra.*`;
  third-party [`pygae/lean-ga`](https://github.com/pygae/lean-ga) as design
  reference (not directly usable, Lean 3-era).
- Plan / milestones:
  1. `quadVec : QuadraticForm ℝ Vec3` via `QuadraticMap.ofPolar`
     (`Q v = ⟪v, v⟫`). **Do this on `Vec3` (EuclideanSpace), NOT on
     `Fin 3 → ℝ` — the plain function type has no `Inner` instance.**
  2. `abbrev GA := CliffordAlgebra quadVec`; `embed : Vec3 →ₗ[ℝ] GA` :=
     `CliffordAlgebra.ι`; `embed_sq : embed v * embed v = ⟪v,v⟫ • 1` from
     `ι_sq_scalar`.
  3. Fundamental identity `embed u * embed v + embed v * embed u =
     (2 * ⟪u, v⟫) • 1`. Proof idea: linearity in `v` + diagonal case
     (`embed_sq`) + basis expansion of `v` in `e₀,e₁,e₂`.
  4. Orthonormal basis `ebasis : Fin 3 → Vec3` with `embed (ebasis i)² =
     1` and anti-commutation `eᵢ eⱼ = -eⱼ eᵢ` (`i ≠ j`).
  5. Pseudoscalar `I := e₀ e₁ e₂`, `I * I = -1`.
  6. Hodge-dual theorem connecting to the DiffGeom layer:
     `embed u * embed v = ⟪u, v⟫ • 1 + embed (cross u v) * I`
     (the blade of two vectors = inner product + dualized cross).
     Needs basis cross products: `cross e₀ e₁ = e₂`, `cross e₀ e₂ =
     -e₁`, `cross e₁ e₂ = e₀`, zero on the diagonal (easy `ext` +
     `fin_cases` from `DiffGeom.cross_coordinates`).
  7. Later: grade projections, blades as subspace carriers
     (`tangentX ∧ tangentY` = tangent plane, `‖blade‖² = det gramMatrix`),
     rotors/versors for camera math.
- Current scratch: `lean/Scratch.lean` (NOT committed) — step 1 attempted
  on the wrong module (`Fin 3 → ℝ`); redo on `Vec3`.
- Useful Mathlib API found: `CliffordAlgebra.ι`, `ι_sq_scalar`,
  `CliffordAlgebra.evenOdd` (ℤ₂-grading), `CliffordAlgebra.even`,
  `EvenHom`/`even.lift` (universal property of the even subalgebra),
  `QuadraticMap.ofPolar`.

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
