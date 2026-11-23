# Lie algebras and `so(3)`

This note explains the Lie-algebra layer in `lean/Brane/LieAlgebra.lean`.
It is the algebraic companion to [`connections.md`](connections.md): the
bracket of vector fields and the torsion of a connection are Lie-algebraic
objects, and the cross product on `ℝ³` is the smallest interesting example.

The Lean code does **not** reinvent Lie algebras. It instantiates Mathlib's
`LieRing` / `LieAlgebra` classes with the concrete vector space `Vec3` from
`Brane.DiffGeom`, and proves the axioms for the cross product.

---

## 1. The definition

A **Lie algebra** over a field is a vector space `L` with a bilinear map
`⁅·, ·⁆ : L × L → L` (the *bracket*) that is

* **alternating**: `⁅x, x⁆ = 0`, equivalently `⁅x, y⁆ = -⁅y, x⁆`;
* satisfies the **Jacobi identity**:

$$
⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0.
$$

Mathlib splits this into two classes. `LieRing` is the additive-group
version, with fields `add_lie`, `lie_add`, `lie_self`, and `leibniz_lie`
(the last is Jacobi in Leibniz form). `LieAlgebra R L` adds compatibility
with scalar multiplication, `lie_smul`.

The equivalent **Leibniz form** of Jacobi is the one that matters for
derivations:

$$
⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆.
$$

## 2. The cross product on `ℝ³`

For `u, v : Vec3 = EuclideanSpace ℝ (Fin 3)`, define

$$
u \times v = (u_1 v_2 - u_2 v_1,\; u_2 v_0 - u_0 v_2,\; u_0 v_1 - u_1 v_0).
$$

This is `Brane.DiffGeom.cross`, transported from Mathlib's `crossProduct` on
`Fin 3 → ℝ`. We register it as the bracket:

```lean
instance : Bracket Vec3 Vec3 := ⟨cross⟩
```

The bracket laws are proved by reducing to coordinates:

* `bracket_add_left`, `bracket_add_right` — additivity;
* `bracket_self` — `⁅u, u⁆ = 0`;
* `bracket_anticomm` — `⁅u, v⁆ = -⁅v, u⁆`;
* `bracket_smul_left`, `bracket_smul_right` — `ℝ`-linearity;
* `bracket_jacobi` — the Jacobi identity;
* `bracket_leibniz` — Jacobi in derivation form.

The Jacobi identity is proved by rewriting with `cross_coordinates` and
checking the three coordinates with `fin_cases` and `ring`. (Mathlib's
`jacobi_cross` proves the same identity for the untransported product on
`Fin 3 → ℝ`; the coordinate proof here avoids the `WithLp` transport.)

The instances

```lean
instance crossLieRing : LieRing Vec3
instance crossLieAlgebra : LieAlgebra ℝ Vec3
```

then make `Vec3` a genuine Lie algebra, with `⁅u, v⁆ = u × v`.

## 3. The adjoint action

For fixed `u`, the map `ad u : v ↦ ⁅u, v⁆` is linear:

```lean
def crossAdjoint (u : Vec3) : Vec3 →ₗ[ℝ] Vec3 where
  toFun v := ⁅u, v⁆
  map_add' v w := Brane.GA.cross_add_right u v w
  map_smul' t v := Brane.GA.cross_smul_right u t v
```

The Jacobi identity says exactly that `ad u` is a **derivation** of the
bracket:

```lean
theorem crossAdjoint_leibniz (u v w : Vec3) :
    crossAdjoint u ⁅v, w⁆ = ⁅crossAdjoint u v, w⁆ + ⁅v, crossAdjoint u w⁆
```

This is the infinitesimal form of the adjoint representation of a Lie
group, and the algebraic pattern behind "differentiate a product" — the
same pattern as the connection Leibniz rule `cov_leibniz` in
`Brane.Connections`.

## 4. The hat map and `so(3)`

The Lie algebra `so(3)` consists of the skew-symmetric `3 × 3` matrices.
The **hat map** sends a vector to the matrix of cross product by that
vector:

```lean
def hatMatrix (u : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -u 2, u 1; u 2, 0, -u 0; -u 1, u 0, 0]
```

Two facts connect it to the bracket:

* `hatMatrix_mem_so` — `hatMatrix u` is skew-symmetric, so it lies in
  `LieAlgebra.Orthogonal.so (Fin 3) ℝ`;
* `hatMatrix_commutator` — `hatMatrix ⁅u, v⁆ = [hatMatrix u, hatMatrix v]`,
  where the right-hand bracket is the matrix commutator
  `A * B - B * A`.

The hat map is therefore a Lie-algebra homomorphism from `(Vec3, ×)` to
`so(3)`. The full equivalence

```lean
noncomputable def so3MatrixEquiv :
    Vec3 ≃ₗ⁅ℝ⁆ LieAlgebra.Orthogonal.so (Fin 3) ℝ
```

is stated and left as `sorry`; the missing work is the explicit inverse
(read off the entries `A₂₁`, `A₀₂`, `A₁₀` of a skew-symmetric matrix) and
the bracket-preservation proof, which follows from
`hatMatrix_commutator`.

## 5. Mathlib's matrix Lie algebras

The file also records the dictionary with Mathlib:

| Object | Mathlib name | Lean restatement |
| --- | --- | --- |
| bracket on matrices | `⁅A, B⁆ = A * B - B * A` | `matrix_bracket_eq_commutator` |
| special linear Lie algebra | `LieAlgebra.SpecialLinear.sl` | `mem_sl_iff` |
| orthogonal Lie algebra | `LieAlgebra.Orthogonal.so` | `mem_so_iff` |
| derivations | `Derivation` | `derivation_leibniz` |

So `Vec3` with the cross product is the same Lie algebra as `so(3)`, and
`sl(3)` / `so(3)` are available from Mathlib whenever a matrix model is
more convenient than the coordinate model.

---

## Proof status

| Result | Lean name | Status |
| --- | --- | --- |
| Bracket additivity | `bracket_add_left/right` | proved |
| Alternation | `bracket_self`, `bracket_anticomm` | proved |
| Scalar linearity | `bracket_smul_left/right` | proved |
| Jacobi identity | `bracket_jacobi` | proved |
| Leibniz form of Jacobi | `bracket_leibniz` | proved |
| `LieRing` instance | `crossLieRing` | proved |
| `LieAlgebra` instance | `crossLieAlgebra` | proved |
| Adjoint is a derivation | `crossAdjoint_leibniz` | proved |
| Hat matrix is skew | `hatMatrix_mem_so` | proved |
| Hat respects commutator | `hatMatrix_commutator` | proved |
| `Vec3 ≃ so(3)` | `so3MatrixEquiv` | `sorry` |

---

## References

### Primary encyclopedia articles

* Wikipedia, [Lie algebra](https://en.wikipedia.org/wiki/Lie_algebra)
* Wikipedia, [Lie bracket of vector fields](https://en.wikipedia.org/wiki/Lie_bracket_of_vector_fields)
* Wikipedia, [Adjoint representation](https://en.wikipedia.org/wiki/Adjoint_representation)
* Wikipedia, [Special orthogonal Lie algebra](https://en.wikipedia.org/wiki/Orthogonal_Lie_algebra)
* Wikipedia, [Derivation (differential algebra)](https://en.wikipedia.org/wiki/Derivation_(differential_algebra))

### Wolfram MathWorld

* [Lie Algebra](https://mathworld.wolfram.com/LieAlgebra.html)
* [Lie Bracket](https://mathworld.wolfram.com/LieBracket.html)
* [Adjoint Representation](https://mathworld.wolfram.com/AdjointRepresentation.html)
* [Special Orthogonal Group](https://mathworld.wolfram.com/SpecialOrthogonalGroup.html)

### nLab

* [Lie algebra](https://ncatlab.org/nlab/show/Lie+algebra)
* [Lie bracket](https://ncatlab.org/nlab/show/Lie+bracket)
* [adjoint action](https://ncatlab.org/nlab/show/adjoint+action)

### Encyclopedia of Mathematics

* [Lie algebra](https://encyclopediaofmath.org/wiki/Lie_algebra)
* [Lie algebra, universal enveloping](https://encyclopediaofmath.org/wiki/Universal_enveloping_algebra)

### Free books and lecture notes

* A. Kirillov, *Introduction to Lie Groups and Lie Algebras* —
  <https://www.math.stonybrook.edu/~kirillov/mat552/liegroups.pdf>
* H. Samelson, *Notes on Lie Algebras* —
  <https://pi.math.cornell.edu/~hatcher/Other/Samelson-LieAlg.pdf>
* P. Etingof, *Lie Groups and Lie Algebras II* (MIT 18.755, 2024) —
  <https://ocw.mit.edu/courses/18-755-lie-groups-and-lie-algebras-ii-spring-2024/mit18_755_s24_lec_full.pdf>
* E. Belmont, *A Course on Lie Algebras and their Representations* —
  <https://mathweb.ucsd.edu/~ebelmont/lie-notes.pdf>
* K. Erdmann and M. Wildon, *Introduction to Lie Algebras*, Springer
  Undergraduate Mathematics Series, 2006.

### Papers

* W. Magnus, "Über Gruppen und Ideale in Lieschen Ringen",
  *J. Reine Angew. Math.* **177** (1937), 105–113.
* C. Chevalley and S. Eilenberg, "Cohomology theory of Lie groups and Lie
  algebras", *Trans. Amer. Math. Soc.* **63** (1948), 85–124.
* H. Munthe-Kaas and A. Lundervold, "On post-Lie algebras, Lie–Butcher
  series and post-Lie algebra valued flows", *SIAM J. Appl. Algebra Geom.*
  **4** (2020), 356–392. DOI: [10.1137/19M1252879](https://doi.org/10.1137/19M1252879)

See [`../bibtex.md`](../bibtex.md) for the human-readable link list and
[`../references.bib`](../references.bib) for the BibTeX entries.
