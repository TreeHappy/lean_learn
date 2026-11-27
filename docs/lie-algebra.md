# Lie Algebras and $\mathfrak{so}(3)$

This note is the algebraic companion to [`connections.md`](connections.md). The
categorical reading of the Lie-algebra adjunction is in
[`category-theory.md`](category-theory.md). The
bracket of vector fields and the torsion of a connection are Lie-algebraic
objects, and the cross product on $\mathbb{R}^3$ is the smallest interesting
example. Everything below cites the actual declarations in
`lean/Brane/LieAlgebra.lean` (namespace `Brane.Lie`).

The Lean code does **not** reinvent Lie algebras. It instantiates Mathlib's
`LieRing` / `LieAlgebra` classes with the concrete vector space `Vec3` from
`Brane.DiffGeom`, and proves the axioms for the cross product. The only
background you need is: vector addition, scalar multiplication, and the cross
product.

> [!NOTE]
> **Where this sits.** `LieAlgebra.lean` imports `Brane.GeometricAlgebra` and
> Mathlib's Lie-algebra API. It is the last layer of the story:
> `DifferentialGeometry.lean` → `Shooting.lean` → `Connections.lean` →
> `ParallelTransport.lean` → `LieAlgebra.lean`.

---

## 1. The definition

> [!IMPORTANT]
> **Definition (Lie algebra).** A **Lie algebra** over a field is a vector
> space $L$ with a bilinear map $[\cdot,\cdot] : L \times L \to L$ (the
> *bracket*) that is
>
> * **alternating**: $[x,x] = 0$, equivalently $[x,y] = -[y,x]$;
> * satisfies the **Jacobi identity**:
>
> ```math
> [x,[y,z]] + [y,[z,x]] + [z,[x,y]] = 0.
> ```

Mathlib splits this into two classes. `LieRing` is the additive-group version,
with fields `add_lie`, `lie_add`, `lie_self`, and `leibniz_lie` (the last is
Jacobi in Leibniz form). `LieAlgebra R L` adds compatibility with scalar
multiplication, `lie_smul`.

The equivalent **Leibniz form** of Jacobi is the one that matters for
derivations:

```math
[x,[y,z]] = [[x,y],z] + [y,[x,z]].
```

> [!TIP]
> **Why two forms?** The cyclic sum is the textbook statement; the Leibniz
> form says "$\mathrm{ad}_x$ differentiates the bracket". The second is
> exactly what the connection Leibniz rule needs, so Lean proves that form and
> derives the first.

---

## 2. The cross product on $\mathbb{R}^3$

For `Vec3` vectors $u, v$ (that is, $u, v \in \mathbb{R}^3$), define

```math
u \times v = (u_1 v_2 - u_2 v_1,\; u_2 v_0 - u_0 v_2,\; u_0 v_1 - u_1 v_0).
```

This is `Brane.DiffGeom.cross`, transported from Mathlib's `crossProduct` on
`Fin 3 → ℝ`. We register it as the bracket:

```lean
instance : Bracket Vec3 Vec3 := ⟨cross⟩
```

The bracket laws are proved by reducing to coordinates. Each line below is a
real theorem in the file:

| Law | Lean name | Statement |
| --- | --- | --- |
| additivity, left slot | `bracket_add_left` | $[u+u',v] = [u,v] + [u',v]$ |
| additivity, right slot | `bracket_add_right` | $[u,v+v'] = [u,v] + [u,v']$ |
| alternation | `bracket_self` | $[u,u] = 0$ |
| antisymmetry | `bracket_anticomm` | $[u,v] = -[v,u]$ |
| scalar linearity, left | `bracket_smul_left` | $[t\thinspace u,v] = t\thinspace [u,v]$ |
| scalar linearity, right | `bracket_smul_right` | $[u,t\thinspace v] = t\thinspace [u,v]$ |
| Jacobi | `bracket_jacobi` | $[u,[v,w]] + [v,[w,u]] + [w,[u,v]] = 0$ |
| Jacobi, Leibniz form | `bracket_leibniz` | $[u,[v,w]] = [[u,v],w] + [v,[u,w]]$ |

> [!NOTE]
> **How Jacobi is proved.** Rewrite with `cross_coordinates` and check the
> three coordinates with `fin_cases` and `ring`:
>
> ```lean
> theorem bracket_jacobi (u v w : Vec3) :
>     ⁅u, ⁅v, w⁆⁆ + ⁅v, ⁅w, u⁆⁆ + ⁅w, ⁅u, v⁆⁆ = 0 := by
>   change cross u (cross v w) + cross v (cross w u) + cross w (cross u v) = 0
>   rw [cross_coordinates, cross_coordinates, cross_coordinates, cross_coordinates,
>     cross_coordinates, cross_coordinates]
>   ext i
>   fin_cases i <;> simp [vec3] <;> ring
> ```
>
> Mathlib's `jacobi_cross` proves the same identity for the untransported
> product on `Fin 3 → ℝ`; the coordinate proof here avoids the `WithLp`
> transport.

The instances

```lean
instance crossLieRing : LieRing Vec3 where
  add_lie := Brane.GA.cross_add_left
  lie_add := Brane.GA.cross_add_right
  lie_self := Brane.GA.cross_self
  leibniz_lie := bracket_leibniz

instance crossLieAlgebra : LieAlgebra ℝ Vec3 where
  lie_smul := fun t x y => Brane.GA.cross_smul_right x t y
```

then make `Vec3` a genuine Lie algebra, with $[u,v] = u \times v$.

---

## 3. The adjoint action

> [!NOTE]
> **Definition (adjoint action).** For fixed $u$, the map
> $\mathrm{ad}_u : v \mapsto [u,v]$ is linear:

```lean
def crossAdjoint (u : Vec3) : Vec3 →ₗ[ℝ] Vec3 where
  toFun v := ⁅u, v⁆
  map_add' v w := Brane.GA.cross_add_right u v w
  map_smul' t v := Brane.GA.cross_smul_right u t v
```

The Jacobi identity says exactly that $\mathrm{ad}_u$ is a **derivation**
of the bracket:

```lean
theorem crossAdjoint_leibniz (u v w : Vec3) :
    crossAdjoint u ⁅v, w⁆ = ⁅crossAdjoint u v, w⁆ + ⁅v, crossAdjoint u w⁆ :=
  bracket_leibniz u v w
```

This is the infinitesimal form of the adjoint representation of a Lie group,
and the algebraic pattern behind "differentiate a product" — the same pattern
as the connection Leibniz rule `cov_leibniz` in `Brane.Connections`.

---

## 4. The hat map and $\mathfrak{so}(3)$

> [!IMPORTANT]
> **Definition ($\mathfrak{so}(3)$).** The Lie algebra $\mathfrak{so}(3)$
> consists of the skew-symmetric $3 \times 3$ matrices. The **hat map** sends
> a vector to the matrix of cross product by that vector:

```lean
def hatMatrix (u : Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -u 2, u 1; u 2, 0, -u 0; -u 1, u 0, 0]
```

Two facts connect it to the bracket:

* `hatMatrix_mem_so` — $\widehat{u}$ is skew-symmetric, so it lies in
  `LieAlgebra.Orthogonal.so (Fin 3) ℝ`;
* `hatMatrix_commutator` — $\widehat{[u,v]} = [\widehat{u},\widehat{v}]$,
  where the right-hand bracket is the matrix commutator
  $\widehat{u}\thinspace \widehat{v} - \widehat{v}\thinspace \widehat{u}$.

```lean
theorem hatMatrix_mem_so (u : Vec3) :
    hatMatrix u ∈ LieAlgebra.Orthogonal.so (Fin 3) ℝ := by
  rw [LieAlgebra.Orthogonal.mem_so]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hatMatrix]

theorem hatMatrix_commutator (u v : Vec3) :
    hatMatrix ⁅u, v⁆ = hatMatrix u * hatMatrix v - hatMatrix v * hatMatrix u := by
  change hatMatrix (cross u v) = hatMatrix u * hatMatrix v - hatMatrix v * hatMatrix u
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hatMatrix, cross_coordinates, vec3] <;> ring
```

The hat map is therefore a Lie-algebra homomorphism from
$(\mathrm{Vec3}, \times)$ to $\mathfrak{so}(3)$. The full equivalence

```lean
noncomputable def so3MatrixEquiv :
    Vec3 ≃ₗ⁅ℝ⁆ LieAlgebra.Orthogonal.so (Fin 3) ℝ := by
  sorry
```

is stated and left as `sorry`; the missing work is the explicit inverse (read
off the entries $u_0 = A_{10}$, $u_1 = A_{02}$, $u_2 = A_{21}$ of a
skew-symmetric matrix) and the bracket-preservation proof, which follows from
`hatMatrix_commutator`.

> [!TIP]
> **Reading the inverse.** The matrix $\widehat{u}$ stores the three
> independent entries in the slots $A_{10}$, $A_{02}$, $A_{21}$. A
> skew-symmetric matrix has exactly those three degrees of freedom, which is
> why the hat map is an isomorphism onto $\mathfrak{so}(3)$ rather than merely
> an injection.

---

## 5. Mathlib's matrix Lie algebras

The file also records the dictionary with Mathlib:

| Object | Mathlib name | Lean restatement |
| --- | --- | --- |
| bracket on matrices | $[A,B] = AB - BA$ | `matrix_bracket_eq_commutator` |
| special linear Lie algebra | `LieAlgebra.SpecialLinear.sl` | `mem_sl_iff` |
| orthogonal Lie algebra | `LieAlgebra.Orthogonal.so` | `mem_so_iff` |
| derivations | `Derivation` | `derivation_leibniz` |

```lean
theorem matrix_bracket_eq_commutator (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    ⁅A, B⁆ = A * B - B * A :=
  rfl

theorem mem_so_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A ∈ LieAlgebra.Orthogonal.so (Fin 3) ℝ ↔ Aᵀ = -A :=
  LieAlgebra.Orthogonal.mem_so (Fin 3) ℝ A

theorem mem_sl_iff (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A ∈ LieAlgebra.SpecialLinear.sl (Fin 3) ℝ ↔ A.trace = 0 := by
  simp [LieAlgebra.SpecialLinear.sl]

theorem derivation_leibniz {A : Type*} [CommRing A] [Algebra ℝ A]
    (D : Derivation ℝ A A) (a b : A) :
    D (a * b) = a • D b + b • D a :=
  D.leibniz a b
```

So `Vec3` with the cross product is the same Lie algebra as
$\mathfrak{so}(3)$, and $\mathfrak{sl}(3)$ / $\mathfrak{so}(3)$ are available
from Mathlib whenever a matrix model is more convenient than the coordinate
model.

---

## 6. Proven vs. declared

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
| $\mathrm{Vec3} \cong \mathfrak{so}(3)$ | `so3MatrixEquiv` | `sorry` |

The single `sorry` is the explicit equivalence with Mathlib's bundled
$\mathfrak{so}(3)$: the homomorphism half is already proved, and the inverse
is the entry-reading map described in §4.

---

## 7. Cheat sheet: file ↔ concept

| `Brane/LieAlgebra.lean` | Plain-language description | Built from |
| --- | --- | --- |
| `Bracket Vec3 Vec3` | the cross product, used as the Lie bracket | `DiffGeom.cross` |
| `bracket_jacobi` | the cross product satisfies Jacobi | coordinates + `ring` |
| `crossLieRing` | `Vec3` is a Lie ring | the bracket laws |
| `crossLieAlgebra` | `Vec3` is a real Lie algebra | `cross_smul_right` |
| `crossAdjoint u` | the linear map $v \mapsto [u,v]$ | `cross_add_right`, `cross_smul_right` |
| `crossAdjoint_leibniz` | $\mathrm{ad}_u$ is a derivation | `bracket_leibniz` |
| `hatMatrix u` | the skew-symmetric matrix of $u$ | matrix literal |
| `hatMatrix_mem_so` | its image lies in $\mathfrak{so}(3)$ | entry check |
| `hatMatrix_commutator` | hat turns $\times$ into the matrix commutator | entry check |
| `so3MatrixEquiv` | $\mathrm{Vec3} \cong \mathfrak{so}(3)$ | `sorry` |

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
