/-
Copyright (c) 2026 Brane contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brane contributors
-/
import Brane.ChartMap
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Control.Monad.Basic

/-!
# A categorical reading of the chart, bundle, and integrator APIs

This file is the Lean companion to `docs/category-theory.md`. It does not
develop new geometry. It names the categorical structures that the existing
modules already use, so that the dictionary in the note is checkable:

* the graph of a height function is a **section** in the slice category
  `Over Point2` (`graphSection`);
* a chart is an **object** of the slice category `Over Point3`, and a
  reparameterization is a **morphism** (`chartObject`, `chartTransition`);
* parameter charts and their reparameterizations form a category
  (`ParamChart`), and the graph-surface construction is a functor
  (`toSurfaceFunctor`);
* the tangent space is an object of `ModuleCat ℝ`, and a chart Jacobian is a
  morphism there (`tangentModule`, `jacobianLin`);
* the Euler integrator is a Kleisli arrow for the state monad, and iterating it
  is the same as `Brane.Shoot.shoot` (`StepM`, `eulerK`, `runSteps`,
  `runSteps_euler`).

The last item is the only new induction proof. The rest are definitions,
instances, and `rfl` lemmas that make the categorical vocabulary available to
later files.

## Main definitions

* `Brane.Cat.proj2`, `graphBundle`, `basePoint`, `graphSection`;
* `Brane.Cat.chartObject`, `chartTransition`;
* `Brane.Cat.ParamChartHom`, `toSurfaceFunctor`;
* `Brane.Cat.tangentModule`, `jacobianLin`;
* `Brane.Cat.StepM`, `eulerK`, `runSteps`.

## Main results

* `Brane.Cat.proj2_graph`: the graph is a section of the projection;
* `Brane.Cat.runSteps_euler`: Kleisli iteration is `Brane.Shoot.shoot`.

## Tags

category theory, slice category, functor, tangent space, state monad,
Kleisli arrow, chart
-/

@[expose] public section

open CategoryTheory
open Brane
open Brane.DiffGeom
open Brane.ChartMap

namespace Brane
namespace Cat

/-! ## Bundles and sections as a slice category -/

/-- Forget the height coordinate of an ambient point. -/
def proj2 (v : Point3) : Point2 := (v 0, v 1)

/-- The graph of `h` is a section of the projection `proj2`. -/
@[simp] theorem proj2_graph (h : HeightFun) (p : Point2) : proj2 (graph h p) = p := rfl

/-- The trivial bundle `Point2 × ℝ`, viewed as an object of the slice over
`Point2`. -/
def graphBundle : Over Point2 := Over.mk (TypeCat.ofHom proj2)

/-- The identity map is the terminal object of the slice over `Point2`. -/
def basePoint : Over Point2 := Over.mk (TypeCat.ofHom (id : Point2 → Point2))

/-- The graph of `h` is a section: a morphism from the terminal object of the
slice to the bundle. -/
def graphSection (h : HeightFun) : basePoint ⟶ graphBundle :=
  Over.homMk (TypeCat.ofHom (graph h)) (by
    refine ConcreteCategory.hom_ext _ _ ?_
    intro p
    exact proj2_graph h p)

/-! ## Charts as objects, reparameterizations as morphisms -/

/-- A chart is an object of the slice over ambient space. -/
def chartObject (h : HeightFun) (φ : ParamChart) : Over Point3 :=
  Over.mk (TypeCat.ofHom (toSurface h φ))

/-- A reparameterization of charts is a morphism in the slice. -/
def chartTransition {h : HeightFun} {φ ψ : ParamChart} (f : ParamChart)
    (hf : ∀ u, toSurface h ψ (f u) = toSurface h φ u) :
    chartObject h φ ⟶ chartObject h ψ :=
  Over.homMk (TypeCat.ofHom f) (by
    refine ConcreteCategory.hom_ext _ _ ?_
    intro u
    change toSurface h ψ (f u) = toSurface h φ u
    exact hf u)

/-- A morphism of parameter charts: `f` reparameterizes `φ` to `ψ` when
`φ = ψ ∘ f`. -/
structure ParamChartHom (φ ψ : ParamChart) where
  /-- The reparameterization. -/
  f : ParamChart
  /-- The reparameterization equation. -/
  comm : φ = ψ ∘ f

instance : CategoryStruct ParamChart where
  Hom := ParamChartHom
  id φ := ⟨id, rfl⟩
  comp := fun {φ ψ χ} f g => ⟨g.f ∘ f.f, by
    calc φ = ψ ∘ f.f := f.comm
      _ = (χ ∘ g.f) ∘ f.f := congrArg (fun k => k ∘ f.f) g.comm
      _ = χ ∘ (g.f ∘ f.f) := Function.comp_assoc χ g.f f.f⟩

instance : Category ParamChart where
  comp_id f := by cases f; rfl
  id_comp f := by cases f; rfl
  assoc f g h := by cases f; cases g; cases h; rfl

/-- The graph-surface construction is a functor from charts to the slice over
ambient space. -/
def toSurfaceFunctor (h : HeightFun) : ParamChart ⥤ Over Point3 where
  obj φ := chartObject h φ
  map f := chartTransition (h := h) f.f (by
    intro u
    exact congrArg (graph h) (congrFun f.comm u).symm)
  map_id φ := rfl
  map_comp f g := rfl

/-! ## The tangent space as a module -/

/-- The tangent space at a point, as an object of the category of real vector
spaces. -/
def tangentModule : ModuleCat ℝ := ModuleCat.of ℝ Vel2

/-- The Jacobian of a chart is a morphism of tangent spaces. -/
noncomputable def jacobianLin (φ : ParamChart) (u : Point2) :
    tangentModule ⟶ tangentModule :=
  ModuleCat.ofHom (Matrix.toLin' (chartJacobian φ u))

/-! ## Monoids and groups as one-object categories -/

/-- The multiplicative monoid `ℝ` as a one-object category. -/
example : Category (SingleObj ℝ) := inferInstance

/-- The group of nonzero reals as a one-object groupoid. -/
example : Groupoid (SingleObj ℝˣ) := inferInstance

/-! ## The integrator as a Kleisli arrow -/

/-- A stateful step is a Kleisli arrow for the state monad. -/
abbrev StepM (K : Type) := StateM (Shoot.ShotState K) Unit

/-- The Euler step as a Kleisli arrow. -/
def eulerK (K : Type) [Shoot.GeoKernel K] [Add K] [Mul K] [Neg K] [Sub K] [Div K]
    (h : K → K → K) (dt : K) : StepM K :=
  fun s => ((), Shoot.eulerStep h s dt)

/-- Iterating a stateful step `n` times. -/
def runSteps {K : Type} (step : StepM K) (n : ℕ) : StepM K :=
  fun s => ((), Nat.iterate (fun t => (step t).2) n s)

/-- Kleisli iteration of the Euler step is exactly `Brane.Shoot.shoot`. -/
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

end Cat
end Brane
