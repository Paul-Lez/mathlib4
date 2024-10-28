/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Glouglou

-/

open Set
open scoped Topology

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 :Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  {F : Type*} [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F]
  {G : Type*} [TopologicalSpace G] [AddCommGroup G] [Module 𝕜 G]

/-- A continuous linear map is invertible if it is the forward direction of a continuous linear
equivalence. -/
def IsInvertible (f : E →L[𝕜] F) : Prop :=
  ∃ (M : E ≃L[𝕜] F), M = f

/-- Given an invertible continuous linear map, choose an equiv of which it is the direct
direction. -/
def IsInvertible.toEquiv {f : E →L[𝕜] F} (hf : f.IsInvertible) : E ≃L[𝕜] F :=
  hf.choose

lemma IsInvertible.toEquiv_eq {f : E →L[𝕜] F} (hf : f.IsInvertible) :
    hf.toEquiv = f :=
  hf.choose_spec

@[simp] lemma isInvertible_equiv {f : E ≃L[𝕜] F} : IsInvertible (f : E →L[𝕜] F) := ⟨f, rfl⟩

lemma inverse_of_not_isInvertible {f : E →L[𝕜] F} (hf : ¬ f.IsInvertible) : f.inverse = 0 :=
  inverse_non_equiv _ hf

lemma IsInvertible.comp {g : F →L[𝕜] G} {f : E →L[𝕜] F}
    (hg : g.IsInvertible) (hf : f.IsInvertible) : (g ∘L f).IsInvertible := by
  rcases hg with ⟨N, rfl⟩
  rcases hf with ⟨M, rfl⟩
  exact ⟨M.trans N, rfl⟩

lemma IsInvertible.of_inverse {f : E →L[𝕜] F} {g : F →L[𝕜] E}
    (hf : f ∘L g = id 𝕜 F) (hg : g ∘L f = id 𝕜 E) :
    f.IsInvertible := by
  let M : E ≃L[𝕜] F :=
  { f with
    invFun := g
    left_inv := by
      intro x
      have : (g ∘L f) x = x := by simp [hg]
      simpa using this
    right_inv := by
      intro x
      have : (f ∘L g) x = x := by simp [hf]
      simpa using this }
  exact ⟨M, rfl⟩

lemma inverse_eq {f : E →L[𝕜] F} {g : F →L[𝕜] E}
    (hf : f ∘L g = id 𝕜 F) (hg : g ∘L f = id 𝕜 E) :
    f.inverse = g := by
  let M : E ≃L[𝕜] F :=
  { f with
    invFun := g
    left_inv := by
      intro x
      have : (g ∘L f) x = x := by simp [hg]
      simpa using this
    right_inv := by
      intro x
      have : (f ∘L g) x = x := by simp [hf]
      simpa using this }
  change (M : E →L[𝕜] F).inverse = g
  simp only [inverse_equiv]
  rfl

lemma IsInvertible.inverse_apply_eq {f : E →L[𝕜] F} {x : E} {y : F} (hf : f.IsInvertible) :
    f.inverse y = x ↔ y = f x := by
  rcases hf with ⟨M, rfl⟩
  simp only [inverse_equiv, ContinuousLinearEquiv.coe_coe]
  exact ContinuousLinearEquiv.symm_apply_eq M

/-- At an invertible map `e : E →L[𝕜] F` between Banach spaces, the operation of
inversion is `C^n`, for all `n`. -/
theorem IsInvertible.contDiffAt_map_inverse {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] (e : E →L[𝕜] F)
    (he : e.IsInvertible) {n : ℕ∞} :
    ContDiffAt 𝕜 n inverse e := by
  rcases he with ⟨M, rfl⟩
  exact _root_.contDiffAt_map_inverse M

@[simp] lemma isInvertible_equiv_comp {e : F ≃L[𝕜] G} {f : E →L[𝕜] F} :
    ((e : F →L[𝕜] G) ∘L f).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨M, hM⟩
    have : f = e.symm ∘L ((e : F →L[𝕜] G) ∘L f) := by ext; simp
    rw [this, ← hM]
    simp
  · rintro ⟨M, rfl⟩
    simp

@[simp] lemma isInvertible_comp_equiv {e : G ≃L[𝕜] E} {f : E →L[𝕜] F} :
    (f ∘L (e : G →L[𝕜] E)).IsInvertible ↔ f.IsInvertible := by
  constructor
  · rintro ⟨M, hM⟩
    have : f = (f ∘L (e : G →L[𝕜] E)) ∘L e.symm := by ext; simp
    rw [this, ← hM]
    simp
  · rintro ⟨M, rfl⟩
    simp

@[simp] lemma inverse_equiv_comp {e : F ≃L[𝕜] G} {f : E →L[𝕜] F} :
    (e ∘L f).inverse = f.inverse ∘L (e.symm : G →L[𝕜] F) := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨M, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf]
    rfl

@[simp] lemma inverse_comp_equiv {e : G ≃L[𝕜] E} {f : E →L[𝕜] F} :
    (f ∘L e).inverse = (e.symm : E →L[𝕜] G) ∘L f.inverse := by
  by_cases hf : f.IsInvertible
  · rcases hf with ⟨M, rfl⟩
    simp only [ContinuousLinearEquiv.comp_coe, inverse_equiv, ContinuousLinearEquiv.coe_inj]
    rfl
  · rw [inverse_of_not_isInvertible (by simp [hf]), inverse_of_not_isInvertible hf]
    simp

lemma IsInvertible.inverse_comp_of_left {g : F →L[𝕜] G} {f : E →L[𝕜] F}
    (hg : g.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hg with ⟨N, rfl⟩
  simp

lemma IsInvertible.inverse_comp_apply_of_left {g : F →L[𝕜] G} {f : E →L[𝕜] F} {v : G}
    (hg : g.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hg.inverse_comp_of_left, coe_comp', Function.comp_apply]

lemma IsInvertible.inverse_comp_of_right {g : F →L[𝕜] G} {f : E →L[𝕜] F}
    (hf : f.IsInvertible) : (g ∘L f).inverse = f.inverse ∘L g.inverse := by
  rcases hf with ⟨M, rfl⟩
  simp

lemma IsInvertible.inverse_comp_apply_of_right {g : F →L[𝕜] G} {f : E →L[𝕜] F} {v : G}
    (hf : f.IsInvertible) : (g ∘L f).inverse v = f.inverse (g.inverse v) := by
  simp only [hf.inverse_comp_of_right, coe_comp', Function.comp_apply]

end ContinuousLinearMap


section LieBracketVectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V W V₁ W₁ : E → E} {s t : Set E} {x : E}

/-!
### The Lie bracket of vector fields in a vector space

We define the Lie bracket of two vector fields, and call it `lieBracket 𝕜 V W x`. We also define
a version localized to sets, `lieBracketWithin 𝕜 V W s x`. We copy the relevant API
of `fderivWithin` and `fderiv` for these notions to get a comprehensive API.
-/

namespace VectorField

variable (𝕜) in
/-- The Lie bracket `[V, W] (x)` of two vector fields at a point, defined as
`DW(x) (V x) - DV(x) (W x)`. -/
def lieBracket (V W : E → E) (x : E) : E :=
  fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)

variable (𝕜) in
/-- The Lie bracket `[V, W] (x)` of two vector fields within a set at a point, defined as
`DW(x) (V x) - DV(x) (W x)` where the derivatives are taken inside `s`. -/
def lieBracketWithin (V W : E → E) (s : Set E) (x : E) : E :=
  fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x)

lemma lieBracket_eq :
    lieBracket 𝕜 V W = fun x ↦ fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x) := rfl

lemma lieBracketWithin_eq :
    lieBracketWithin 𝕜 V W s =
      fun x ↦ fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x) := rfl

@[simp]
theorem lieBracketWithin_univ : lieBracketWithin 𝕜 V W univ = lieBracket 𝕜 V W := by
  ext1 x
  simp [lieBracketWithin, lieBracket]

lemma lieBracketWithin_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    lieBracketWithin 𝕜 V W s x = 0 := by
  simp [lieBracketWithin, hV, hW]

lemma lieBracket_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    lieBracket 𝕜 V W x = 0 := by
  simp [lieBracket, hV, hW]

lemma lieBracketWithin_add_left (hV : DifferentiableWithinAt 𝕜 V s x)
    (hV₁ : DifferentiableWithinAt 𝕜 V₁ s x) (hs :  UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (V + V₁) W s x =
      lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V₁ W s x := by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add' hs hV hV₁, ContinuousLinearMap.add_apply]
  abel

lemma lieBracket_add_left (hV : DifferentiableAt 𝕜 V x) (hV₁ : DifferentiableAt 𝕜 V₁ x) :
    lieBracket 𝕜 (V + V₁) W  x =
      lieBracket 𝕜 V W x + lieBracket 𝕜 V₁ W x := by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add' hV hV₁, ContinuousLinearMap.add_apply]
  abel

lemma lieBracketWithin_add_right (hW : DifferentiableWithinAt 𝕜 W s x)
    (hW₁ : DifferentiableWithinAt 𝕜 W₁ s x) (hs :  UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (W + W₁) s x =
      lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V W₁ s x := by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add' hs hW hW₁, ContinuousLinearMap.add_apply]
  abel

lemma lieBracket_add_right (hW : DifferentiableAt 𝕜 W x) (hW₁ : DifferentiableAt 𝕜 W₁ x) :
    lieBracket 𝕜 V (W + W₁) x =
      lieBracket 𝕜 V W x + lieBracket 𝕜 V W₁ x := by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add' hW hW₁, ContinuousLinearMap.add_apply]
  abel

lemma lieBracketWithin_swap : lieBracketWithin 𝕜 V W s = - lieBracketWithin 𝕜 W V s := by
  ext x; simp [lieBracketWithin]

lemma lieBracket_swap : lieBracket 𝕜 V W x = - lieBracket 𝕜 W V x := by
  simp [lieBracket]

@[simp] lemma lieBracketWithin_self : lieBracketWithin 𝕜 V V s = 0 := by
  ext x; simp [lieBracketWithin]

@[simp] lemma lieBracket_self : lieBracket 𝕜 V V = 0 := by
  ext x; simp [lieBracket]

lemma _root_.ContDiffWithinAt.lieBracketWithin_vectorField
    {m n : ℕ∞} (hV : ContDiffWithinAt 𝕜 n V s x)
    (hW : ContDiffWithinAt 𝕜 n W s x) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 m (lieBracketWithin 𝕜 V W s) s x := by
  apply ContDiffWithinAt.sub
  · exact ContDiffWithinAt.clm_apply (hW.fderivWithin_right hs hmn hx)
      (hV.of_le (le_trans le_self_add hmn))
  · exact ContDiffWithinAt.clm_apply (hV.fderivWithin_right hs hmn hx)
      (hW.of_le (le_trans le_self_add hmn))

lemma _root_.ContDiffAt.lieBracket_vectorField {m n : ℕ∞} (hV : ContDiffAt 𝕜 n V x)
    (hW : ContDiffAt 𝕜 n W x) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (lieBracket 𝕜 V W) x := by
  rw [← contDiffWithinAt_univ] at hV hW ⊢
  simp_rw [← lieBracketWithin_univ]
  exact hV.lieBracketWithin_vectorField hW uniqueDiffOn_univ hmn (mem_univ _)

lemma _root_.ContDiffOn.lieBracketWithin_vectorField {m n : ℕ∞} (hV : ContDiffOn 𝕜 n V s)
    (hW : ContDiffOn 𝕜 n W s) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (lieBracketWithin 𝕜 V W s) s :=
  fun x hx ↦ (hV x hx).lieBracketWithin_vectorField (hW x hx) hs hmn hx

lemma _root_.ContDiff.lieBracket_vectorField {m n : ℕ∞} (hV : ContDiff 𝕜 n V)
    (hW : ContDiff 𝕜 n W) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m (lieBracket 𝕜 V W) :=
  contDiff_iff_contDiffAt.2 (fun _ ↦ hV.contDiffAt.lieBracket_vectorField hW.contDiffAt hmn)

theorem lieBracketWithin_of_mem (st : t ∈ 𝓝[s] x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x := by
  simp [lieBracketWithin, fderivWithin_of_mem st hs hV, fderivWithin_of_mem st hs hW]

theorem lieBracketWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x :=
  lieBracketWithin_of_mem (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW

theorem lieBracketWithin_inter (ht : t ∈ 𝓝 x) :
    lieBracketWithin 𝕜 V W (s ∩ t) x = lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, fderivWithin_inter, ht]

theorem lieBracketWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x := by
  rw [← lieBracketWithin_univ, ← univ_inter s, lieBracketWithin_inter h]

theorem lieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x :=
  lieBracketWithin_of_mem_nhds (hs.mem_nhds hx)

theorem lieBracketWithin_eq_lieBracket (hs : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x := by
  simp [lieBracketWithin, lieBracket, fderivWithin_eq_fderiv, hs, hV, hW]

/-- Variant of `lieBracketWithin_congr_set` where one requires the sets to coincide only in
the complement of a point. -/
theorem lieBracketWithin_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x := by
  simp [lieBracketWithin, fderivWithin_congr_set' _ h]

theorem lieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x :=
  lieBracketWithin_congr_set' x <| h.filter_mono inf_le_left

/-- Variant of `lieBracketWithin_eventually_congr_set` where one requires the sets to coincide only
in  the complement of a point. -/
theorem lieBracketWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lieBracketWithin 𝕜 V W s =ᶠ[𝓝 x] lieBracketWithin 𝕜 V W t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => lieBracketWithin_congr_set' y

theorem lieBracketWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    lieBracketWithin 𝕜 V W s =ᶠ[𝓝 x] lieBracketWithin 𝕜 V W t :=
  lieBracketWithin_eventually_congr_set' x <| h.filter_mono inf_le_left

theorem _root_.DifferentiableWithinAt.lieBracketWithin_congr_mono
    (hV : DifferentiableWithinAt 𝕜 V s x) (hVs : EqOn V₁ V t) (hVx : V₁ x = V x)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hWs : EqOn W₁ W t) (hWx : W₁ x = W x)
    (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t ⊆ s) :
    lieBracketWithin 𝕜 V₁ W₁ t x = lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, hV.fderivWithin_congr_mono, hW.fderivWithin_congr_mono, hVs, hVx,
    hWs, hWx, hxt, h₁]

theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x) (hW : W₁ =ᶠ[𝓝[s] x] W) (hxW : W₁ x = W x) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x := by
  simp only [lieBracketWithin, hV.fderivWithin_eq hxV, hW.fderivWithin_eq hxW, hxV, hxW]

theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  hV.lieBracketWithin_vectorField_eq (mem_of_mem_nhdsWithin hx hV :)
    hW (mem_of_mem_nhdsWithin hx hW :)

/-- If vector fields coincide on a neighborhood of a point within a set, then the Lie brackets
also coincide on a neighborhood of this point within this set. Version where one considers the Lie
bracket within a subset. -/
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField'
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (ht : t ⊆ s) :
    lieBracketWithin 𝕜 V₁ W₁ t =ᶠ[𝓝[s] x] lieBracketWithin 𝕜 V W t := by
  filter_upwards [hV.fderivWithin' ht (𝕜 := 𝕜), hW.fderivWithin' ht (𝕜 := 𝕜), hV, hW]
    with x hV' hW' hV hW
  simp [lieBracketWithin, hV', hW', hV, hW]

protected theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s =ᶠ[𝓝[s] x] lieBracketWithin 𝕜 V W s :=
  hV.lieBracketWithin_vectorField' hW Subset.rfl

protected theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_insert
    (hV : V₁ =ᶠ[𝓝[insert x s] x] V) (hW : W₁ =ᶠ[𝓝[insert x s] x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x := by
  apply mem_of_mem_nhdsWithin (mem_insert x s) (hV.lieBracketWithin_vectorField' hW
    (subset_insert x s))

theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  (hV.filter_mono nhdsWithin_le_nhds).lieBracketWithin_vectorField_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds

theorem lieBracketWithin_congr
    (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  (hV.eventuallyEq.filter_mono inf_le_right).lieBracketWithin_vectorField_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

/-- Version of `lieBracketWithin_congr` in which one assumes that the point belongs to the
given set. -/
theorem lieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  lieBracketWithin_congr hV (hV hx) hW (hW hx)

theorem _root_.Filter.EventuallyEq.lieBracket_vectorField_eq
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    lieBracket 𝕜 V₁ W₁ x = lieBracket 𝕜 V W x := by
  rw [← lieBracketWithin_univ, ← lieBracketWithin_univ, hV.lieBracketWithin_vectorField_eq_nhds hW]

protected theorem _root_.Filter.EventuallyEq.lieBracket_vectorField
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) : lieBracket 𝕜 V₁ W₁ =ᶠ[𝓝 x] lieBracket 𝕜 V W := by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.lieBracket_vectorField_eq hWy

variable (𝕜) in
/-- The Lie derivative of a function with respect to a vector field `L_V f(x)`. This is just
`Df(x) (V x)`, but the notation emphasizes how this is linear in `f`.-/
def lieDeriv (V : E → E) (f : E → F) (x : E) : F := fderiv 𝕜 f x (V x)

lemma lieDeriv_eq (V : E → E) (f : E → F) : lieDeriv 𝕜 V f = fun x ↦ fderiv 𝕜 f x (V x) := rfl

/-- The equation `L_V L_W f - L_W L_V f = L_{[V, W]} f`, which is the motivation for the definition
of the Lie bracket. This requires the second derivative of `f` to be symmetric. -/
lemma sub_eq_lieDeriv_lieBracket {V W : E → E} {f : E → F} {x : E} (hf : IsSymmSndFDerivAt 𝕜 f x)
    (h'f : ContDiffAt 𝕜 2 f x) (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x) :
    lieDeriv 𝕜 V (lieDeriv 𝕜 W f) x - lieDeriv 𝕜 W (lieDeriv 𝕜 V f) x =
      lieDeriv 𝕜 (lieBracket 𝕜 V W) f x := by
  have A : DifferentiableAt 𝕜 (fderiv 𝕜 f) x :=
    (h'f.fderiv_right (m := 1) le_rfl).differentiableAt le_rfl
  simp only [lieDeriv_eq, lieBracket_eq]
  rw [fderiv_clm_apply A hV, fderiv_clm_apply A hW]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.flip_apply, map_sub, hf.eq]
  abel

variable (𝕜) in
/-- The pullback of a vector field under a function, defined
as `(f^* V) (x) = Df(x)^{-1} (V (f x))`. If `Df(x)` is not invertible, we use the junk value `0`.
-/
def pullback (f : E → F) (V : F → F) (x : E) : E := (fderiv 𝕜 f x).inverse (V (f x))

variable (𝕜) in
/-- The pullback of a vector field under a function, defined
as `(f^* V) (x) = Df(x)^{-1} (V (f x))`. If `Df(x)` is not invertible, we use the junk value `0`.
-/
def pullbackWithin (f : E → F) (V : F → F) (s : Set E) (x : E) : E :=
  (fderivWithin 𝕜 f s x).inverse (V (f x))

lemma pullbackWithin_eq {f : E → F} {V : F → F} {s : Set E} :
    pullbackWithin 𝕜 f V s = fun x ↦ (fderivWithin 𝕜 f s x).inverse (V (f x)) := rfl

lemma pullback_eq_of_fderiv_eq
    {f : E → F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderiv 𝕜 f x) (V : F → F) :
    pullback 𝕜 f V x = M.symm (V (f x)) := by
  simp [pullback, ← hf]

lemma pullback_eq_of_not_isInvertible {f : E → F} {x : E}
    (h : ¬(fderiv 𝕜 f x).IsInvertible) (V : F → F) :
    pullback 𝕜 f V x = 0 := by
  simp only [ContinuousLinearMap.IsInvertible] at h
  simp [pullback, h]

lemma pullbackWithin_eq_of_not_isInvertible {f : E → F} {x : E}
    (h : ¬(fderivWithin 𝕜 f s x).IsInvertible) (V : F → F) :
    pullbackWithin 𝕜 f V s x = 0 := by
  simp only [ContinuousLinearMap.IsInvertible] at h
  simp [pullbackWithin, h]

lemma pullbackWithin_eq_of_fderivWithin_eq
    {f : E → F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderivWithin 𝕜 f s x) (V : F → F) :
    pullbackWithin 𝕜 f V s x = M.symm (V (f x)) := by
  simp [pullbackWithin, ← hf]

@[simp] lemma pullbackWithin_univ {f : E → F} {V : F → F} :
    pullbackWithin 𝕜 f V univ = pullback 𝕜 f V := by
  ext x
  simp [pullbackWithin, pullback]

open scoped Topology Filter

lemma fderiv_pullback (f : E → F) (V : F → F) (x : E) (h'f : (fderiv 𝕜 f x).IsInvertible) :
    fderiv 𝕜 f x (pullback 𝕜 f V x) = V (f x) := by
  rcases h'f with ⟨M, hM⟩
  simp [pullback_eq_of_fderiv_eq hM, ← hM]

lemma fderivWithin_pullbackWithin {f : E → F} {V : F → F} {x : E}
    (h'f : (fderivWithin 𝕜 f s x).IsInvertible) :
    fderivWithin 𝕜 f s x (pullbackWithin 𝕜 f V s x) = V (f x) := by
  rcases h'f with ⟨M, hM⟩
  simp [pullbackWithin_eq_of_fderivWithin_eq hM, ← hM]

/-- The equation `L_{f^* V} (g ∘ f) (x) = (L_V g) (f x)`, which is essentially the definition of
the pullback.
Note that `hf` can probably be removed, as it's implied by `h'f`.
-/
lemma lieDeriv_pullback (f : E → F) (V : F → F) (g : F → G) (x : E)
    (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) (h'f : (fderiv 𝕜 f x).IsInvertible) :
    lieDeriv 𝕜 (pullback 𝕜 f V) (g ∘ f) x = lieDeriv 𝕜 V g (f x) := by
  rcases h'f with ⟨M, hM⟩
  rw [lieDeriv, lieDeriv, fderiv.comp _ hg hf]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  rw [fderiv_pullback]
  exact ⟨M, hM⟩

lemma leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt
    {U V W : E → E} {s : Set E} {x : E} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s)
    (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x)
    (hW : ContDiffWithinAt 𝕜 2 W s x)
    (h'U : IsSymmSndFDerivWithinAt 𝕜 U s x) (h'V : IsSymmSndFDerivWithinAt 𝕜 V s x)
    (h'W : IsSymmSndFDerivWithinAt 𝕜 W s x) :
    lieBracketWithin 𝕜 U (lieBracketWithin 𝕜 V W s) s x =
      lieBracketWithin 𝕜 (lieBracketWithin 𝕜 U V s) W s x
      + lieBracketWithin 𝕜 V (lieBracketWithin 𝕜 U W s) s x := by
  simp only [lieBracketWithin_eq, map_sub]
  rw [fderivWithin_sub (hs x hx)]; rotate_left
  · apply ContDiffWithinAt.differentiableWithinAt _ le_rfl
    exact hW.fderivWithin_right_apply (hV.of_le one_le_two) hs le_rfl hx
  · apply ContDiffWithinAt.differentiableWithinAt _ le_rfl
    exact hV.fderivWithin_right_apply (hW.of_le one_le_two) hs le_rfl hx
  rw [fderivWithin_sub (hs x hx)]; rotate_left
  · apply ContDiffWithinAt.differentiableWithinAt _ le_rfl
    exact hV.fderivWithin_right_apply (hU.of_le one_le_two) hs le_rfl hx
  · apply ContDiffWithinAt.differentiableWithinAt _ le_rfl
    exact hU.fderivWithin_right_apply (hV.of_le one_le_two) hs le_rfl hx
  rw [fderivWithin_sub (hs x hx)]; rotate_left
  · apply ContDiffWithinAt.differentiableWithinAt _ le_rfl
    exact hW.fderivWithin_right_apply (hU.of_le one_le_two) hs le_rfl hx
  · apply ContDiffWithinAt.differentiableWithinAt _ le_rfl
    exact hU.fderivWithin_right_apply (hW.of_le one_le_two) hs le_rfl hx
  rw [fderivWithin_clm_apply (hs x hx)]; rotate_left
  · apply ContDiffWithinAt.differentiableWithinAt _ le_rfl
    exact hW.fderivWithin_right hs le_rfl hx
  · exact ContDiffWithinAt.differentiableWithinAt hV one_le_two
  rw [fderivWithin_clm_apply (hs x hx)]; rotate_left
  · apply ContDiffWithinAt.differentiableWithinAt _ le_rfl
    exact hV.fderivWithin_right hs le_rfl hx
  · exact ContDiffWithinAt.differentiableWithinAt hW one_le_two
  rw [fderivWithin_clm_apply (hs x hx)]; rotate_left
  · apply ContDiffWithinAt.differentiableWithinAt _ le_rfl
    exact hV.fderivWithin_right hs le_rfl hx
  · exact ContDiffWithinAt.differentiableWithinAt hU one_le_two
  rw [fderivWithin_clm_apply (hs x hx)]; rotate_left
  · apply ContDiffWithinAt.differentiableWithinAt _ le_rfl
    exact hU.fderivWithin_right hs le_rfl hx
  · exact ContDiffWithinAt.differentiableWithinAt hV one_le_two
  rw [fderivWithin_clm_apply (hs x hx)]; rotate_left
  · apply ContDiffWithinAt.differentiableWithinAt _ le_rfl
    exact hW.fderivWithin_right hs le_rfl hx
  · exact ContDiffWithinAt.differentiableWithinAt hU one_le_two
  rw [fderivWithin_clm_apply (hs x hx)]; rotate_left
  · apply ContDiffWithinAt.differentiableWithinAt _ le_rfl
    exact hU.fderivWithin_right hs le_rfl hx
  · exact ContDiffWithinAt.differentiableWithinAt hW one_le_two
  simp only [ContinuousLinearMap.coe_sub', Pi.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.flip_apply, h'V.eq,
    h'U.eq, h'W.eq]
  abel

lemma leibniz_identity_lieBracketWithin [IsRCLikeNormedField 𝕜] {U V W : E → E} {s : Set E} {x : E}
    (hs : UniqueDiffOn 𝕜 s) (h'x : x ∈ closure (interior s)) (hx : x ∈ s)
    (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x)
    (hW : ContDiffWithinAt 𝕜 2 W s x) :
    lieBracketWithin 𝕜 U (lieBracketWithin 𝕜 V W s) s x =
      lieBracketWithin 𝕜 (lieBracketWithin 𝕜 U V s) W s x
      + lieBracketWithin 𝕜 V (lieBracketWithin 𝕜 U W s) s x := by
  apply leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt hs hx hU hV hW
  · exact hU.isSymmSndFDerivWithinAt le_rfl hs h'x hx
  · exact hV.isSymmSndFDerivWithinAt le_rfl hs h'x hx
  · exact hW.isSymmSndFDerivWithinAt le_rfl hs h'x hx

lemma leibniz_identity_lieBracket [IsRCLikeNormedField 𝕜] {U V W : E → E} {x : E}
    (hU : ContDiffAt 𝕜 2 U x) (hV : ContDiffAt 𝕜 2 V x) (hW : ContDiffAt 𝕜 2 W x) :
    lieBracket 𝕜 U (lieBracket 𝕜 V W) x =
      lieBracket 𝕜 (lieBracket 𝕜 U V) W x + lieBracket 𝕜 V (lieBracket 𝕜 U W) x := by
  simp only [← lieBracketWithin_univ, ← contDiffWithinAt_univ] at hU hV hW ⊢
  exact leibniz_identity_lieBracketWithin uniqueDiffOn_univ (by simp) (mem_univ _) hU hV hW

open Set

variable [CompleteSpace E]

/- TODO: move me -/

/-- If a `C^2` map has an invertible derivative within a set at a point, then nearby derivatives
can be written as continuous linear equivs, which depend in a `C^1` way on the point, as well as
their inverse, and moreover one can compute the derivative of the inverse. -/
lemma _root_.exists_continuousLinearEquiv_fderivWithin_symm_eq
    {f : E → F} {s : Set E} {x : E} (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hf : (fderivWithin 𝕜 f s x).IsInvertible) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    ∃ N : E → (E ≃L[𝕜] F), ContDiffWithinAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) s x
    ∧ ContDiffWithinAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x
    ∧ (∀ᶠ y in 𝓝[s] x, N y = fderivWithin 𝕜 f s y)
    ∧ ∀ v, fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x v
      = - (N x).symm  ∘L ((fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v)) ∘L (N x).symm := by
  classical
  rcases hf with ⟨M, hM⟩
  let U := {y | ∃ (N : E ≃L[𝕜] F), N = fderivWithin 𝕜 f s y}
  have hU : U ∈ 𝓝[s] x := by
    have I : range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (fderivWithin 𝕜 f s x) := by
      rw [← hM]
      exact M.nhds
    have : ContinuousWithinAt (fderivWithin 𝕜 f s) s x :=
      (h'f.fderivWithin_right (m := 1) hs le_rfl hx).continuousWithinAt
    exact this I
  let N : E → (E ≃L[𝕜] F) := fun x ↦ if h : x ∈ U then h.choose else M
  have eN : (fun y ↦ (N y : E →L[𝕜] F)) =ᶠ[𝓝[s] x] fun y ↦ fderivWithin 𝕜 f s y := by
    filter_upwards [hU] with y hy
    simpa only [hy, ↓reduceDIte, N] using Exists.choose_spec hy
  have e'N : N x = fderivWithin 𝕜 f s x := by apply mem_of_mem_nhdsWithin hx eN
  have hN : ContDiffWithinAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) s x := by
    have : ContDiffWithinAt 𝕜 1 (fun y ↦ fderivWithin 𝕜 f s y) s x :=
      h'f.fderivWithin_right (m := 1) hs le_rfl hx
    apply this.congr_of_eventuallyEq eN e'N
  have hN' : ContDiffWithinAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x := by
    have : ContDiffWithinAt 𝕜 1 (ContinuousLinearMap.inverse ∘ (fun y ↦ (N y : E →L[𝕜] F))) s x :=
      (contDiffAt_map_inverse (N x)).comp_contDiffWithinAt x hN
    convert this with y
    simp only [Function.comp_apply, ContinuousLinearMap.inverse_equiv]
  refine ⟨N, hN, hN', eN, fun v ↦ ?_⟩
  have A' y : ContinuousLinearMap.compL 𝕜 F E F (N y : E →L[𝕜] F) ((N y).symm : F →L[𝕜] E)
      = ContinuousLinearMap.id 𝕜 F := by ext; simp
  have : fderivWithin 𝕜 (fun y ↦ ContinuousLinearMap.compL 𝕜 F E F (N y : E →L[𝕜] F)
      ((N y).symm : F →L[𝕜] E)) s x v = 0 := by
    simp [A', fderivWithin_const_apply, hs x hx]
  have I : (N x : E →L[𝕜] F) ∘L (fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x v) =
      - (fderivWithin 𝕜 (fun y ↦ (N y : E →L[𝕜] F)) s x v) ∘L ((N x).symm : F →L[𝕜] E) := by
    rw [ContinuousLinearMap.fderivWithin_of_bilinear _ (hN.differentiableWithinAt le_rfl)
      (hN'.differentiableWithinAt le_rfl) (hs x hx)] at this
    simpa [eq_neg_iff_add_eq_zero] using this
  have B (M : F →L[𝕜] E) : M = ((N x).symm : F →L[𝕜] E) ∘L ((N x) ∘L M) := by
    ext; simp
  rw [B (fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x v), I]
  simp only [ContinuousLinearMap.comp_neg, neg_inj, eN.fderivWithin_eq e'N]

/-- If a `C^2` map has an invertible derivative at a point, then nearby derivatives can be written
as continuous linear equivs, which depend in a `C^1` way on the point, as well as their inverse, and
moreover one can compute the derivative of the inverse. -/
lemma _root_.exists_continuousLinearEquiv_fderiv_symm_eq
    {f : E → F} {x : E} (h'f : ContDiffAt 𝕜 2 f x) (hf : (fderiv 𝕜 f x).IsInvertible) :
    ∃ N : E → (E ≃L[𝕜] F), ContDiffAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) x
    ∧ ContDiffAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x
    ∧ (∀ᶠ y in 𝓝 x, N y = fderiv 𝕜 f y)
    ∧ ∀ v, fderiv 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x v
      = - (N x).symm  ∘L ((fderiv 𝕜 (fderiv 𝕜 f) x v)) ∘L (N x).symm := by
  simp only [← fderivWithin_univ, ← contDiffWithinAt_univ, ← nhdsWithin_univ] at hf h'f ⊢
  exact exists_continuousLinearEquiv_fderivWithin_symm_eq h'f hf uniqueDiffOn_univ (mem_univ _)

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeo. -/
lemma lieBracketWithin_pullbackWithin {f : E → F} {V W : F → F} {x : E} {t : Set F}
    (hf : IsSymmSndFDerivWithinAt 𝕜 f s x) (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x =
      pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x := by
  by_cases h : (fderivWithin 𝕜 f s x).IsInvertible; swap
  · simp [pullbackWithin_eq_of_not_isInvertible h, lieBracketWithin_eq]
  rcases exists_continuousLinearEquiv_fderivWithin_symm_eq h'f h hu hx
    with ⟨M, -, M_symm_smooth, hM, M_diff⟩
  have hMx : M x = fderivWithin 𝕜 f s x := (mem_of_mem_nhdsWithin hx hM :)
  have AV : fderivWithin 𝕜 (pullbackWithin 𝕜 f V s) s x =
      fderivWithin 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (V (f y))) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
    filter_upwards [hM] with y hy using pullbackWithin_eq_of_fderivWithin_eq hy _
  have AW : fderivWithin 𝕜 (pullbackWithin 𝕜 f W s) s x =
      fderivWithin 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (W (f y))) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
    filter_upwards [hM] with y hy using pullbackWithin_eq_of_fderivWithin_eq hy _
  have Af : DifferentiableWithinAt 𝕜 f s x := h'f.differentiableWithinAt one_le_two
  simp only [lieBracketWithin_eq, pullbackWithin_eq_of_fderivWithin_eq hMx, map_sub, AV, AW]
  rw [fderivWithin_clm_apply, fderivWithin_clm_apply]
  · simp [fderivWithin.comp' x hW Af hst (hu x hx), ← hMx,
      fderivWithin.comp' x hV Af hst (hu x hx), M_diff, hf.eq]
  · exact hu x hx
  · exact M_symm_smooth.differentiableWithinAt le_rfl
  · exact hV.comp x Af hst
  · exact hu x hx
  · exact M_symm_smooth.differentiableWithinAt le_rfl
  · exact hW.comp x Af hst

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeo. Variant where unique differentiability and
the invariance property are only required in a smaller set `u`. -/
lemma lieBracketWithin_pullbackWithin_of_eventuallyEq
    {f : E → F} {V W : F → F} {x : E} {t : Set F} {u : Set E}
    (hf : IsSymmSndFDerivWithinAt 𝕜 f s x) (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 u) (hx : x ∈ u) (hst : MapsTo f u t) (hus : u =ᶠ[𝓝 x] s) :
    lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x =
      pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x := calc
  lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x =
      lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) u x :=
    lieBracketWithin_congr_set hus.symm
  _ = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V u) (pullbackWithin 𝕜 f W u) u x := by
    apply Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem _ _ hx
    · apply nhdsWithin_le_nhds
      filter_upwards [fderivWithin_eventually_congr_set (𝕜 := 𝕜) (f := f) hus] with y hy
      simp [pullbackWithin, hy]
    · apply nhdsWithin_le_nhds
      filter_upwards [fderivWithin_eventually_congr_set (𝕜 := 𝕜) (f := f) hus] with y hy
      simp [pullbackWithin, hy]
  _ = pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) u x :=
    lieBracketWithin_pullbackWithin (hf.congr_set hus.symm) (h'f.congr_set hus.symm)
      hV hW hu hx hst
  _ = pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x := by
    simp only [pullbackWithin]
    congr 2
    exact fderivWithin_congr_set hus

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeo. -/
lemma lieBracket_pullback {f : E → F} {V W : F → F} {x : E}
    (hf : IsSymmSndFDerivAt 𝕜 f x) (h'f : ContDiffAt 𝕜 2 f x)
    (hV : DifferentiableAt 𝕜 V (f x)) (hW : DifferentiableAt 𝕜 W (f x)) :
    lieBracket 𝕜 (pullback 𝕜 f V) (pullback 𝕜 f W) x = pullback 𝕜 f (lieBracket 𝕜 V W) x := by
  simp only [← lieBracketWithin_univ, ← pullbackWithin_univ, ← isSymmSndFDerivWithinAt_univ,
    ← differentiableWithinAt_univ] at hf h'f hV hW ⊢
  exact lieBracketWithin_pullbackWithin hf h'f hV hW uniqueDiffOn_univ
    (mem_univ _) (mapsTo_univ _ _)

lemma DifferentiableWithinAt.pullbackWithin {f : E → F} {V : F → F} {s : Set E} {t : Set F} {x : E}
    (hV : DifferentiableWithinAt 𝕜 V t (f x))
    (hf : ContDiffWithinAt 𝕜 2 f s x) (hf' : (fderivWithin 𝕜 f s x).IsInvertible)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    DifferentiableWithinAt 𝕜 (pullbackWithin 𝕜 f V s) s x := by
  rcases exists_continuousLinearEquiv_fderivWithin_symm_eq hf hf' hs hx
    with ⟨M, -, M_symm_smooth, hM, -⟩
  simp only [pullbackWithin_eq]
  have : DifferentiableWithinAt 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (V (f y))) s x := by
    apply DifferentiableWithinAt.clm_apply
    · exact M_symm_smooth.differentiableWithinAt le_rfl
    · exact hV.comp _ (hf.differentiableWithinAt one_le_two) hst
  apply this.congr_of_eventuallyEq
  · filter_upwards [hM] with y hy using by simp [← hy]
  · have hMx : M x = fderivWithin 𝕜 f s x := by apply mem_of_mem_nhdsWithin hx hM
    simp [← hMx]

end VectorField

end LieBracketVectorField

section LieBracketManifold

open Set Function
open scoped Manifold

/- We work in the `VectorField` namespace because pullbacks, Lie brackets, and so on, are notions
that make sense in a variety of contexts. We also prefix the notions with `m` to distinguish the
manifold notions from the vector spaces notions. For instance, the Lie bracket of two vector
fields in a manifold is denoted with `mlieBracket I V W x`, where `I` is the relevant model with
corners, `V W : Π (x : M), TangentSpace I x` are the vector fields, and `x : M` is the basepoint.
-/
namespace VectorField


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {H'' : Type*} [TopologicalSpace H''] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']

variable {f : M → M'} {s t : Set M} {x x₀ : M}

section

variable {V W V₁ W₁ : Π (x : M'), TangentSpace I' x}
variable {m n : ℕ∞} {t : Set M'} {y₀ : M'}

variable (I I') in
/-- The pullback of a vector field under a map between manifolds, within a set `s`. -/
def mpullbackWithin (f : M → M') (V : Π (x : M'), TangentSpace I' x) (s : Set M) (x : M) :
    TangentSpace I x :=
  (mfderivWithin I I' f s x).inverse (V (f x))

variable (I I') in
/-- The pullback of a vector field under a map between manifolds. -/
def mpullback (f : M → M') (V : Π (x : M'), TangentSpace I' x) (x : M) :
    TangentSpace I x :=
  (mfderiv I I' f x).inverse (V (f x))

lemma mpullbackWithin_apply :
    mpullbackWithin I I' f V s x = (mfderivWithin I I' f s x).inverse (V (f x)) := rfl

lemma mpullbackWithin_add_apply :
    mpullbackWithin I I' f (V + V₁) s x =
      mpullbackWithin I I' f V s x + mpullbackWithin I I' f V₁ s x := by
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_add :
    mpullbackWithin I I' f (V + V₁) s =
      mpullbackWithin I I' f V s + mpullbackWithin I I' f V₁ s := by
  ext x
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_neg_apply :
    mpullbackWithin I I' f (-V) s x = - mpullbackWithin I I' f V s x := by
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_neg :
    mpullbackWithin I I' f (-V) s = - mpullbackWithin I I' f V s := by
  ext x
  simp [mpullbackWithin_apply]

lemma mpullback_apply :
    mpullback I I' f V x = (mfderiv I I' f x).inverse (V (f x)) := rfl

lemma mpullback_add_apply :
    mpullback I I' f (V + V₁) x = mpullback I I' f V x + mpullback I I' f V₁ x := by
  simp [mpullback_apply]

lemma mpullback_add :
    mpullback I I' f (V + V₁) = mpullback I I' f V + mpullback I I' f V₁ := by
  ext x
  simp [mpullback_apply]

lemma mpullback_neg_apply :
    mpullback I I' f (-V) x = - mpullback I I' f V x := by
  simp [mpullback_apply]

lemma mpullback_neg :
    mpullback I I' f (-V) = - mpullback I I' f V := by
  ext x
  simp [mpullback_apply]

@[simp] lemma mpullbackWithin_univ : mpullbackWithin I I' f V univ = mpullback I I' f V := by
  ext x
  simp [mpullback_apply, mpullbackWithin_apply]

lemma mpullbackWithin_eq_pullbackWithin {f : E → E'} {V : E' → E'} {s : Set E} :
    mpullbackWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f V s = pullbackWithin 𝕜 f V s := by
  ext x
  simp only [mpullbackWithin, mfderivWithin_eq_fderivWithin, pullbackWithin]
  rfl

@[simp] lemma mpullback_id {V : Π (x : M), TangentSpace I x} : mpullback I I id V = V := by
  ext x
  simp [mpullback]

open ContinuousLinearMap

/-! ### Smoothness of pullback of vector fields -/
section

variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M'] [CompleteSpace E]

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version within a set at a point. -/
protected lemma _root_.MDifferentiableWithinAt.mpullbackWithin_vectorField
    (hV : MDifferentiableWithinAt I' I'.tangent
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : 2 ≤ n) :
    MDifferentiableWithinAt I I.tangent
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f ⁻¹' t) x₀ := by
  /- We want to apply the general theorem `MDifferentiableWithinAt.clm_apply_of_inCoordinates`,
  stating that applying linear maps to vector fields gives a smooth result when the linear map and
  the vector field are smooth. This theorem is general, we will apply it to
  `b₁ = f`, `b₂ = id`, `v = V ∘ f`, `ϕ = fun x ↦ (mfderivWithin I I' f s x).inverse`-/
  let b₁ := f
  let b₂ : M → M := id
  let v : Π (x : M), TangentSpace I' (f x) := V ∘ f
  let ϕ : Π (x : M), TangentSpace I' (f x) →L[𝕜] TangentSpace I x :=
    fun x ↦ (mfderivWithin I I' f s x).inverse
  have hv : MDifferentiableWithinAt I I'.tangent
      (fun x ↦ (v x : TangentBundle I' M')) (s ∩ f ⁻¹' t) x₀ := by
    apply hV.comp x₀ ((hf.mdifferentiableWithinAt (one_le_two.trans hmn)).mono inter_subset_left)
    exact MapsTo.mono_left (mapsTo_preimage _ _) inter_subset_right
  /- The only nontrivial fact, from which the conclusion follows, is
  that `ϕ` depends smoothly on `x`. -/
  suffices hϕ : MDifferentiableWithinAt I 𝓘(𝕜, E' →L[𝕜] E)
      (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E' (TangentSpace I' (M := M')) E (TangentSpace I (M := M))
        (b₁ x₀) (b₁ x) (b₂ x₀) (b₂ x) (ϕ x)) s x₀ from
    MDifferentiableWithinAt.clm_apply_of_inCoordinates (hϕ.mono inter_subset_left)
      hv mdifferentiableWithinAt_id
  /- To prove that `ϕ` depends smoothly on `x`, we use that the derivative depends smoothly on `x`
  (this is `ContMDiffWithinAt.mfderivWithin_const`), and that taking the inverse is a smooth
  operation at an invertible map. -/
  -- the derivative in coordinates depends smoothly on the point
  have : MDifferentiableWithinAt I 𝓘(𝕜, E →L[𝕜] E')
      (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderivWithin I I' f s x)) s x₀ :=
    (hf.mfderivWithin_const hmn hx₀ hs).mdifferentiableWithinAt le_rfl
  -- therefore, its inverse in coordinates also depends smoothly on the point
  have : MDifferentiableWithinAt I 𝓘(𝕜, E' →L[𝕜] E)
      (ContinuousLinearMap.inverse ∘ (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderivWithin I I' f s x))) s x₀ := by
    apply MDifferentiableAt.comp_mdifferentiableWithinAt _ _ this
    apply ContMDiffAt.mdifferentiableAt _ le_rfl
    apply ContDiffAt.contMDiffAt
    apply IsInvertible.contDiffAt_map_inverse
    rw [inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' x₀)
      (FiberBundle.mem_baseSet_trivializationAt' (f x₀))]
    exact isInvertible_equiv.comp (hf'.comp isInvertible_equiv)
  -- the inverse in coordinates coincides with the in-coordinate version of the inverse,
  -- therefore the previous point gives the conclusion
  apply this.congr_of_eventuallyEq_of_mem _ hx₀
  have A : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝[s] x₀ := by
    apply nhdsWithin_le_nhds
    apply (trivializationAt _ _ _).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' _
  have B : f ⁻¹' (trivializationAt E' (TangentSpace I') (f x₀)).baseSet ∈ 𝓝[s] x₀ := by
    apply hf.continuousWithinAt.preimage_mem_nhdsWithin
    apply (trivializationAt _ _ _).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' _
  filter_upwards [A, B] with x hx h'x
  simp only [Function.comp_apply]
  rw [inCoordinates_eq hx h'x, inCoordinates_eq h'x (by exact hx)]
  simp only [inverse_equiv_comp, inverse_comp_equiv, ContinuousLinearEquiv.symm_symm, ϕ]
  rfl

lemma _root_.MDifferentiableWithinAt.mpullbackWithin_vectorField_of_eq
    (hV : MDifferentiableWithinAt I' I'.tangent
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : 2 ≤ n) (h : y₀ = f x₀) :
    MDifferentiableWithinAt I I.tangent
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f⁻¹' t) x₀ := by
  subst h
  exact hV.mpullbackWithin_vectorField hf hf' hx₀ hs hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version on a set. -/
protected lemma _root_.MDifferentiableOn.mpullbackWithin_vectorField
    (hV : MDifferentiableOn I' I'.tangent (fun (y : M') ↦ (V y : TangentBundle I' M')) t)
    (hf : ContMDiffOn I I' n f s) (hf' : ∀ x ∈ s ∩ f ⁻¹' t, (mfderivWithin I I' f s x).IsInvertible)
    (hs : UniqueMDiffOn I s) (hmn : 2 ≤ n) :
    MDifferentiableOn I I.tangent
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f ⁻¹' t) :=
  fun _ hx₀ ↦ MDifferentiableWithinAt.mpullbackWithin_vectorField
    (hV _ hx₀.2) (hf _ hx₀.1) (hf' _ hx₀) hx₀.1 hs hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version within a set at a point, but with full pullback. -/
protected lemma _root_.MDifferentiableWithinAt.mpullback_vectorField
    (hV : MDifferentiableWithinAt I' I'.tangent
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : 2 ≤ n) :
    MDifferentiableWithinAt I I.tangent
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) x₀ := by
  simp only [← contMDiffWithinAt_univ, ← mfderivWithin_univ, ← mpullbackWithin_univ] at hV hf hf' ⊢
  simpa using hV.mpullbackWithin_vectorField hf hf' (mem_univ _) uniqueMDiffOn_univ hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version within a set at a point, but with full pullback. -/
protected lemma _root_.MDifferentiableWithinAt.mpullback_vectorField_of_eq
    (hV : MDifferentiableWithinAt I' I'.tangent (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : 2 ≤ n)
    (hy₀ : y₀ = f x₀) :
    MDifferentiableWithinAt I I.tangent
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) x₀ := by
  subst hy₀
  exact hV.mpullback_vectorField hf hf' hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version on a set, but with full pullback -/
protected lemma _root_.MDifferentiableOn.mpullback_vectorField
    (hV : MDifferentiableOn I' I'.tangent (fun (y : M') ↦ (V y : TangentBundle I' M')) t)
    (hf : ContMDiff I I' n f) (hf' : ∀ x ∈ f ⁻¹' t, (mfderiv I I' f x).IsInvertible)
    (hmn : 2 ≤ n) :
    MDifferentiableOn I I.tangent
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) :=
  fun x₀ hx₀ ↦ MDifferentiableWithinAt.mpullback_vectorField (hV _ hx₀) (hf x₀) (hf' _ hx₀) hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version at a point. -/
protected lemma _root_.MDifferentiableAt.mpullback_vectorField
    (hV : MDifferentiableAt I' I'.tangent (fun (y : M') ↦ (V y : TangentBundle I' M')) (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : 2 ≤ n) :
    MDifferentiableAt I I.tangent
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) x₀ := by
  simpa using MDifferentiableWithinAt.mpullback_vectorField hV hf hf' hmn

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. -/
protected lemma _root_.MDifferentiable.mpullback_vectorField
    (hV : MDifferentiable I' I'.tangent (fun (y : M') ↦ (V y : TangentBundle I' M')))
    (hf : ContMDiff I I' n f) (hf' : ∀ x, (mfderiv I I' f x).IsInvertible) (hmn : 2 ≤ n) :
    MDifferentiable I I.tangent (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) :=
  fun x ↦ MDifferentiableAt.mpullback_vectorField (hV (f x)) (hf x) (hf' x) hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_inter
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f ⁻¹' t) x₀ := by
  /- We want to apply the general theorem `ContMDiffWithinAt.clm_apply_of_inCoordinates`, stating
  that applying linear maps to vector fields gives a smooth result when the linear map and the
  vector field are smooth. This theorem is general, we will apply it to
  `b₁ = f`, `b₂ = id`, `v = V ∘ f`, `ϕ = fun x ↦ (mfderivWithin I I' f s x).inverse`-/
  let b₁ := f
  let b₂ : M → M := id
  let v : Π (x : M), TangentSpace I' (f x) := V ∘ f
  let ϕ : Π (x : M), TangentSpace I' (f x) →L[𝕜] TangentSpace I x :=
    fun x ↦ (mfderivWithin I I' f s x).inverse
  have hv : ContMDiffWithinAt I I'.tangent m
      (fun x ↦ (v x : TangentBundle I' M')) (s ∩ f ⁻¹' t) x₀ := by
    apply hV.comp x₀ ((hf.of_le (le_trans (le_self_add) hmn)).mono inter_subset_left)
    exact MapsTo.mono_left (mapsTo_preimage _ _) inter_subset_right
  /- The only nontrivial fact, from which the conclusion follows, is
  that `ϕ` depends smoothly on `x`. -/
  suffices hϕ : ContMDiffWithinAt I 𝓘(𝕜, E' →L[𝕜] E) m
      (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E' (TangentSpace I' (M := M')) E (TangentSpace I (M := M))
        (b₁ x₀) (b₁ x) (b₂ x₀) (b₂ x) (ϕ x)) s x₀ from
    ContMDiffWithinAt.clm_apply_of_inCoordinates (hϕ.mono inter_subset_left) hv contMDiffWithinAt_id
  /- To prove that `ϕ` depends smoothly on `x`, we use that the derivative depends smoothly on `x`
  (this is `ContMDiffWithinAt.mfderivWithin_const`), and that taking the inverse is a smooth
  operation at an invertible map. -/
  -- the derivative in coordinates depends smoothly on the point
  have : ContMDiffWithinAt I 𝓘(𝕜, E →L[𝕜] E') m
      (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderivWithin I I' f s x)) s x₀ :=
    hf.mfderivWithin_const hmn hx₀ hs
  -- therefore, its inverse in coordinates also depends smoothly on the point
  have : ContMDiffWithinAt I 𝓘(𝕜, E' →L[𝕜] E) m
      (ContinuousLinearMap.inverse ∘ (fun (x : M) ↦ ContinuousLinearMap.inCoordinates
        E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ x (f x₀) (f x) (mfderivWithin I I' f s x))) s x₀ := by
    apply ContMDiffAt.comp_contMDiffWithinAt _ _ this
    apply ContDiffAt.contMDiffAt
    apply IsInvertible.contDiffAt_map_inverse
    rw [inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' x₀)
      (FiberBundle.mem_baseSet_trivializationAt' (f x₀))]
    exact isInvertible_equiv.comp (hf'.comp isInvertible_equiv)
  -- the inverse in coordinates coincides with the in-coordinate version of the inverse,
  -- therefore the previous point gives the conclusion
  apply this.congr_of_eventuallyEq_of_mem _ hx₀
  have A : (trivializationAt E (TangentSpace I) x₀).baseSet ∈ 𝓝[s] x₀ := by
    apply nhdsWithin_le_nhds
    apply (trivializationAt _ _ _).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' _
  have B : f ⁻¹' (trivializationAt E' (TangentSpace I') (f x₀)).baseSet ∈ 𝓝[s] x₀ := by
    apply hf.continuousWithinAt.preimage_mem_nhdsWithin
    apply (trivializationAt _ _ _).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' _
  filter_upwards [A, B] with x hx h'x
  simp only [Function.comp_apply]
  rw [inCoordinates_eq hx h'x, inCoordinates_eq h'x (by exact hx)]
  simp only [inverse_equiv_comp, inverse_comp_equiv, ContinuousLinearEquiv.symm_symm, ϕ]
  rfl

lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_inter_of_eq
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (h : f x₀ = y₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f⁻¹' t) x₀ := by
  subst h
  exact ContMDiffWithinAt.mpullbackWithin_vectorField_inter hV hf hf' hx₀ hs hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) s x₀ := by
  apply (ContMDiffWithinAt.mpullbackWithin_vectorField_inter hV hf hf' hx₀ hs hmn).mono_of_mem
  exact Filter.inter_mem self_mem_nhdsWithin hst

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem_of_eq
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hy₀ : f x₀ = y₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) s x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem hV hf hf' hx₀ hs hmn hst

/- TODO: move me -/
lemma _root_.Set.MapsTo.preimage_mem_nhdsWithin {α β : Type*} [TopologicalSpace α]
    {f : α → β} {s : Set α} {t : Set β} {x : α}
    (hst : MapsTo f s t) : f ⁻¹' t ∈ 𝓝[s] x :=
  Filter.mem_of_superset self_mem_nhdsWithin hst

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (hst : MapsTo f s t) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) s x₀ :=
  ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem hV hf hf' hx₀ hs hmn
    hst.preimage_mem_nhdsWithin

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffWithinAt I I' n f s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (hst : MapsTo f s t) (h : f x₀ = y₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) s x₀ := by
  subst h
  exact ContMDiffWithinAt.mpullbackWithin_vectorField hV hf hf' hx₀ hs hmn hst

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, with a set used for the pullback possibly larger. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField' {u : Set M}
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffWithinAt I I' n f u x₀) (hf' : (mfderivWithin I I' f u x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (hu : s ⊆ u) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V u y : TangentBundle I M)) s x₀ := by
  have hn : (1 : ℕ) ≤ n := le_trans le_add_self hmn
  have hh : (mfderivWithin I I' f s x₀).IsInvertible := by
    convert hf' using 1
    exact (hf.mdifferentiableWithinAt hn).mfderivWithin_mono (hs _ hx₀) hu
  apply (hV.mpullbackWithin_vectorField_of_mem (hf.mono hu) hh hx₀ hs hmn
    hst).congr_of_eventuallyEq_of_mem _ hx₀
  have Y := contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin.1 (hf.of_le hn)
  simp_rw [insert_eq_of_mem (hu hx₀)] at Y
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_mono _ hu Y] with y hy h'y
  simp only [mpullbackWithin, Bundle.TotalSpace.mk_inj]
  rw [MDifferentiableWithinAt.mfderivWithin_mono (h'y.mdifferentiableWithinAt le_rfl) (hs _ hy) hu]

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, with a set used for the pullback possibly larger. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq' {u : Set M}
    (hV : ContMDiffWithinAt I' I'.tangent m
      (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffWithinAt I I' n f u x₀) (hf' : (mfderivWithin I I' f u x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hu : s ⊆ u) (hy₀ : f x₀ = y₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V u y : TangentBundle I M)) s x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullbackWithin_vectorField' hV hf hf' hx₀ hs hmn hst hu

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version on a set. -/
protected lemma _root_.ContMDiffOn.mpullbackWithin_vectorField_inter
    (hV : ContMDiffOn I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t)
    (hf : ContMDiffOn I I' n f s) (hf' : ∀ x ∈ s ∩ f ⁻¹' t, (mfderivWithin I I' f s x).IsInvertible)
    (hs : UniqueMDiffOn I s) (hmn : m + 1 ≤ n) :
    ContMDiffOn I I.tangent m
      (fun (y : M) ↦ (mpullbackWithin I I' f V s y : TangentBundle I M)) (s ∩ f ⁻¹' t) :=
  fun _ hx₀ ↦ ContMDiffWithinAt.mpullbackWithin_vectorField_inter
    (hV _ hx₀.2) (hf _ hx₀.1) (hf' _ hx₀) hx₀.1 hs hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_preimage
    (hV : ContMDiffWithinAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) x₀ := by
  simp only [← contMDiffWithinAt_univ, ← mfderivWithin_univ, ← mpullbackWithin_univ] at hV hf hf' ⊢
  simpa using hV.mpullbackWithin_vectorField_inter hf hf' (mem_univ _) uniqueMDiffOn_univ hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_preimage_of_eq
    (hV : ContMDiffWithinAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n)
    (hy₀ : y₀ = f x₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullback_vectorField_preimage hV hf hf' hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_of_mem
    (hV : ContMDiffWithinAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) s x₀ :=
  (ContMDiffWithinAt.mpullback_vectorField_preimage hV hf hf' hmn).mono_of_mem hst

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_of_mem_of_eq
    (hV : ContMDiffWithinAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t y₀)
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (hy₀ : y₀ = f x₀) :
    ContMDiffWithinAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) s x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullback_vectorField_of_mem hV hf hf' hmn hst

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version on a set, but with full pullback -/
protected lemma _root_.ContMDiffOn.mpullback_vectorField_preimage
    (hV : ContMDiffOn I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) t)
    (hf : ContMDiff I I' n f) (hf' : ∀ x ∈ f ⁻¹' t, (mfderiv I I' f x).IsInvertible)
    (hmn : m + 1 ≤ n) :
    ContMDiffOn I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) (f ⁻¹' t) :=
  fun x₀ hx₀ ↦ ContMDiffWithinAt.mpullback_vectorField_preimage (hV _ hx₀) (hf x₀) (hf' _ hx₀) hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`.
Version at a point. -/
protected lemma _root_.ContMDiffAt.mpullback_vectorField_preimage
    (hV : ContMDiffAt I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')) (f x₀))
    (hf : ContMDiffAt I I' n f x₀) (hf' : (mfderiv I I' f x₀).IsInvertible) (hmn : m + 1 ≤ n) :
    ContMDiffAt I I.tangent m
      (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) x₀ := by
  simp only [← contMDiffWithinAt_univ] at hV hf hf' ⊢
  simpa using ContMDiffWithinAt.mpullback_vectorField_preimage hV hf hf' hmn

/-- The pullback of a `C^m` vector field by a `C^n` function with `m + 1 ≤ n` is `C^m`. -/
protected lemma _root_.ContMDiff.mpullback_vectorField
    (hV : ContMDiff I' I'.tangent m (fun (y : M') ↦ (V y : TangentBundle I' M')))
    (hf : ContMDiff I I' n f) (hf' : ∀ x, (mfderiv I I' f x).IsInvertible) (hmn : m + 1 ≤ n) :
    ContMDiff I I.tangent m (fun (y : M) ↦ (mpullback I I' f V y : TangentBundle I M)) :=
  fun x ↦ ContMDiffAt.mpullback_vectorField_preimage (hV (f x)) (hf x) (hf' x) hmn

end

lemma mpullbackWithin_comp_of_left
    {g : M' → M''} {f : M → M'} {V : Π (x : M''), TangentSpace I'' x}
    {s : Set M} {t : Set M'} {x₀ : M} (hg : MDifferentiableWithinAt I' I'' g t (f x₀))
    (hf : MDifferentiableWithinAt I I' f s x₀) (h : Set.MapsTo f s t)
    (hu : UniqueMDiffWithinAt I s x₀) (hg' : (mfderivWithin I' I'' g t (f x₀)).IsInvertible) :
    mpullbackWithin I I'' (g ∘ f) V s x₀ =
      mpullbackWithin I I' f (mpullbackWithin I' I'' g V t) s x₀ := by
  simp only [mpullbackWithin, comp_apply]
  rw [mfderivWithin_comp _ hg hf h hu, IsInvertible.inverse_comp_apply_of_left]
  · rfl
  · exact hg'

lemma mpullbackWithin_comp_of_right
    {g : M' → M''} {f : M → M'} {V : Π (x : M''), TangentSpace I'' x}
    {s : Set M} {t : Set M'} {x₀ : M} (hg : MDifferentiableWithinAt I' I'' g t (f x₀))
    (hf : MDifferentiableWithinAt I I' f s x₀) (h : Set.MapsTo f s t)
    (hu : UniqueMDiffWithinAt I s x₀) (hf' : (mfderivWithin I I' f s x₀).IsInvertible) :
    mpullbackWithin I I'' (g ∘ f) V s x₀ =
      mpullbackWithin I I' f (mpullbackWithin I' I'' g V t) s x₀ := by
  simp only [mpullbackWithin, comp_apply]
  rw [mfderivWithin_comp _ hg hf h hu, IsInvertible.inverse_comp_apply_of_right hf']
  rfl

end

variable {V W V₁ W₁ : Π (x : M), TangentSpace I x}

variable (I I') in
/-- The Lie bracket of two vector fields in a manifold, within a set. -/
def mlieBracketWithin (V W : Π (x : M), TangentSpace I x) (s : Set M) (x₀ : M) :
    TangentSpace I x₀ :=
  mpullback I 𝓘(𝕜, E) (extChartAt I x₀)
    (lieBracketWithin 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) x₀

variable (I I') in
/-- The Lie bracket of two vector fields in a manifold. -/
def mlieBracket (V W : Π (x : M), TangentSpace I x) (x₀ : M) : TangentSpace I x₀ :=
  mlieBracketWithin I V W univ x₀

lemma mlieBracketWithin_def  :
    mlieBracketWithin I V W s = fun x₀ ↦
    mpullback I 𝓘(𝕜, E) (extChartAt I x₀)
    (lieBracketWithin 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) x₀ := rfl

lemma mlieBracketWithin_apply :
    mlieBracketWithin I V W s x₀ =
    (mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) x₀).inverse
    ((lieBracketWithin 𝕜
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) ((extChartAt I x₀ x₀))) := rfl

lemma mlieBracketWithin_eq_lieBracketWithin {V W : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} :
     mlieBracketWithin 𝓘(𝕜, E) V W s  = lieBracketWithin 𝕜 V W s := by
  ext x
  simp [mlieBracketWithin_apply]

/-********************************************************************************
Copy of the `lieBracket` API in manifolds
-/

@[simp] lemma mlieBracketWithin_univ :
    mlieBracketWithin I V W univ = mlieBracket I V W := rfl

lemma mlieBracketWithin_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    mlieBracketWithin I V W s x = 0 := by
  simp only [mlieBracketWithin, mpullback_apply, comp_apply]
  rw [lieBracketWithin_eq_zero_of_eq_zero]
  · simp
  · simp only [mpullbackWithin_apply]
    have : (extChartAt I x).symm ((extChartAt I x) x) = x := by simp
    rw [this, hV]
    simp
  · simp only [mpullbackWithin_apply]
    have : (extChartAt I x).symm ((extChartAt I x) x) = x := by simp
    rw [this, hW]
    simp

open FiberBundle

variable (H I) in
/-- In the tangent bundle to the model space, the second projection is smooth. -/
lemma contMDiff_snd_tangentBundle_modelSpace {n : ℕ∞} :
    ContMDiff I.tangent 𝓘(𝕜, E) n (fun (p : TangentBundle I H) ↦ p.2) := by
  change ContMDiff I.tangent 𝓘(𝕜, E) n
    ((id Prod.snd : ModelProd H E → E) ∘ (tangentBundleModelSpaceHomeomorph I))
  apply ContMDiff.comp (I' := I.prod 𝓘(𝕜, E))
  · convert contMDiff_snd
    rw [chartedSpaceSelf_prod]
    rfl
  · exact contMDiff_tangentBundleModelSpaceHomeomorph

variable [SmoothManifoldWithCorners I M] in
lemma isInvertible_mfderivWithin_extChartAt_symm {y : E} (hy : y ∈ (extChartAt I x).target) :
    (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) y).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hy)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hy)

variable [SmoothManifoldWithCorners I M] in
lemma isInvertible_mfderiv_extChartAt {y : M} (hy : y ∈ (extChartAt I x).source) :
    (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y).IsInvertible := by
  have h'y : extChartAt I x y ∈ (extChartAt I x).target := (extChartAt I x).map_source hy
  have Z := ContinuousLinearMap.IsInvertible.of_inverse
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm h'y)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt h'y)
  have : (extChartAt I x).symm ((extChartAt I x) y) = y := (extChartAt I x).left_inv hy
  rwa [this] at Z

lemma mlieBracketWithin_swap_apply :
    mlieBracketWithin I V W s x = - mlieBracketWithin I W V s x := by
  rw [mlieBracketWithin, lieBracketWithin_swap, mpullback_neg]
  rfl

lemma mlieBracketWithin_swap :
    mlieBracketWithin I V W s = - mlieBracketWithin I W V s := by
  ext x
  exact mlieBracketWithin_swap_apply

lemma mlieBracket_swap_apply : mlieBracket I V W x = - mlieBracket I W V x :=
  mlieBracketWithin_swap_apply

lemma mlieBracket_swap : mlieBracket I V W = - mlieBracket I W V :=
  mlieBracketWithin_swap

@[simp] lemma mlieBracketWithin_self : mlieBracketWithin I V V = 0 := by
  ext x; simp [mlieBracketWithin, mpullback]

@[simp] lemma mlieBracket_self : mlieBracket I V V = 0 := by
  ext x; simp_rw [mlieBracket, mlieBracketWithin_self, Pi.zero_apply]

/-- Variant of `mlieBracketWithin_congr_set` where one requires the sets to coincide only in
the complement of a point. -/
theorem mlieBracketWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x := by
  simp only [mlieBracketWithin_apply]
  congr 1
  have : T1Space M := I.t1Space M
  suffices A : ((extChartAt I x).symm ⁻¹' s ∩ range I : Set E)
    =ᶠ[𝓝[{(extChartAt I x) x}ᶜ] (extChartAt I x x)]
      ((extChartAt I x).symm ⁻¹' t ∩ range I : Set E) by
    apply lieBracketWithin_congr_set' _ A
  obtain ⟨u, u_mem, hu⟩ : ∃ u ∈ 𝓝 x, u ∩ {x}ᶜ ⊆ {y | (y ∈ s) = (y ∈ t)} :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (nhdsWithin_compl_singleton_le x y h)
  rw [← extChartAt_to_inv (I := I) x] at u_mem
  have B : (extChartAt I x).target ∪ (range I)ᶜ ∈ 𝓝 (extChartAt I x x) := by
    rw [← nhdsWithin_univ, ← union_compl_self (range I), nhdsWithin_union]
    apply Filter.union_mem_sup (extChartAt_target_mem_nhdsWithin x) self_mem_nhdsWithin
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.2
    ⟨_, Filter.inter_mem ((continuousAt_extChartAt_symm x).preimage_mem_nhds u_mem) B, ?_⟩
  rintro z ⟨hz, h'z⟩
  simp only [eq_iff_iff, mem_setOf_eq]
  change z ∈ (extChartAt I x).symm ⁻¹' s ∩ range I ↔ z ∈ (extChartAt I x).symm ⁻¹' t ∩ range I
  by_cases hIz : z ∈ range I
  · simp [-extChartAt, hIz] at hz ⊢
    rw [← eq_iff_iff]
    apply hu ⟨hz.1, ?_⟩
    simp only [mem_compl_iff, mem_singleton_iff, ne_comm, ne_eq] at h'z ⊢
    rw [(extChartAt I x).eq_symm_apply (by simp) hz.2]
    exact Ne.symm h'z
  · simp [hIz]

theorem mlieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x :=
  mlieBracketWithin_congr_set' x <| h.filter_mono inf_le_left

theorem mlieBracketWithin_inter (ht : t ∈ 𝓝 x) :
    mlieBracketWithin I V W (s ∩ t) x = mlieBracketWithin I V W s x := by
  apply mlieBracketWithin_congr_set
  filter_upwards [ht] with y hy
  change (y ∈ s ∩ t) = (y ∈ s)
  aesop

theorem mlieBracketWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    mlieBracketWithin I V W s x = mlieBracket I V W x := by
  rw [← mlieBracketWithin_univ, ← univ_inter s, mlieBracketWithin_inter h]

theorem mlieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    mlieBracketWithin I V W s x = mlieBracket I V W x :=
  mlieBracketWithin_of_mem_nhds (hs.mem_nhds hx)

/-- Variant of `mlieBracketWithin_eventually_congr_set` where one requires the sets to coincide only
in  the complement of a point. -/
theorem mlieBracketWithin_eventually_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mlieBracketWithin I V W s =ᶠ[𝓝 x] mlieBracketWithin I V W t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => mlieBracketWithin_congr_set' y

theorem mlieBracketWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    mlieBracketWithin I V W s =ᶠ[𝓝 x] mlieBracketWithin I V W t :=
  mlieBracketWithin_eventually_congr_set' x <| h.filter_mono inf_le_left

theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x) (hW : W₁ =ᶠ[𝓝[s] x] W) (hxW : W₁ x = W x) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x := by
  simp only [mlieBracketWithin_apply]
  congr 1
  let I1 : NormedAddCommGroup (TangentSpace 𝓘(𝕜, E) (extChartAt I x x)) :=
    inferInstanceAs (NormedAddCommGroup E)
  let _I2 : NormedSpace 𝕜 (TangentSpace 𝓘(𝕜, E) (extChartAt I x x)) :=
    inferInstanceAs (NormedSpace 𝕜 E)
  apply Filter.EventuallyEq.lieBracketWithin_vectorField_eq
  · apply nhdsWithin_mono _ inter_subset_left
    filter_upwards [(continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin''
      hV (by simp)] with y hy
    simp only [mpullbackWithin_apply]
    congr 1
  · simp only [mpullbackWithin_apply]
    congr 1
    convert hxV <;> exact extChartAt_to_inv x
  · apply nhdsWithin_mono _ inter_subset_left
    filter_upwards [(continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin''
      hW (by simp)] with y hy
    simp only [mpullbackWithin_apply]
    congr 1
  · simp only [mpullbackWithin_apply]
    congr 1
    convert hxW <;> exact extChartAt_to_inv x

theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (hx : x ∈ s) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  hV.mlieBracketWithin_vectorField_eq (mem_of_mem_nhdsWithin hx hV :)
    hW (mem_of_mem_nhdsWithin hx hW :)

/-- If vector fields coincide on a neighborhood of a point within a set, then the Lie brackets
also coincide on a neighborhood of this point within this set. Version where one considers the Lie
bracket within a subset. -/
theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField'
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (ht : t ⊆ s) :
    mlieBracketWithin I V₁ W₁ t =ᶠ[𝓝[s] x] mlieBracketWithin I V W t := by
  filter_upwards [hV, hW, eventually_eventually_nhdsWithin.2 hV,
    eventually_eventually_nhdsWithin.2 hW] with y hVy hWy hVy' hWy'
  apply Filter.EventuallyEq.mlieBracketWithin_vectorField_eq
  · apply nhdsWithin_mono _ ht
    exact hVy'
  · exact hVy
  · apply nhdsWithin_mono _ ht
    exact hWy'
  · exact hWy

protected theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) :
    mlieBracketWithin I V₁ W₁ s =ᶠ[𝓝[s] x] mlieBracketWithin I V W s :=
  hV.mlieBracketWithin_vectorField' hW Subset.rfl

protected theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_of_insert
    (hV : V₁ =ᶠ[𝓝[insert x s] x] V) (hW : W₁ =ᶠ[𝓝[insert x s] x] W) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x := by
  apply mem_of_mem_nhdsWithin (mem_insert x s)
    (hV.mlieBracketWithin_vectorField' hW (subset_insert x s))

theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  (hV.filter_mono nhdsWithin_le_nhds).mlieBracketWithin_vectorField_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds

theorem mlieBracketWithin_congr
    (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  (hV.eventuallyEq.filter_mono inf_le_right).mlieBracketWithin_vectorField_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

/-- Version of `mlieBracketWithin_congr` in which one assumes that the point belongs to the
given set. -/
theorem mlieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x ∈ s) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  mlieBracketWithin_congr hV (hV hx) hW (hW hx)

theorem _root_.Filter.EventuallyEq.mlieBracket_vectorField_eq
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    mlieBracket I V₁ W₁ x = mlieBracket I V W x := by
  rw [← mlieBracketWithin_univ, ← mlieBracketWithin_univ,
    hV.mlieBracketWithin_vectorField_eq_nhds hW]

protected theorem _root_.Filter.EventuallyEq.mlieBracket_vectorField
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) : mlieBracket I V₁ W₁ =ᶠ[𝓝 x] mlieBracket I V W := by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.mlieBracket_vectorField_eq hWy

section

variable [SmoothManifoldWithCorners I M] [CompleteSpace E]

lemma _root_.MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField
    (hV : MDifferentiableWithinAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) s x) :
    DifferentiableWithinAt 𝕜 (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I))
    ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  apply MDifferentiableWithinAt.differentiableWithinAt
  have := MDifferentiableWithinAt.mpullbackWithin_vectorField_of_eq hV
    (contMDiffWithinAt_extChartAt_symm_range x (mem_extChartAt_target x))
    (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x)) (mem_range_self _)
    I.uniqueMDiffOn le_rfl (extChartAt_to_inv x).symm
  rw [inter_comm]
  exact ((contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.mdifferentiableAt
    le_rfl).comp_mdifferentiableWithinAt _ this

lemma mlieBracketWithin_add_left
    (hV : MDifferentiableWithinAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) s x)
    (hV₁ : MDifferentiableWithinAt I I.tangent (fun x ↦ (V₁ x : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I (V + V₁) W s x =
      mlieBracketWithin I V W s x + mlieBracketWithin I V₁ W s x := by
  simp only [mlieBracketWithin_apply]
  rw [← ContinuousLinearMap.map_add, mpullbackWithin_add, lieBracketWithin_add_left]
  · exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · exact hV₁.differentiableWithinAt_mpullbackWithin_vectorField
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs

lemma mlieBracket_add_left
    (hV : MDifferentiableAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) x)
    (hV₁ : MDifferentiableAt I I.tangent (fun x ↦ (V₁ x : TangentBundle I M)) x) :
    mlieBracket I (V + V₁) W  x =
      mlieBracket I V W x + mlieBracket I V₁ W x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hV hV₁ ⊢
  exact mlieBracketWithin_add_left hV hV₁ (uniqueMDiffWithinAt_univ _)

lemma mlieBracketWithin_add_right
    (hW : MDifferentiableWithinAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) s x)
    (hW₁ : MDifferentiableWithinAt I I.tangent (fun x ↦ (W₁ x : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieBracketWithin I V (W + W₁) s x =
      mlieBracketWithin I V W s x + mlieBracketWithin I V W₁ s x := by
  rw [mlieBracketWithin_swap, Pi.neg_apply, mlieBracketWithin_add_left hW hW₁ hs,
    mlieBracketWithin_swap (V := V), mlieBracketWithin_swap (V := V), Pi.neg_apply, Pi.neg_apply]
  abel

lemma mlieBracket_add_right
    (hW : MDifferentiableAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) x)
    (hW₁ : MDifferentiableAt I I.tangent (fun x ↦ (W₁ x : TangentBundle I M)) x) :
    mlieBracket I V (W + W₁) x =
      mlieBracket I V W x + mlieBracket I V W₁ x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hW hW₁ ⊢
  exact mlieBracketWithin_add_right hW hW₁ (uniqueMDiffWithinAt_univ _)

theorem mlieBracketWithin_of_mem
    (st : t ∈ 𝓝[s] x) (hs : UniqueMDiffWithinAt I s x)
    (hV : MDifferentiableWithinAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) t x)
    (hW : MDifferentiableWithinAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) t x) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x := by
  simp only [mlieBracketWithin_apply]
  congr 1
  rw [lieBracketWithin_of_mem]
  · apply Filter.inter_mem
    · apply nhdsWithin_mono _ inter_subset_left
      exact (continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin''
        st (by simp)
    · exact nhdsWithin_mono _ inter_subset_right self_mem_nhdsWithin
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs
  · exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · exact hW.differentiableWithinAt_mpullbackWithin_vectorField

theorem mlieBracketWithin_subset (st : s ⊆ t) (ht : UniqueMDiffWithinAt I s x)
    (hV : MDifferentiableWithinAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) t x)
    (hW : MDifferentiableWithinAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) t x) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x :=
  mlieBracketWithin_of_mem (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW

theorem mlieBracketWithin_eq_mlieBracket (hs : UniqueMDiffWithinAt I s x)
    (hV : MDifferentiableAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) x)
    (hW : MDifferentiableAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) x) :
    mlieBracketWithin I V W s x = mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ, ← mdifferentiableWithinAt_univ] at hV hW ⊢
  exact mlieBracketWithin_subset (subset_univ _) hs hV hW


theorem _root_.DifferentiableWithinAt.mlieBracketWithin_congr_mono
    (hV : MDifferentiableWithinAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) s x)
    (hVs : EqOn V₁ V t) (hVx : V₁ x = V x)
    (hW : MDifferentiableWithinAt I I.tangent (fun x ↦ (W x : TangentBundle I M)) s x)
    (hWs : EqOn W₁ W t) (hWx : W₁ x = W x)
    (hxt : UniqueMDiffWithinAt I t x) (h₁ : t ⊆ s) :
    mlieBracketWithin I V₁ W₁ t x = mlieBracketWithin I V W s x := by
  rw [mlieBracketWithin_congr hVs hVx hWs hWx]
  exact mlieBracketWithin_subset h₁ hxt hV hW

end

/-- A vector field on a vector space is smooth in the manifold sense iff it is smoooth in the vector
space sense-/
lemma contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {n : ℕ∞} {s : Set E} {x : E} :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent n (fun x ↦ (V x : TangentBundle 𝓘(𝕜, E) E))
      s x ↔ ContDiffWithinAt 𝕜 n V s x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ContMDiffWithinAt.contDiffWithinAt <|
      (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.comp_contMDiffWithinAt _ h
  · apply (Bundle.contMDiffWithinAt_totalSpace _).2
    refine ⟨contMDiffWithinAt_id, ?_⟩
    convert h.contMDiffWithinAt with y
    simp

/-- A vector field on a vector space is smooth in the manifold sense iff it is smoooth in the vector
space sense-/
lemma contMDiffAt_vectorSpace_iff_contDiffAt
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {n : ℕ∞} {x : E} :
    ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent n (fun x ↦ (V x : TangentBundle 𝓘(𝕜, E) E)) x ↔
      ContDiffAt 𝕜 n V x := by
  simp only [← contMDiffWithinAt_univ, ← contDiffWithinAt_univ,
    contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

/-- A vector field on a vector space is smooth in the manifold sense iff it is smoooth in the vector
space sense-/
lemma contMDiffOn_vectorSpace_iff_contDiffOn
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {n : ℕ∞} {s : Set E} :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E).tangent n (fun x ↦ (V x : TangentBundle 𝓘(𝕜, E) E)) s ↔
      ContDiffOn 𝕜 n V s := by
  simp only [ContMDiffOn, ContDiffOn, contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt ]

/-- A vector field on a vector space is smooth in the manifold sense iff it is smoooth in the vector
space sense-/
lemma contMDiff_vectorSpace_iff_contDiff
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {n : ℕ∞} :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, E).tangent n (fun x ↦ (V x : TangentBundle 𝓘(𝕜, E) E)) ↔
      ContDiff 𝕜 n V := by
  simp only [← contMDiffOn_univ, ← contDiffOn_univ, contMDiffOn_vectorSpace_iff_contDiffOn]


/-******************************************************************************-/

variable [SmoothManifoldWithCorners I M] [SmoothManifoldWithCorners I' M'] [CompleteSpace E]


-- TODO: we have no fderivWithin_comp !!!
-- because it's called fderivWithin.comp...

/- The Lie bracket of vector fields on manifolds is well defined, i.e., it is invariant under
diffeomorphisms. Auxiliary version where one assumes that all relevant sets are contained
in chart domains. -/
private lemma mpullbackWithin_mlieBracketWithin_aux [CompleteSpace E']
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (V x : TangentBundle I' M')) t (f x₀))
    (hW : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (W x : TangentBundle I' M')) t (f x₀))
    (hu : UniqueMDiffOn I s) (hf : ContMDiffOn I I' 2 f s) (hx₀ : x₀ ∈ s)
    (ht : t ⊆ (extChartAt I' (f x₀)).source) (hst : MapsTo f s t)
    (hsymm : IsSymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I) (extChartAt I x₀ x₀)) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
  have A : (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ := by simp
  have A' : x₀ = (extChartAt I x₀).symm (extChartAt I x₀ x₀) := by simp
  have h'f : MDifferentiableWithinAt I I' f s x₀ := (hf x₀ hx₀).mdifferentiableWithinAt one_le_two
  simp only [mlieBracketWithin_apply, mpullbackWithin_apply]
  -- first, rewrite the pullback of the Lie bracket as a pullback in `E` under the map
  -- `F = extChartAt I' (f x₀) ∘ f ∘ (extChartAt I x₀).symm` of a Lie bracket computed in `E'`,
  -- of two vector fields `V'` and `W'`.
  rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_left
    (isInvertible_mfderiv_extChartAt (mem_extChartAt_source (f x₀)))]
  rw [← mfderiv_comp_mfderivWithin _ (mdifferentiableAt_extChartAt
    (ChartedSpace.mem_chart_source (f x₀))) h'f (hu x₀ hx₀)]
  rw [eq_comm, (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x₀)).inverse_apply_eq]
  have : (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) (extChartAt I x₀ x₀)).inverse =
      mfderiv I 𝓘(𝕜, E) (extChartAt I x₀) x₀ := by
    apply ContinuousLinearMap.inverse_eq
    · convert mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) (x := x₀)
        (y := extChartAt I x₀ x₀) (by simp)
    · convert mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀)
        (y := extChartAt I x₀ x₀) (by simp)
  rw [← this, ← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_right]; swap
  · exact isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x₀)
  have : mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) (extChartAt I x₀ x₀) =
      mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm ((extChartAt I x₀).symm ⁻¹' s ∩ range I)
      (extChartAt I x₀ x₀) :=
    (MDifferentiableWithinAt.mfderivWithin_mono
      (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x₀))
      (UniqueDiffWithinAt.uniqueMDiffWithinAt (hu x₀ hx₀)) inter_subset_right).symm
  rw [this]; clear this
  rw [← mfderivWithin_comp_of_eq]; rotate_left
  · apply MDifferentiableAt.comp_mdifferentiableWithinAt (I' := I') _ _ h'f
    exact mdifferentiableAt_extChartAt (ChartedSpace.mem_chart_source (f x₀))
  · exact (mdifferentiableWithinAt_extChartAt_symm (mem_extChartAt_target x₀)).mono
      inter_subset_right
  · exact inter_subset_left
  · exact UniqueDiffWithinAt.uniqueMDiffWithinAt (hu x₀ hx₀)
  · simp
  set V' := mpullbackWithin 𝓘(𝕜, E') I' (extChartAt I' (f x₀)).symm V (range I') with hV'
  set W' := mpullbackWithin 𝓘(𝕜, E') I' (extChartAt I' (f x₀)).symm W (range I') with hW'
  set F := ((extChartAt I' (f x₀)) ∘ f) ∘ ↑(extChartAt I x₀).symm with hF
  have hFx₀ : extChartAt I' (f x₀) (f x₀) = F (extChartAt I x₀ x₀) := by simp [F]
  rw [hFx₀, ← mpullbackWithin_apply]
  -- second rewrite, the Lie bracket of the pullback as the Lie bracket of the pullback of the
  -- vector fields `V'` and `W'` in `E'`.
  have P (Y : (x : M') → TangentSpace I' x) :
      (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (mpullbackWithin I I' f Y s)
      (range I)) =ᶠ[𝓝[(extChartAt I x₀).symm ⁻¹' s ∩ range I] (extChartAt I x₀ x₀)]
        mpullbackWithin 𝓘(𝕜, E) 𝓘(𝕜, E') F
          (mpullbackWithin 𝓘(𝕜, E') I' ((extChartAt I' (f x₀)).symm) Y (range I'))
          ((extChartAt I x₀).symm ⁻¹' s ∩ range I) := by
    have : (extChartAt I x₀).target
        ∈ 𝓝[(extChartAt I x₀).symm ⁻¹' s ∩ range I] (extChartAt I x₀ x₀) :=
      nhdsWithin_mono _ inter_subset_right (extChartAt_target_mem_nhdsWithin x₀)
    filter_upwards [self_mem_nhdsWithin, this] with y hy h'''y
    have h'y : f ((extChartAt I x₀).symm y) ∈ (extChartAt I' (f x₀)).source := ht (hst hy.1)
    have h''y : f ((extChartAt I x₀).symm y) ∈ (chartAt H' (f x₀)).source := by simpa using h'y
    have huy : UniqueMDiffWithinAt 𝓘(𝕜, E) ((extChartAt I x₀).symm ⁻¹' s ∩ range I) y := by
      apply UniqueDiffWithinAt.uniqueMDiffWithinAt
      rw [inter_comm]
      apply hu.uniqueDiffWithinAt_range_inter
      exact ⟨h'''y, hy.1⟩
    simp only [mpullbackWithin_apply, hF, comp_apply, ← mfderivWithin_eq_fderivWithin]
    rw [mfderivWithin_comp (I' := I) (u := s)]; rotate_left
    · apply (mdifferentiableAt_extChartAt h''y).comp_mdifferentiableWithinAt (I' := I')
      exact (hf _ hy.1).mdifferentiableWithinAt one_le_two
    · exact (mdifferentiableWithinAt_extChartAt_symm h'''y).mono inter_subset_right
    · exact inter_subset_left
    · exact huy
    rw [mfderiv_comp_mfderivWithin (I' := I')]; rotate_left
    · exact mdifferentiableAt_extChartAt h''y
    · exact (hf _ hy.1).mdifferentiableWithinAt one_le_two
    · exact hu _ hy.1
    rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_right]; swap
    · exact isInvertible_mfderivWithin_extChartAt_symm h'''y
    rw [← ContinuousLinearMap.IsInvertible.inverse_comp_apply_of_left]; swap
    · exact isInvertible_mfderivWithin_extChartAt_symm (PartialEquiv.map_source _ h'y)
    have : f ((extChartAt I x₀).symm y)
        = (extChartAt I' (f x₀)).symm ((extChartAt I' (f x₀)) (f ((extChartAt I x₀).symm y))) :=
      (PartialEquiv.left_inv (extChartAt I' (f x₀)) h'y).symm
    congr 2
    have : (mfderivWithin 𝓘(𝕜, E') I' ((extChartAt I' (f x₀)).symm) (range I')
        (extChartAt I' (f x₀) (f ((extChartAt I x₀).symm y)))) ∘L
        (mfderiv I' 𝓘(𝕜, E') (↑(extChartAt I' (f x₀))) (f ((extChartAt I x₀).symm y))) =
        ContinuousLinearMap.id _ _ := by
      convert mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
        ((PartialEquiv.map_source _ h'y))
    simp only [← ContinuousLinearMap.comp_assoc, this, ContinuousLinearMap.id_comp]
    congr 1
    exact ((mdifferentiableWithinAt_extChartAt_symm h'''y).mfderivWithin_mono huy
      inter_subset_right).symm
  rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem (P V) (P W) (by simp [hx₀]),
    ← hV', ← hW']
  simp only [mpullbackWithin_eq_pullbackWithin]
  -- finally, use the fact that for `C^2` maps between vector spaces with symmetric second
  -- derivative, the pullback and the Lie bracket commute.
  rw [lieBracketWithin_pullbackWithin_of_eventuallyEq
      (u := (extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target)]
  · exact hsymm
  · rw [hF, comp_assoc]
    apply ContMDiffWithinAt.contDiffWithinAt
    apply ContMDiffAt.comp_contMDiffWithinAt (I' := I')
    · exact contMDiffAt_extChartAt' (by simp)
    apply ContMDiffWithinAt.comp_of_eq (I' := I) (hf _ hx₀) _ _ A
    · exact (contMDiffWithinAt_extChartAt_symm_range _ (mem_extChartAt_target x₀)).mono
        inter_subset_right
    · exact (mapsTo_preimage _ _).mono_left inter_subset_left
  · rw [← hFx₀]
    exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · rw [← hFx₀]
    exact hW.differentiableWithinAt_mpullbackWithin_vectorField
  · rw [inter_comm]
    exact UniqueMDiffOn.uniqueDiffOn_target_inter hu x₀
  · simp [hx₀]
  · intro z hz
    simp only [comp_apply, mem_inter_iff, mem_preimage, mem_range, F]
    refine ⟨?_, mem_range_self _⟩
    convert hst hz.1
    exact PartialEquiv.left_inv (extChartAt I' (f x₀)) (ht (hst hz.1))
  · rw [← nhdsWithin_eq_iff_eventuallyEq]
    apply le_antisymm
    · exact nhdsWithin_mono _ (inter_subset_inter_right _ (extChartAt_target_subset_range x₀))
    · rw [nhdsWithin_le_iff, nhdsWithin_inter]
      exact Filter.inter_mem_inf self_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin x₀)

/- The Lie bracket of vector fields on manifolds is well defined, i.e., it is invariant under
diffeomorphisms. -/
lemma mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (V x : TangentBundle I' M')) t (f x₀))
    (hW : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (W x : TangentBundle I' M')) t (f x₀))
    (hu : UniqueMDiffOn I s) (hf : ContMDiffWithinAt I I' 2 f s x₀) (hx₀ : x₀ ∈ s)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hsymm : IsSymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I) (extChartAt I x₀ x₀)) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
  have A : (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ := by simp
  by_cases hfi : (mfderivWithin I I' f s x₀).IsInvertible; swap
  · simp only [mlieBracketWithin_apply, mpullbackWithin_apply,
      ContinuousLinearMap.inverse_of_not_isInvertible hfi, ContinuousLinearMap.zero_apply]
    rw [lieBracketWithin_eq_zero_of_eq_zero]
    · simp [-extChartAt]
    · simp only [mpullbackWithin_apply]
      rw [A, ContinuousLinearMap.inverse_of_not_isInvertible hfi]
      simp [-extChartAt]
    · simp only [mpullbackWithin_apply]
      rw [A, ContinuousLinearMap.inverse_of_not_isInvertible hfi]
      simp [-extChartAt]
  -- Now, interesting case where the derivative of `f` is invertible
  have : CompleteSpace E' := by
    rcases hfi with ⟨M, -⟩
    let M' : E ≃L[𝕜] E' := M
    exact (completeSpace_congr (e := M'.toEquiv) M'.isUniformEmbedding).1 (by assumption)
  -- choose a small open set `v` around `x₀` where `f` is `C^2`
  obtain ⟨u, u_open, x₀u, ut, maps_u, u_smooth⟩ :
      ∃ u, IsOpen u ∧ x₀ ∈ u ∧ s ∩ u ⊆ f ⁻¹' t ∧
        s ∩ u ⊆ f ⁻¹' (extChartAt I' (f x₀)).source ∧ ContMDiffOn I I' 2 f (s ∩ u) := by
    obtain ⟨u, u_open, x₀u, hu⟩ :
      ∃ u, IsOpen u ∧ x₀ ∈ u ∧ ContMDiffOn I I' 2 f (insert x₀ s ∩ u) := hf.contMDiffOn' le_rfl
    have : f ⁻¹' (extChartAt I' (f x₀)).source ∈ 𝓝[s] x₀ :=
      hf.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (f x₀))
    rcases mem_nhdsWithin.1 (Filter.inter_mem hst this) with ⟨w, w_open, x₀w, hw⟩
    refine ⟨u ∩ w, u_open.inter w_open, by simp [x₀u, x₀w], ?_, ?_, ?_⟩
    · apply Subset.trans _ (hw.trans inter_subset_left)
      exact fun y hy ↦ ⟨hy.2.2, hy.1⟩
    · apply Subset.trans _ (hw.trans inter_subset_right)
      exact fun y hy ↦ ⟨hy.2.2, hy.1⟩
    · apply hu.mono
      exact fun y hy ↦ ⟨subset_insert _ _ hy.1, hy.2.1⟩
  have u_mem : u ∈ 𝓝 x₀ := u_open.mem_nhds x₀u
  -- apply the auxiliary version to `s ∩ u`
  set s' := s ∩ u with hs'
  have s'_eq : s' =ᶠ[𝓝 x₀] s := by
    filter_upwards [u_mem] with y hy
    change (y ∈ s ∩ u) = (y ∈ s)
    simp [hy]
  set t' := t ∩ (extChartAt I' (f x₀)).source with ht'
  calc mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀
  _ = mpullbackWithin I I' f (mlieBracketWithin I' V W t) s' x₀ := by
    simp only [mpullbackWithin, hs', mfderivWithin_inter u_mem]
  _ = mpullbackWithin I I' f (mlieBracketWithin I' V W t') s' x₀ := by
    simp only [mpullbackWithin, ht', mlieBracketWithin_inter (extChartAt_source_mem_nhds (f x₀))]
  _ = mlieBracketWithin I (mpullbackWithin I I' f V s') (mpullbackWithin I I' f W s') s' x₀ := by
    apply mpullbackWithin_mlieBracketWithin_aux (t := t') (hV.mono inter_subset_left)
      (hW.mono inter_subset_left) (hu.inter u_open) u_smooth ⟨hx₀, x₀u⟩ inter_subset_right
      (fun y hy ↦ ⟨ut hy, maps_u hy⟩)
    apply hsymm.congr_set
    have : (extChartAt I x₀).symm ⁻¹' u ∈ 𝓝 (extChartAt I x₀ x₀) := by
      apply (continuousAt_extChartAt_symm x₀).preimage_mem_nhds
      apply u_open.mem_nhds (by simpa using x₀u)
    filter_upwards [this] with y hy
    change (y ∈ (extChartAt I x₀).symm ⁻¹' s ∩ range I) =
      (y ∈ (extChartAt I x₀).symm ⁻¹' (s ∩ u) ∩ range I)
    simp [-extChartAt, hy]
  _ = mlieBracketWithin I (mpullbackWithin I I' f V s') (mpullbackWithin I I' f W s') s x₀ := by
    simp only [hs', mlieBracketWithin_inter u_mem]
  _ = mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
    apply Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem _ _ hx₀
    · apply nhdsWithin_le_nhds
      filter_upwards [mfderivWithin_eventually_congr_set (I := I) (I' := I') (f := f) s'_eq]
        with y hy using by simp [mpullbackWithin, hy]
    · apply nhdsWithin_le_nhds
      filter_upwards [mfderivWithin_eventually_congr_set (I := I) (I' := I') (f := f) s'_eq]
        with y hy using by simp [mpullbackWithin, hy]

open Filter

variable [IsRCLikeNormedField 𝕜]

lemma mpullbackWithin_mlieBracketWithin
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (V x : TangentBundle I' M')) t (f x₀))
    (hW : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (W x : TangentBundle I' M')) t (f x₀))
    (hu : UniqueMDiffOn I s) (hf : ContMDiffWithinAt I I' 2 f s x₀) (hx₀ : x₀ ∈ s)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (h'x₀ : x₀ ∈ closure (interior s)) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ =
      mlieBracketWithin I (mpullbackWithin I I' f V s) (mpullbackWithin I I' f W s) s x₀ := by
  apply mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt hV hW hu hf hx₀ hst
  have A : ((extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target : Set E)
      =ᶠ[𝓝 (extChartAt I x₀ x₀)] ((extChartAt I x₀).symm ⁻¹' s ∩ range I : Set E) :=
    EventuallyEq.inter (by rfl) extChartAt_target_eventuallyEq
  apply IsSymmSndFDerivWithinAt.congr_set _ A
  apply ContDiffWithinAt.isSymmSndFDerivWithinAt (n := 2) _ le_rfl
  · rw [inter_comm]
    exact UniqueMDiffOn.uniqueDiffOn_target_inter hu x₀
  · simp_rw [mem_closure_iff, interior_inter, ← inter_assoc]
    intro o o_open ho
    obtain ⟨y, ⟨yo, hy⟩, ys⟩ :
        ((extChartAt I x₀) ⁻¹' o ∩ (extChartAt I x₀).source ∩ interior s).Nonempty := by
      have : (extChartAt I x₀) ⁻¹' o ∈ 𝓝 x₀ := by
        apply (continuousAt_extChartAt x₀).preimage_mem_nhds (o_open.mem_nhds ho)
      exact (mem_closure_iff_nhds.1 h'x₀) _ (inter_mem this (extChartAt_source_mem_nhds x₀))
    have A : interior (↑(extChartAt I x₀).symm ⁻¹' s) ∈ 𝓝 (extChartAt I x₀ y) := by
      simp only [interior_mem_nhds]
      apply (continuousAt_extChartAt_symm' hy).preimage_mem_nhds
      simp only [hy, PartialEquiv.left_inv]
      exact mem_interior_iff_mem_nhds.mp ys
    have B : (extChartAt I x₀) y ∈ closure (interior (extChartAt I x₀).target) := by
      apply extChartAt_target_subset_closure_interior (x := x₀)
      exact (extChartAt I x₀).map_source hy
    exact mem_closure_iff_nhds.1 B _ (inter_mem (o_open.mem_nhds yo) A)
  · simp [hx₀]
  · exact (contMDiffWithinAt_iff.1 hf).2.congr_set A.symm

lemma mpullback_mlieBracketWithin
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (V x : TangentBundle I' M')) t (f x₀))
    (hW : MDifferentiableWithinAt I' I'.tangent (fun x ↦ (W x : TangentBundle I' M')) t (f x₀))
    (hu : UniqueMDiffOn I s) (hf : ContMDiffAt I I' 2 f x₀) (hx₀ : x₀ ∈ s)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (h'x₀ : x₀ ∈ closure (interior s)) :
    mpullback I I' f (mlieBracketWithin I' V W t) x₀ =
      mlieBracketWithin I (mpullback I I' f V) (mpullback I I' f W) s x₀ := by
  have : mpullback I I' f (mlieBracketWithin I' V W t) x₀ =
      mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀ := by
    simp only [mpullback, mpullbackWithin]
    congr
    apply (mfderivWithin_eq_mfderiv (hu _ hx₀) _).symm
    exact hf.mdifferentiableAt one_le_two
  rw [this, mpullbackWithin_mlieBracketWithin hV hW hu hf.contMDiffWithinAt hx₀ hst h'x₀]
  apply Filter.EventuallyEq.mlieBracketWithin_vectorField_of_insert
  · rw [insert_eq_of_mem hx₀]
    filter_upwards [nhdsWithin_le_nhds (contMDiffAt_iff_contMDiffAt_nhds.1 hf),
      self_mem_nhdsWithin] with y hy h'y
    simp only [mpullback, mpullbackWithin]
    congr
    apply mfderivWithin_eq_mfderiv (hu _ h'y)
    exact hy.mdifferentiableAt one_le_two
  · rw [insert_eq_of_mem hx₀]
    filter_upwards [nhdsWithin_le_nhds (contMDiffAt_iff_contMDiffAt_nhds.1 hf),
      self_mem_nhdsWithin] with y hy h'y
    simp only [mpullback, mpullbackWithin]
    congr
    apply mfderivWithin_eq_mfderiv (hu _ h'y)
    exact hy.mdifferentiableAt one_le_two

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
protected lemma _root_.ContMDiffWithinAt.mlieBracketWithin_vectorField {m n : ℕ∞}
    {U V : Π (x : M), TangentSpace I x} {s : Set M} {x : M}
    (hU : ContMDiffWithinAt I I.tangent n (fun x ↦ (U x : TangentBundle I M)) s x)
    (hV : ContMDiffWithinAt I I.tangent n (fun x ↦ (V x : TangentBundle I M)) s x)
    (hs : UniqueMDiffOn I s) (h's : s ⊆ closure (interior s)) (hx : x ∈ s) (hmn : m + 1 ≤ n) :
    ContMDiffWithinAt I I.tangent m
      (fun x ↦ (mlieBracketWithin I U V s x : TangentBundle I M)) s x := by
  /- The statement is not obvious, since at different points the Lie bracket is defined using
  different charts. However, since we know that the Lie bracket is invariant under diffeos, we can
  use a single chart to prove the statement. Let `U'` and `V'` denote the pullbacks of `U` and `V`
  in the chart around `x`. Then the Lie bracket there is smooth (as it coincides with the vector
  space Lie bracket, given by an explicit formula). Pulling back this Lie bracket in `M` gives
  locally a smooth function, which coincides with the initial Lie bracket by invariance
  under diffeos. -/
  apply contMDiffWithinAt_iff_nat.2 (fun m' hm' ↦ ?_)
  have hn : (1 : ℕ∞) ≤ m' + 1 := by exact_mod_cast (show 1 ≤ m' + 1 by omega)
  have hm'n : m' + 1 ≤ n := le_trans (add_le_add_right hm' 1) hmn
  have s_inter_mem : s ∩ (extChartAt I x).source ∈ 𝓝[s] x :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (extChartAt_source_mem_nhds x))
  have pre_mem : (extChartAt I x) ⁻¹' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
      ∈ 𝓝[s] x := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)] with y hy h'y
    exact ⟨(extChartAt I x).map_source h'y,
      by simpa only [mem_preimage, (extChartAt I x).left_inv h'y] using hy⟩
  let U' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm U (range I)
  let V' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I)
  have J0 (Z : Π (x : M), TangentSpace I x)
      (hZ : ContMDiffWithinAt I I.tangent (m'+ 1) (fun x ↦ (Z x : TangentBundle I M)) s x) :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent (m' + 1)
      (fun y ↦ (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Z (range I) y :
        TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) :=
    ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq' hZ
      (contMDiffWithinAt_extChartAt_symm_range (n := ⊤) _ (mem_extChartAt_target x))
      (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x))
      (by simp [hx]) (UniqueMDiffOn.uniqueDiffOn_target_inter hs x).uniqueMDiffOn le_top
      ((mapsTo_preimage _ _).mono_left inter_subset_right).preimage_mem_nhdsWithin
      (Subset.trans inter_subset_left (extChartAt_target_subset_range x)) (extChartAt_to_inv x)
  have J1 (Z : Π (x : M), TangentSpace I x)
        (hZ : ContMDiffWithinAt I I.tangent (m' + 1) (fun x ↦ (Z x : TangentBundle I M)) s x) :
      ∀ᶠ y in 𝓝[s] x, ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent (m' + 1)
      (fun z ↦ (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Z (range I) z :
        TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x y) := by
    have T := nhdsWithin_mono _ (subset_insert _ _)
        (contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin.1 (J0 Z hZ))
    have A := (continuousAt_extChartAt (I := I) x).continuousWithinAt.preimage_mem_nhdsWithin'' T
      rfl
    apply (nhdsWithin_le_iff.2 _) A
    filter_upwards [s_inter_mem] with y hy
    simp only [mfld_simps] at hy
    simp [hy.1, hy.2]
  have A : ContDiffWithinAt 𝕜 m' (lieBracketWithin 𝕜 U' V'
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) :=
    ContDiffWithinAt.lieBracketWithin_vectorField
      (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1 (J0 U (hU.of_le hm'n)))
      (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1 (J0 V (hV.of_le hm'n)))
      (hs.uniqueDiffOn_target_inter x) le_rfl (by simp [hx])
  have B : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent m' (fun y ↦ (mlieBracketWithin 𝓘(𝕜, E) U' V'
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) y : TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) := by
    rw [← mlieBracketWithin_eq_lieBracketWithin] at A
    exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.2 A
  have C : ContMDiffWithinAt I I.tangent m' (fun y ↦ (mpullback I 𝓘(𝕜, E) (extChartAt I x)
      ((mlieBracketWithin 𝓘(𝕜, E) U' V'
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s))) y : TangentBundle I M)) s x :=
    ContMDiffWithinAt.mpullback_vectorField_of_mem_of_eq B contMDiffAt_extChartAt
      (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)) le_top pre_mem rfl
  apply C.congr_of_eventuallyEq_of_mem _ hx
  have J (Z : Π (x : M), TangentSpace I x) :
      ∀ᶠ y in 𝓝[s] x, Z y = mpullback I 𝓘(𝕜, E) (extChartAt I x)
        (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Z (range I)) y := by
    apply nhdsWithin_le_nhds
    filter_upwards [extChartAt_source_mem_nhds (I := I) x] with y hy
    have A : (extChartAt I x).symm (extChartAt I x y) = y := (extChartAt I x).left_inv hy
    rw [mpullback_apply, mpullbackWithin_apply,
      ← (isInvertible_mfderiv_extChartAt hy).inverse_comp_apply_of_right,
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy, A]
    simp only [ContinuousLinearMap.inverse_id, ContinuousLinearMap.coe_id', id_eq]
  filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem,
    eventually_eventually_nhdsWithin.2 (J U),
    eventually_eventually_nhdsWithin.2 (J V), J1 U (hU.of_le hm'n), J1 V (hV.of_le hm'n),
    nhdsWithin_le_nhds (chart_source_mem_nhds H x), self_mem_nhdsWithin]
    with y hy hyU hyV h'yU h'yV hy_chart hys
  simp only [Bundle.TotalSpace.mk_inj]
  rw [mpullback_mlieBracketWithin (h'yU.mdifferentiableWithinAt hn)
    (h'yV.mdifferentiableWithinAt hn) hs (contMDiffAt_extChartAt' hy_chart) hys hy (h's hys)]
  exact Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem hyU hyV hys

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
lemma _root_.ContMDiffAt.mlieBracket_vectorField {m n : ℕ∞}
    {U V : Π (x : M), TangentSpace I x} {x : M}
    (hU : ContMDiffAt I I.tangent n (fun x ↦ (U x : TangentBundle I M)) x)
    (hV : ContMDiffAt I I.tangent n (fun x ↦ (V x : TangentBundle I M)) x)
    (hmn : m + 1 ≤ n) :
    ContMDiffAt I I.tangent m (fun x ↦ (mlieBracket I U V x : TangentBundle I M)) x := by
  simp only [← contMDiffWithinAt_univ, ← mlieBracketWithin_univ] at hU hV ⊢
  exact hU.mlieBracketWithin_vectorField hV uniqueMDiffOn_univ (by simp) (mem_univ _) hmn

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
lemma _root_.ContMDiffOn.mlieBracketWithin_vectorField {m n : ℕ∞}
    {U V : Π (x : M), TangentSpace I x}
    (hU : ContMDiffOn I I.tangent n (fun x ↦ (U x : TangentBundle I M)) s)
    (hV : ContMDiffOn I I.tangent n (fun x ↦ (V x : TangentBundle I M)) s)
    (hs : UniqueMDiffOn I s) (h's : s ⊆ closure (interior s)) (hmn : m + 1 ≤ n) :
    ContMDiffOn I I.tangent m (fun x ↦ (mlieBracketWithin I U V s x : TangentBundle I M)) s :=
  fun x hx ↦ (hU x hx).mlieBracketWithin_vectorField (hV x hx) hs h's hx hmn

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
lemma _root_.ContDiff.mlieBracket {m n : ℕ∞}
    {U V : Π (x : M), TangentSpace I x}
    (hU : ContMDiff I I.tangent n (fun x ↦ (U x : TangentBundle I M)))
    (hV : ContMDiff I I.tangent n (fun x ↦ (V x : TangentBundle I M)))
    (hmn : m + 1 ≤ n) :
    ContMDiff I I.tangent m (fun x ↦ (mlieBracket I U V x : TangentBundle I M)) := by
  simp only [← contMDiffOn_univ, mlieBracketWithin_univ] at hU hV ⊢
  exact hU.mlieBracketWithin_vectorField hV uniqueMDiffOn_univ (by simp) hmn

lemma leibniz_identity_mlieBracketWithin [IsRCLikeNormedField 𝕜]
    {U V W : Π (x : M), TangentSpace I x} {s : Set M} {x : M}
    (hs : UniqueMDiffOn I s) (h's : s ⊆ closure (interior s)) (hx : x ∈ s)
    (hU : ContMDiffWithinAt I I.tangent 2 (fun x ↦ (U x : TangentBundle I M)) s x)
    (hV : ContMDiffWithinAt I I.tangent 2 (fun x ↦ (V x : TangentBundle I M)) s x)
    (hW : ContMDiffWithinAt I I.tangent 2 (fun x ↦ (W x : TangentBundle I M)) s x) :
    mlieBracketWithin I U (mlieBracketWithin I V W s) s x =
      mlieBracketWithin I (mlieBracketWithin I U V s) W s x
      + mlieBracketWithin I V (mlieBracketWithin I U W s) s x := by
  have s_inter_mem : s ∩ (extChartAt I x).source ∈ 𝓝[s] x :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (extChartAt_source_mem_nhds x))
  have pre_mem : (extChartAt I x) ⁻¹' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
      ∈ 𝓝[s] x := by
    filter_upwards [s_inter_mem] with y hy
    exact ⟨(extChartAt I x).map_source hy.2,
      by simpa only [mem_preimage, (extChartAt I x).left_inv hy.2] using hy.1⟩
  -- write everything as pullbacks of vector fields in `E` (denoted with primes), for which
  -- the identity can be checked via direct calculation.
  set U' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm U (range I) with hU'
  set V' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm V (range I) with hV'
  set W' := mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm W (range I) with hW'
  have J0 (Z : Π (x : M), TangentSpace I x)
      (hZ : ContMDiffWithinAt I I.tangent 2 (fun x ↦ (Z x : TangentBundle I M)) s x) :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent 2
      (fun y ↦ (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Z (range I) y :
        TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) :=
    ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq' hZ
      (contMDiffWithinAt_extChartAt_symm_range (n := ⊤) _ (mem_extChartAt_target x))
      (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x))
      (by simp [hx]) (UniqueMDiffOn.uniqueDiffOn_target_inter hs x).uniqueMDiffOn le_top
      ((mapsTo_preimage _ _).mono_left inter_subset_right).preimage_mem_nhdsWithin
      (Subset.trans inter_subset_left (extChartAt_target_subset_range x)) (extChartAt_to_inv x)
  have J1 (Z : Π (x : M), TangentSpace I x)
        (hZ : ContMDiffWithinAt I I.tangent 2 (fun x ↦ (Z x : TangentBundle I M)) s x) :
      ∀ᶠ y in 𝓝[s] x, ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent 2
      (fun y ↦ (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Z (range I) y :
        TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x y) := by
    have T := nhdsWithin_mono _ (subset_insert _ _)
        (contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin.1 (J0 Z hZ))
    have A := (continuousAt_extChartAt (I := I) x).continuousWithinAt.preimage_mem_nhdsWithin'' T
      rfl
    apply (nhdsWithin_le_iff.2 _) A
    filter_upwards [s_inter_mem] with y hy
    simp only [mfld_simps] at hy
    simp [hy.1, hy.2]
  have J0U : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent 2 (fun y ↦ (U' y : TangentBundle 𝓘(𝕜, E) E))
    ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) := J0 U hU
  have J0V : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent 2 (fun y ↦ (V' y : TangentBundle 𝓘(𝕜, E) E))
    ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) := J0 V hV
  have J0W : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent 2 (fun y ↦ (W' y : TangentBundle 𝓘(𝕜, E) E))
    ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) := J0 W hW
  have J1U : ∀ᶠ y in 𝓝[s] x, ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent 2
    (fun y ↦ (U' y : TangentBundle 𝓘(𝕜, E) E))
    ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x y) := J1 U hU
  have J1V : ∀ᶠ y in 𝓝[s] x, ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent 2
    (fun y ↦ (V' y : TangentBundle 𝓘(𝕜, E) E))
    ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x y) := J1 V hV
  have J1W : ∀ᶠ y in 𝓝[s] x, ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent 2
    (fun y ↦ (W' y : TangentBundle 𝓘(𝕜, E) E))
    ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x y) := J1 W hW
  have J (Z : Π (x : M), TangentSpace I x) :
      ∀ᶠ y in 𝓝[s] x, Z y = mpullback I 𝓘(𝕜, E) (extChartAt I x)
        (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x).symm Z (range I)) y := by
    apply nhdsWithin_le_nhds
    filter_upwards [extChartAt_source_mem_nhds (I := I) x] with y hy
    have A : (extChartAt I x).symm (extChartAt I x y) = y := (extChartAt I x).left_inv hy
    rw [mpullback_apply, mpullbackWithin_apply,
      ← (isInvertible_mfderiv_extChartAt hy).inverse_comp_apply_of_right,
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hy, A]
    simp only [ContinuousLinearMap.inverse_id, ContinuousLinearMap.coe_id', id_eq]
  -- rewrite the vector fields as pullbacks of vector fields in `E`.
  have JU : U =ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x) U' := J U
  have JV : V =ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x) V' := J V
  have JW : W =ᶠ[𝓝[s] x] mpullback I 𝓘(𝕜, E) (extChartAt I x) W' := J W
  rw [JU.mlieBracketWithin_vectorField_eq_of_mem (JV.mlieBracketWithin_vectorField JW) hx,
    (JU.mlieBracketWithin_vectorField JV).mlieBracketWithin_vectorField_eq_of_mem JW hx,
    JV.mlieBracketWithin_vectorField_eq_of_mem (JU.mlieBracketWithin_vectorField JW) hx]
  /-have : mlieBracketWithin I
      (mpullback I 𝓘(𝕜, E) (extChartAt I x) V') (mpullback I 𝓘(𝕜, E) (extChartAt I x) W') s x
    = mpullback I 𝓘(𝕜, E) (extChartAt I x) (mlieBracketWithin 𝓘(𝕜, E) V' W'
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)) x := by
    apply (mpullback_mlieBracketWithin (J0V.mdifferentiableWithinAt one_le_two)
      (J0W.mdifferentiableWithinAt one_le_two) hs contMDiffAt_extChartAt hx _ (h's hx)).symm
    filter_upwards [s_inter_mem] with y hy
    exact ⟨(extChartAt I x).map_source hy.2,
      by simpa only [mem_preimage, (extChartAt I x).left_inv hy.2] using hy.1⟩ -/
  have : ∀ᶠ y in 𝓝[s] x, mlieBracketWithin I
        (mpullback I 𝓘(𝕜, E) (extChartAt I x) V') (mpullback I 𝓘(𝕜, E) (extChartAt I x) W') s y
      = mpullback I 𝓘(𝕜, E) (extChartAt I x) (mlieBracketWithin 𝓘(𝕜, E) V' W'
        ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)) y := by
    filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem, J1V, J1W,
      nhdsWithin_le_nhds (chart_source_mem_nhds H x), self_mem_nhdsWithin] with y hy hyV hyW h'y ys
    exact (mpullback_mlieBracketWithin (hyV.mdifferentiableWithinAt one_le_two)
      (hyW.mdifferentiableWithinAt one_le_two) hs (contMDiffAt_extChartAt' h'y) ys hy (h's ys)).symm
  rw [Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem EventuallyEq.rfl this hx,
    ← mpullback_mlieBracketWithin (J0U.mdifferentiableWithinAt one_le_two) _ hs
      contMDiffAt_extChartAt hx pre_mem (h's hx)]
  swap
  · apply ContMDiffWithinAt.mdifferentiableWithinAt _ le_rfl
    apply J0V.mlieBracketWithin_vectorField J0W (m := 1)
    exact hs.uniqueMDiffOn_target_inter x

































#exit





lemma leibniz_identity_mlieBracket [IsRCLikeNormedField 𝕜]
    {U V W : Π (x : M), TangentSpace I x} {x : M}
    (hU : ContMDiffAt I I.tangent 2 (fun x ↦ (U x : TangentBundle I M)) x)
    (hV : ContMDiffAt I I.tangent 2 (fun x ↦ (V x : TangentBundle I M)) x)
    (hW : ContMDiffAt I I.tangent 2 (fun x ↦ (W x : TangentBundle I M)) x) :
    mlieBracket I U (mlieBracket I V W) x =
      mlieBracket I (mlieBracket I U V) W x + mlieBracket I V (mlieBracket I U W) x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hU hV hW ⊢
  exact leibniz_identity_mlieBracketWithin uniqueMDiffOn_univ (by simp) (mem_univ _) hU hV hW

end VectorField

end LieBracketManifold

set_option linter.style.longFile 1900
