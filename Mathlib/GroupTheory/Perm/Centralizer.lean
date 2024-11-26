/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.GroupTheory.Perm.ConjAct
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.Cycle.Factors


/-! # Centralizer of a permutation and cardinality of conjugacy classes
  # in the symmetric groups

Let `α : Type` with `Fintype α` (and `DecidableEq α`).
The main goal of this file is to compute the cardinality of
conjugacy classes in `Equiv.Perm α`.
Every `g : Equiv.Perm α` has a `cycleType α : Multiset ℕ`.
By `Equiv.Perm.isConj_iff_cycleType_eq`,
two permutations are conjugate in `Equiv.Perm α` iff
their cycle types are equal.
To compute the cardinality of the conjugacy classes, we could use
a purely combinatorial approach and compute the number of permutations
with given cycle type but we resorted to a more algebraic approach
based on the study of the centralizer of a permutation `g`.

Given `g : Equiv.Perm α`, the conjugacy class of `g` is the orbit
of `g` under the action `ConjAct (Equiv.Perm α)`, and we use the
orbit-stabilizer theorem
(`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`) to reduce
the computation to the computation of the centralizer of `g`, the
subgroup of `Equiv.Perm α` consisting of all permutations which
commute with `g`. It is accessed here as `MulAction.stabilizer
(ConjAct (Equiv.Perm α)) g` and
`Equiv.Perm.centralizer_eq_comap_stabilizer`.

We compute this subgroup as follows.

* If `h : Subgroup.centralizer {g}`, then the action of `ConjAct.toConjAct h`
by conjugation on `Equiv.Perm α` stabilizes `g.cycleFactorsFinset`.
That induces an action of `Subgroup.centralizer {g}` on
`g.cycleFactorsFinset` which is defined via
`Equiv.Perm.OnCycleFactors.subMulActionOnCycleFactors `

* This action defines a group morphism `Equiv.Perm.OnCycleFactors.toPermHom g`
from `Subgroup.centralizer {g}` to `Equiv.Perm g.cycleFactorsFinset`

* `Equiv.Perm.OnCycleFactors.toPermHom_range'` is the subgroup of
`Equiv.Perm g.cycleFactorsFinset` consisting of permutations that
preserve the cardinality of the support.

* `Equiv.Perm.OnCycleFactors.range_eq_range_toPermHom'  shows that
the range of `Equiv.Perm.OnCycleFactors.toPermHom g`
is the subgroup `toPermHom_range' g` of `Equiv.Perm g.cycleFactorsFinset`.

This is showed by constructing a right inverse
`Equiv.Perm.Basis.toCentralizer`, as established by
`Equiv.Perm.Basis.toCentralizer_rightInverse`.

* `Equiv.Perm.OnCycleFactors.nat_card_range_toPermHom` computes the
cardinality of `(Equiv.Perm.OnCycleFactors.toPermHom g).range`
as a product of factorials.

* `Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff` proves that `k :
  Subgroup.centralizer {g}` belongs to the kernel of
  `Equiv.Perm.OnCycleFactors.toPermHom g` if and only if it commutes with
  each cycle of `g`.  This is equivalent to the conjunction of two properties:
  * `k` preserves the set of fixed points of `g``
  * on each cycle `c`, `k` acts as a power of that cycle

  This allows to give a description of the kernel of
  `Equiv.Perm.OnCycleFactors.toPermHom g` as the product of a
  symmetric group and of a product of cyclic groups.  This analysis
  starts with the morphism `Equiv.Perm.OnCycleFactors.θ`, its
  injectivity `Equiv.Perm.OnCycleFactors.θ_injective`, its range
  `Equiv.Perm.OnCycleFactors.θ_range_eq`, and  its cardinality
  `Equiv.Perm.OnCycleFactors.θ_range_card`.

* `Equiv.Perm.nat_card_centralizer g` computes the cardinality
  of the centralizer of `g`

* `Equiv.Perm.card_isConj_mul_eq g`computes the cardinality
  of the conjugacy class of `g`.

* We now can compute the cardinality of the set of permutations with given cycle type.
  The condition for this cardinality to be zero is given by
  `Equiv.Perm.card_of_cycleType_eq_zero_iff`
  which is itself derived from `Equiv.Perm.exists_with_cycleType_iff`.

* `Equiv.Perm.card_of_cycleType_mul_eq m` and `Equiv.Perm.card_of_cycleType m`
  compute this cardinality.

-/

open scoped Pointwise

namespace Equiv.Perm

open MulAction Equiv Subgroup

variable {α : Type*} [DecidableEq α] [Fintype α] {g : Equiv.Perm α}

namespace OnCycleFactors

variable (g)

variable {g} in
lemma Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset
    (k : Subgroup.centralizer {g}) (c : g.cycleFactorsFinset) :
    ConjAct.toConjAct (k : Perm α) • (c : Perm α) ∈ g.cycleFactorsFinset := by
  suffices (g.cycleFactorsFinset : Set (Perm α)) =
    (ConjAct.toConjAct (k : Perm α)) • (g.cycleFactorsFinset) by
    rw [← Finset.mem_coe, this]
    simp only [Set.smul_mem_smul_set_iff, Finset.mem_coe, Finset.coe_mem]
  have this := cycleFactorsFinset_conj_eq (ConjAct.toConjAct (k : Perm α)) g
  rw [ConjAct.toConjAct_smul, Subgroup.mem_centralizer_singleton_iff.mp k.prop, mul_assoc] at this
  simp only [mul_inv_cancel, mul_one] at this
  conv_lhs => rw [this]
  simp only [Finset.coe_smul_finset]

/-- The action by conjugation of `Subgroup.centraliser {g}`
  on the cycles of a given permutation -/
def Subgroup.Centralizer.cycleFactorsFinset_mulAction :
    MulAction (Subgroup.centralizer {g}) g.cycleFactorsFinset where
  smul k c := ⟨ConjAct.toConjAct (k : Perm α) • (c : Perm α),
    Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k c⟩
  one_smul c := by
    rw [← Subtype.coe_inj]
    change ConjAct.toConjAct (1 : Perm α) • (c : Perm α) = c
    simp only [map_one, one_smul]
  mul_smul k l c := by
    simp only [← Subtype.coe_inj]
    change ConjAct.toConjAct (k * l : Perm α) • (c : Perm α) =
      ConjAct.toConjAct (k : Perm α) • (ConjAct.toConjAct (l : Perm α)) • (c : Perm α)
    simp only [map_mul, mul_smul]

/-- The conjugation action of `Subgroup.centralizer {g}` on `g.cycleFactorsFinset` -/
scoped instance : MulAction (Subgroup.centralizer {g}) (g.cycleFactorsFinset) :=
  (Subgroup.Centralizer.cycleFactorsFinset_mulAction g)

/-- The canonical morphism from `Subgroup.centralizer {g}`
  to the group of permutations of `g.cycleFactorsFinset` -/
def toPermHom := MulAction.toPermHom (Subgroup.centralizer {g}) g.cycleFactorsFinset

theorem centralizer_smul_def (k : Subgroup.centralizer {g}) (c : g.cycleFactorsFinset) :
    k • c = ⟨k * c * k⁻¹, Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k c⟩ :=
  rfl

theorem toPermHom_apply (k : Subgroup.centralizer {g}) (c :  g.cycleFactorsFinset) :
    (toPermHom g k c) = k • c := rfl

theorem coe_toPermHom (k : Subgroup.centralizer {g}) (c :  g.cycleFactorsFinset) :
    (toPermHom g k c : Perm α) = k * c * (k : Perm α)⁻¹ := rfl

/-- The range of `Equiv.Perm.OnCycleFactors.toPermHom`.

The equality is proved by `Equiv.Perm.OnCycleFactors.range_eq_range_toPermHom'`. -/
def range_toPermHom' : Subgroup (Perm g.cycleFactorsFinset) where
  carrier := {τ | ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card}
  one_mem' := by
    simp only [Set.mem_setOf_eq, coe_one, id_eq, eq_self_iff_true, imp_true_iff]
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Subtype.forall, Set.mem_setOf_eq, coe_mul, Function.comp_apply]
    simp only [Subtype.forall, Set.mem_setOf_eq] at hσ hτ
    intro c hc
    rw [hσ, hτ]
  inv_mem' := by
    intro σ hσ
    simp only [Subtype.forall, Set.mem_setOf_eq] at hσ ⊢
    intro c hc
    rw [← hσ]
    · simp only [Finset.coe_mem, Subtype.coe_eta, apply_inv_self]
    · simp only [Finset.coe_mem]

variable {g} in
theorem mem_range_toPermHom'_iff {τ : Perm g.cycleFactorsFinset} :
    τ ∈ range_toPermHom' g ↔
      ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card :=
  Iff.rfl

/-- `k : Subgroup.centralizer {g}` belongs to the kernel of `toPermHom g`
iff it commutes with each cycle of `g` -/
theorem mem_ker_toPermHom_iff (k : Subgroup.centralizer {g}) :
    k ∈ (toPermHom g).ker ↔
      ∀ c ∈ g.cycleFactorsFinset, Commute (k : Perm α) c := by
  simp only [toPermHom, MonoidHom.mem_ker, DFunLike.ext_iff]
  simp only [coe_one, id_eq, Subtype.forall]
  apply forall₂_congr
  intro c hc
  simp only [MulAction.toPermHom_apply, toPerm_apply, ← Subtype.coe_inj,
    commute_iff_eq, centralizer_smul_def, InvMemClass.coe_inv,
    mul_inv_eq_iff_eq_mul]

end OnCycleFactors

open OnCycleFactors Subgroup

/-- A `Basis` of a permutation is a choice of an element in each of its cycles -/
class Basis (g : Equiv.Perm α) where
  /-- A choice of elements in each cycle -/
  (toFun : g.cycleFactorsFinset → α)
  /-- For each cycle, the chosen element belongs to the cycle -/
  (mem_support_self' : ∀ (c : g.cycleFactorsFinset), toFun c ∈ (c : Perm α).support)

instance (g : Perm α) :
    DFunLike (Basis g) (g.cycleFactorsFinset) (fun _ => α) where
  coe a := a.toFun
  coe_injective' a a' _ := by cases a; cases a'; congr

namespace Basis

theorem nonempty (g : Perm α) : Nonempty (Basis g) := by
  have (c : g.cycleFactorsFinset) : (c : Perm α).support.Nonempty :=
    IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.prop).1
  exact ⟨fun c ↦ (this c).choose, fun c ↦ (this c).choose_spec⟩

variable (a : Basis g)

theorem mem_support_self (c : g.cycleFactorsFinset) :
    a c ∈ (c : Perm α).support := a.mem_support_self' c

theorem injective : Function.Injective a := by
  intro c d h
  rw [← Subtype.coe_inj]
  apply g.cycleFactorsFinset_pairwise_disjoint.eq c.prop d.prop
  simp only [Disjoint, not_forall, not_or]
  use a c
  conv_rhs => rw [h]
  simp only [← Perm.mem_support, a.mem_support_self c, a.mem_support_self d, and_self]

theorem cycleOf_eq (c : g.cycleFactorsFinset) :
    g.cycleOf (a c) = c :=
  (cycle_is_cycleOf (a.mem_support_self c) c.prop).symm

variable (τ : range_toPermHom' g)

/-- The function that will provide a right inverse `toCentralizer` to `toPermHom` -/
noncomputable def newK (x : α) : α := by
  if hx : g.cycleOf x ∈ g.cycleFactorsFinset
  then
    let h := mem_support_cycleOf_iff.mp (a.mem_support_self ⟨g.cycleOf x, hx⟩)
    exact (g ^ h.1.symm.choose) (a ((τ : Perm g.cycleFactorsFinset) ⟨g.cycleOf x, hx⟩))
  else exact x

theorem mem_fixedPoints_or_exists_zpow_eq (x : α) : x ∈ Function.fixedPoints g ∨
    ∃ (c : g.cycleFactorsFinset) (_ : x ∈ (c : Perm α).support) (m : ℤ), (g ^ m) (a c) = x := by
  rw [Classical.or_iff_not_imp_left]
  intro hx
  rw [Function.mem_fixedPoints_iff, ← ne_eq, ← mem_support,
    ← cycleOf_mem_cycleFactorsFinset_iff] at hx
  let c : g.cycleFactorsFinset := ⟨g.cycleOf x, hx⟩
  have hc : x ∈ (c : Perm α).support := by
    rw [mem_support_cycleOf_iff]
    rw [← cycleOf_mem_cycleFactorsFinset_iff]
    simp [SameCycle.rfl, hx, and_self]
  exact ⟨c, hc, (mem_support_cycleOf_iff.mp (a.mem_support_self c)).1.symm⟩

theorem newK_apply_of_cycleOf_mem {x : α} {c : g.cycleFactorsFinset}
    (hx : x ∈ (c : Perm α).support) {m : ℤ} (hm : (g ^ m) (a c) = x) :
    newK a τ x = (g ^ m) (a ((τ  : Perm g.cycleFactorsFinset) c)) := by
  have hx' : c = g.cycleOf x := cycle_is_cycleOf hx (Subtype.prop c)
  have hx'' : g.cycleOf x ∈ g.cycleFactorsFinset := hx' ▸ c.prop
  let h := mem_support_cycleOf_iff.mp (a.mem_support_self ⟨g.cycleOf x, hx''⟩)
  set n := h.1.symm.choose
  have hn : (g ^ n) (a c) = x := by
    rw [← h.1.symm.choose_spec]
    congr
    rw [← Subtype.coe_inj, hx']
  suffices newK a τ x = (g ^ n) (a ((τ : Perm g.cycleFactorsFinset) c)) by
    rw [this, IsCycleOn.zpow_apply_eq_zpow_apply
      (isCycleOn_support_of_mem_cycleFactorsFinset ((τ : Perm g.cycleFactorsFinset) c).prop)
      (mem_support_self a ((τ : Perm g.cycleFactorsFinset) c))]
    simp only [τ.prop c]
    rw [← IsCycleOn.zpow_apply_eq_zpow_apply
      (isCycleOn_support_of_mem_cycleFactorsFinset c.prop) (mem_support_self a c)]
    rw [hn, hm]
  simp only [newK, dif_pos hx'']
  congr
  exact hx'.symm

theorem newK_apply_of_mem_fixedPoints {x : α} (hx : x ∈ Function.fixedPoints g) :
    newK a τ x = x := by
  rw [newK, dif_neg]
  rw [cycleOf_mem_cycleFactorsFinset_iff, not_mem_support]
  exact hx

theorem zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff
    {x :α} {m : ℤ} {c : g.cycleFactorsFinset} :
    (g ^ m) x ∈ (c : Perm α).support ↔ x ∈ (c : Perm α).support := by
  rw [← g.eq_cycleOf_of_mem_cycleFactorsFinset_iff _ c.prop]
  rw [cycleOf_self_apply_zpow g m x]
  rw [eq_cycleOf_of_mem_cycleFactorsFinset_iff _ _ c.prop]

theorem newK_apply_mem_support_cycle_iff {x : α} {c : g.cycleFactorsFinset} :
    newK a τ x ∈ ((τ : Perm g.cycleFactorsFinset) c : Perm α).support ↔
      x ∈ (c : Perm α).support := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨d, hd, m, hm⟩)
  · simp only [newK_apply_of_mem_fixedPoints a τ hx]
    suffices ∀ (d : g.cycleFactorsFinset), x ∉ (d : Perm α).support by
      simp only [this]
    intro d hx'
    rw [Function.mem_fixedPoints_iff, ← not_mem_support] at hx
    apply hx
    exact mem_cycleFactorsFinset_support_le d.prop hx'
  · rw [newK_apply_of_cycleOf_mem a τ hd hm] --
    rw [zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff]
    by_cases h : c = d
    · simp only [h, hd, iff_true, mem_support_self]
    · have H : Disjoint (c : Perm α) (d : Perm α) :=
        cycleFactorsFinset_pairwise_disjoint g c.prop d.prop (Subtype.coe_ne_coe.mpr h)
      have H' : Disjoint ((τ : Perm g.cycleFactorsFinset) c : Perm α)
        ((τ : Perm g.cycleFactorsFinset) d : Perm α) :=
        cycleFactorsFinset_pairwise_disjoint g ((τ : Perm g.cycleFactorsFinset) c).prop
          ((τ : Perm g.cycleFactorsFinset) d).prop (by
          intro h'; apply h
          simpa only [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] using h')
      rw [disjoint_iff_disjoint_support, Finset.disjoint_right] at H H'
      simp only [H hd, H' (mem_support_self a _)]

theorem newK_apply_mem_fixedPoints_iff {x : α} :
    newK a τ x ∈ Function.fixedPoints g ↔ x ∈ Function.fixedPoints g := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [hx, newK_apply_of_mem_fixedPoints a τ hx]
  · rw [newK_apply_of_cycleOf_mem a τ hc hm, ← hm]
    simp only [Function.mem_fixedPoints_iff, ← not_mem_support]
    simp only [zpow_apply_mem_support, not_iff_not]
    simp only [Finset.coe_mem,
      mem_cycleFactorsFinset_support_le _ (mem_support_self a _)]

theorem newK_commute_zpow_apply (x : α) (j : ℤ) :
    newK a τ ((g ^ j) x) = (g ^ j) (newK a τ x) := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | hx)
  · rw [newK_apply_of_mem_fixedPoints a τ hx, newK_apply_of_mem_fixedPoints]
    rw [Function.mem_fixedPoints_iff]
    simp only [← mul_apply, ← zpow_one_add, add_comm]
    conv_rhs => rw [← hx, ← mul_apply, ← zpow_add_one]
  · obtain ⟨c, hc, m, hm⟩ := hx
    have hm' : (g ^ (j + m)) (a c) = (g ^ j) x := by rw [zpow_add, mul_apply, hm]
    rw [newK_apply_of_cycleOf_mem a τ hc hm, newK_apply_of_cycleOf_mem a τ _ hm',
      ← mul_apply, ← zpow_add]
    exact zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff.mpr hc

theorem newK_mul (σ τ : range_toPermHom' g) (x) :
    newK a (σ * τ) x = (newK a σ) (newK a τ x) := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [newK_apply_of_mem_fixedPoints a _ hx]
  · simp only [newK_apply_of_cycleOf_mem a _ hc hm]
    rw [newK_apply_of_cycleOf_mem a _ _ rfl]
    · rfl
    · rw [zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff]
      apply mem_support_self

theorem newK_one (x : α) : (newK a 1) x = x := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · rw [newK_apply_of_mem_fixedPoints a _ hx]
  · rw [newK_apply_of_cycleOf_mem a _ hc hm, OneMemClass.coe_one, coe_one, id_eq, hm]

/-- Given `a : g.Basis` and a permutation of `g.cycleFactorsFinset` that
  preserve the lengths of the cycles, a permutation of `α` that
  moves the `Basis` and commutes with `g` -/
noncomputable def ofPermHom : range_toPermHom' g →* Perm α where
  toFun τ := {
    toFun := newK a τ
    invFun := newK a τ⁻¹
    left_inv := fun x ↦ by rw [← newK_mul, inv_mul_cancel, newK_one]
    right_inv := fun x ↦ by rw [← newK_mul, mul_inv_cancel, newK_one] }
  map_one' := ext fun x ↦ newK_one a x
  map_mul' := fun σ τ ↦ ext fun x ↦ by simp [mul_apply, newK_mul a σ τ x]

theorem ofPermHom_support :
    (ofPermHom a τ).support = Finset.biUnion (τ : Perm g.cycleFactorsFinset).support
        (fun c ↦ (c : Perm α).support) := by
  ext x
  simp only [mem_support, Finset.mem_biUnion]
  change newK a τ x ≠ x ↔ _
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [newK_apply_of_mem_fixedPoints a τ hx, ne_eq, not_true_eq_false, false_iff]
    rw [Function.mem_fixedPoints_iff] at hx
    simp only [← mem_support]
    intro h
    obtain ⟨c, _, h'⟩ := h
    exact mem_support.mp ((mem_cycleFactorsFinset_support_le c.prop) h') hx
  · rw [newK_apply_of_cycleOf_mem a τ hc hm]
    nth_rewrite 1 [← hm]
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, (a.injective).eq_iff]
    rw [not_iff_comm]
    by_cases H : (τ : Perm g.cycleFactorsFinset) c = c
    · simp only [H, iff_true]
      push_neg
      intro d hd
      rw [← not_mem_support]
      have := g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop
      rw [disjoint_iff_disjoint_support, Finset.disjoint_left] at this
      refine this ?_ hc
      intro h
      rw [Subtype.coe_inj] at h
      exact hd (h ▸ H)
    · simp only [H, iff_false, not_not]
      exact ⟨c, H, mem_support.mp hc⟩

theorem card_ofPermHom_support :
    (ofPermHom a τ).support.card =  (τ : Perm g.cycleFactorsFinset).support.sum
        (fun c ↦ (c : Perm α).support.card) := by
  rw [ofPermHom_support, Finset.card_biUnion]
  intro c _ d _ h
  apply Equiv.Perm.Disjoint.disjoint_support
  apply g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop (Subtype.coe_ne_coe.mpr h)

theorem ofPermHom_mem_centralizer :
    ofPermHom a τ ∈ Subgroup.centralizer {g} := by
  rw [mem_centralizer_singleton_iff]
  ext x
  simp only [mul_apply]
  exact newK_commute_zpow_apply a τ x 1

/-- Given `a : Equiv.Perm.Basis g`,
we define a right inverse of `Equiv.Perm.OnCycleFactors.toPermHom`,
on `range_toPermHom' g` -/
noncomputable def toCentralizer :
    range_toPermHom' g →* Subgroup.centralizer {g}  where
  toFun τ := ⟨ofPermHom a τ, ofPermHom_mem_centralizer a τ⟩
  map_one' := by simp only [map_one, mk_eq_one]
  map_mul' σ τ := by simp only [map_mul, MulMemClass.mk_mul_mk]

theorem toCentralizer_apply (x) : (toCentralizer a τ : Perm α) x = newK a τ x := rfl

variable (c) in
theorem toCentralizer_equivariant :
    (toCentralizer a τ) • c = (τ : Perm g.cycleFactorsFinset) c := by
  rw [centralizer_smul_def, ← Subtype.coe_inj]
  simp only [InvMemClass.coe_inv, mul_inv_eq_iff_eq_mul]
  ext x
  simp only [mul_apply]
  change newK a τ ((c : Perm α) x) = ((τ : Perm g.cycleFactorsFinset) c : Perm α) (newK a τ x)
  by_cases hx : x ∈ (c : Perm α).support
  · rw [(mem_cycleFactorsFinset_iff.mp c.prop).2 x hx]
    have := newK_commute_zpow_apply a τ x 1
    simp only [zpow_one] at this
    rw [this]
    rw [← (mem_cycleFactorsFinset_iff.mp ((τ : Perm g.cycleFactorsFinset) c).prop).2]
    rw [newK_apply_mem_support_cycle_iff]
    exact hx
  · rw [not_mem_support.mp hx, eq_comm, ← not_mem_support, newK_apply_mem_support_cycle_iff]
    exact hx

theorem toCentralizer_rightInverse :
    (OnCycleFactors.toPermHom g) (toCentralizer a τ) = (τ : Perm g.cycleFactorsFinset) := by
  apply ext
  intro c
  rw [OnCycleFactors.toPermHom_apply, toCentralizer_equivariant]

end Basis

namespace OnCycleFactors

open Basis BigOperators Nat Equiv.Perm Equiv Subgroup

theorem mem_range_toPermHom_iff {τ} : τ ∈ (toPermHom g).range ↔
    ∀ c, (τ c : Perm α).support.card = (c : Perm α).support.card := by
  constructor
  · rintro ⟨k, rfl⟩ c
    rw [coe_toPermHom, Equiv.Perm.support_conj]
    apply Finset.card_map
  · obtain ⟨a⟩ := Basis.nonempty g
    exact fun hτ ↦ ⟨toCentralizer a ⟨τ, hτ⟩, toCentralizer_rightInverse a ⟨τ, hτ⟩⟩

/-- Unapplied variant of `Equiv.Perm.mem_range_toPermHom_iff` -/
theorem mem_range_toPermHom_iff' {τ} : τ ∈ (toPermHom g).range ↔
    (fun (c : g.cycleFactorsFinset) ↦ (c : Perm α).support.card) ∘ τ =
      fun (c : g.cycleFactorsFinset) ↦ (c : Perm α).support.card := by
  rw [mem_range_toPermHom_iff, funext_iff]
  simp only [Finset.coe_sort_coe, Subtype.forall, Function.comp_apply]

/-- Computes the range of `Equiv.Perm.toPermHom g` -/
theorem range_toPermHom_eq_range_toPermHom' :
    (toPermHom g).range = range_toPermHom' g := by
  ext τ
  rw [mem_range_toPermHom_iff, mem_range_toPermHom'_iff]

theorem nat_card_range_toPermHom :
    Nat.card (toPermHom g).range =
      ∏ n in g.cycleType.toFinset, (g.cycleType.count n)! := by
  classical
  let sc (c : g.cycleFactorsFinset) : ℕ := (c : Perm α).support.card
  suffices Fintype.card (toPermHom g).range =
    Fintype.card { k : Perm g.cycleFactorsFinset | sc ∘ k = sc } by
    simp only [Nat.card_eq_fintype_card, this, Set.coe_setOf,
      DomMulAct.stabilizer_card', ← CycleType.count_def]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext n
    simp only [Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach,
        sc, true_and, Subtype.exists, exists_prop, Multiset.mem_toFinset]
    simp only [cycleType_def, Function.comp_apply, Multiset.mem_map, Finset.mem_val]
  simp only [← SetLike.coe_sort_coe, Fintype.card_eq_nat_card]
  congr
  ext τ
  erw [mem_range_toPermHom_iff'] -- rw doesn't work
  simp only [Finset.coe_sort_coe, Set.mem_setOf_eq]

section Kernel
/- Here, we describe the kernel of `g.OnCycleFactors.toPermHom` -/

open BigOperators Nat OnCycleFactors Subgroup

variable {u k : Perm (Function.fixedPoints g)}
  {v v' : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)}
  {x : α}

variable (g) in
/-- The parametrization of the kernel of `toPermHom` -/
def θHom : (Perm (Function.fixedPoints g)) ×
    ((c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α)) →* Perm α :=
  MonoidHom.noncommCoprod ofSubtype (Subgroup.noncommPiCoprod g.pairwise_commute_of_mem_zpowers)
    g.commute_ofSubtype_noncommPiCoprod

variable {ι : Type*} (k : ι → Perm α) (s : Finset ι)
    (hs : (s : Set ι).Pairwise fun i j ↦ Disjoint (k i) (k j))

theorem support_θHom :
    support (θHom g (u,v)) = u.support.map (Function.Embedding.subtype _) ∪
      Finset.univ.biUnion fun c ↦  support (v c : Perm α) := by
  simp only [θHom, MonoidHom.noncommCoprod_apply]
  rw [Disjoint.support_mul (g.disjoint_ofSubtype_noncommPiCoprod u v), u.support_ofSubtype]
  apply congr_arg₂ _ rfl
  rw [noncommPiCoprod_apply, support_noncommProd]
  exact fun i _ j _ h ↦ g.pairwise_disjoint_of_mem_zpowers h _ _ (v i).prop (v j).prop

theorem support_θHom_of_fst_eq_one :
    support (θHom g (u,v)) ⊆ g.support ↔ u = 1 := by
  classical
  rw [support_θHom]
  rw [Finset.union_subset_iff, Finset.biUnion_subset]
  rw [Finset.map_subset_iff_subset_preimage]
  suffices  g.support.preimage (Function.Embedding.subtype _) _ = ∅ by
    rw [this, Finset.subset_empty, Equiv.Perm.support_eq_empty_iff]
    suffices ∀ x ∈ Finset.univ, (v x : Perm α).support ⊆ g.support by
      simp [this]
    intro c _
    exact support_zpowers_of_mem_cycleFactorsFinset_le (v c)
  ext x
  simp only [Function.Embedding.coe_subtype, Finset.mem_preimage, mem_support, ne_eq,
    Finset.not_mem_empty, iff_false, Decidable.not_not]
  exact x.prop

theorem θHom_disjoint_iff {f : Perm α} :
    Disjoint (θHom g (u,v)) f ↔ Disjoint (ofSubtype u) f ∧ ∀ c, Disjoint (v c : Perm α) f := by
  classical
  simp only [disjoint_iff_disjoint_support, support_θHom, Finset.disjoint_union_left,
    Finset.disjoint_biUnion_left]
  apply and_congr
  · rw [← support_ofSubtype]
  · simp only [Finset.univ_eq_attach, Finset.mem_attach, true_implies, Subtype.forall]

theorem θHom_disjoint_self_iff :
    Disjoint (θHom g (u,v)) g ↔ v = 1 := by
  rw [θHom_disjoint_iff]
  suffices (ofSubtype u).Disjoint g by
    simp only [this, Subtype.forall, true_and]
    rw [funext_iff, Subtype.forall]
    apply forall₂_congr
    intro c hc
    rw [disjoint_iff_disjoint_support, disjoint_of_le_iff_left_eq_bot _]
    simp only [Finset.bot_eq_empty, support_eq_empty_iff, OneMemClass.coe_eq_one, Pi.one_apply]
    exact support_zpowers_of_mem_cycleFactorsFinset_le _
  exact disjoint_ofSubtype_of_memFixedPoints_self u

theorem θHom_disjoint_cycle_iff {c : g.cycleFactorsFinset} :
    Disjoint (θHom g (u,v)) c ↔ v c = 1 := by
  rw [θHom_disjoint_iff]
  suffices (ofSubtype u).Disjoint (c : Perm α) by
    simp only [this, Subtype.forall, true_and]
    constructor
    · intro h
      specialize h c c.prop
      rw [disjoint_iff_disjoint_support, disjoint_of_le_iff_left_eq_bot _] at h
      simpa using h
      obtain ⟨m, hm⟩ := (v c).prop; simp only [← hm]; exact support_zpow_le _ m
    · intro hc
      intro d hd
      by_cases h : c = d
      · suffices c = ⟨d, hd⟩ by
          rw [this] at hc
          simp only [hc, OneMemClass.coe_one, disjoint_one_left]
        simp only [← Subtype.coe_inj, h]
      · apply Disjoint.mono (cycleFactorsFinset_pairwise_disjoint g hd c.prop _) _ le_rfl
        exact fun a ↦ h (id (Eq.symm a))
        obtain ⟨m, hm⟩ := (v ⟨d, hd⟩).prop
        simp only [← hm]
        exact support_zpow_le _ m
  exact Equiv.Perm.Disjoint.mono (disjoint_ofSubtype_of_memFixedPoints_self u) le_rfl
    (mem_cycleFactorsFinset_support_le c.prop)

theorem θHom_apply (x : α) : θHom g (u,v) x =
    if hx : g.cycleOf x ∈ g.cycleFactorsFinset
    then (v ⟨g.cycleOf x, hx⟩ : Perm α) x
    else ofSubtype u x := by
  split_ifs with hx
  · have hx' := hx
    rw [cycleOf_mem_cycleFactorsFinset_iff, mem_support, Ne, ← Function.mem_fixedPoints_iff] at hx'
    rw [θHom, MonoidHom.noncommCoprod_apply', mul_apply, ofSubtype_apply_of_not_mem u hx',
      noncommPiCoprod_apply, ← Finset.noncommProd_erase_mul _ (Finset.mem_univ ⟨g.cycleOf x, hx⟩),
      mul_apply, ← not_mem_support]
    contrapose! hx'
    obtain ⟨a, ha1, ha2⟩ := mem_support_of_mem_noncommProd_support hx'
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Ne, Subtype.ext_iff] at ha1
    have key := cycleFactorsFinset_pairwise_disjoint g a.2 hx ha1
    rw [disjoint_iff_disjoint_support, Finset.disjoint_left] at key
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (v a).2
    replace ha2 := key (support_zpow_le a.1 k (hk ▸ ha2))
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (v ⟨g.cycleOf x, hx⟩).2
    rwa [← hk, zpow_apply_mem_support, not_mem_support, cycleOf_apply_self] at ha2
  · rw [cycleOf_mem_cycleFactorsFinset_iff] at hx
    rw [θHom, MonoidHom.noncommCoprod_apply, mul_apply, Equiv.apply_eq_iff_eq, ← not_mem_support]
    contrapose! hx
    obtain ⟨a, -, ha⟩ := mem_support_of_mem_noncommProd_support
      (comm := fun a ha b hb h ↦ g.pairwise_commute_of_mem_zpowers h (v a) (v b) (v a).2 (v b).2) hx
    exact support_zpowers_of_mem_cycleFactorsFinset_le (v a) ha

theorem θHom_apply_of_mem_support_cycle {c} {x}
    (hc : c ∈ g.cycleFactorsFinset) (hx : x ∈ c.support) :
    θHom g (u, v) x = (v ⟨c, hc⟩ : Perm α) x := by
  suffices hx' : _ by
    rw [θHom_apply, dif_pos hx']
    suffices (⟨g.cycleOf x, hx'⟩ : g.cycleFactorsFinset) = ⟨c, hc⟩ by
      rw [this]
    simp [← Subtype.coe_inj, Subtype.coe_eta, cycle_is_cycleOf hx hc]
  rw [cycleOf_mem_cycleFactorsFinset_iff]
  exact mem_cycleFactorsFinset_support_le hc hx

theorem θHom_apply_of_cycleOf_eq {x : α} {c : g.cycleFactorsFinset}
    (hx : x ∈ (c : Perm α).support) : θHom g (u,v) x = (v c : Perm α) x :=
  θHom_apply_of_mem_support_cycle _ hx

theorem θHom_apply_of_cycleOf_not_mem {x : α} (hx : g.cycleOf x ∉ g.cycleFactorsFinset) :
    θHom g (u,v) x = ofSubtype u x := by
  rw [θHom_apply, dif_neg hx]

theorem θHom_injective (g : Perm α) : Function.Injective (θHom g) := by
  rw [θHom, MonoidHom.noncommCoprod_injective]
  refine ⟨ofSubtype_injective, ?_, ?_⟩
  · apply injective_noncommPiCoprod_of_independent
    intro a
    simp only [zpowers_eq_closure, ← closure_iUnion]
    apply disjoint_closure_of_disjoint_support
    rintro - ⟨-⟩ - ⟨-, ⟨b, rfl⟩, -, ⟨h, rfl⟩, ⟨-⟩⟩
    rw [← disjoint_iff_disjoint_support]
    exact cycleFactorsFinset_pairwise_disjoint g a.2 b.2 (mt Subtype.ext_iff.mpr h.symm)
  · rw [noncommPiCoprod_range, ← ofSubtype.range.closure_eq]
    simp only [zpowers_eq_closure, ← closure_iUnion]
    apply disjoint_closure_of_disjoint_support
    rintro - ⟨a, rfl⟩ - ⟨-, ⟨b, rfl⟩, ⟨-⟩⟩
    exact (ofSubtype_support_disjoint a).mono_right (mem_cycleFactorsFinset_support_le b.2)

lemma θHom_range_eq : (θHom g).range = (toPermHom g).ker.map (Subgroup.subtype _) := by
  apply le_antisymm
  · rw [θHom, MonoidHom.noncommCoprod_range, sup_le_iff, noncommPiCoprod_range, iSup_le_iff]
    simp only [zpowers_le]
    constructor
    · rintro - ⟨a, rfl⟩
      refine ⟨⟨ofSubtype a, ?_⟩, ?_, rfl⟩
      · rw [mem_centralizer_singleton_iff]
        exact Disjoint.commute (disjoint_iff_disjoint_support.mpr (ofSubtype_support_disjoint a))
      · exact Perm.ext fun x ↦ Subtype.ext (disjoint_iff_disjoint_support.mpr
          ((ofSubtype_support_disjoint a).mono_right
            (mem_cycleFactorsFinset_support_le x.2))).commute.mul_inv_cancel
    · intro i
      refine ⟨⟨i, mem_centralizer_singleton_iff.mpr (self_mem_cycle_factors_commute i.2)⟩, ?_, rfl⟩
      exact Perm.ext fun x ↦ Subtype.ext (cycleFactorsFinset_mem_commute' g i.2 x.2).mul_inv_cancel
  · rintro - ⟨p, hp, rfl⟩
    simp only [coeSubtype]
    set u : Perm (Function.fixedPoints g) :=
      subtypePerm p (fun x ↦ mem_fixedPoints_iff_apply_mem_of_mem_centralizer p.2)
    simp only [SetLike.mem_coe, mem_ker_toPermHom_iff, IsCycle.forall_commute_iff] at hp
    set v : (c : g.cycleFactorsFinset) → (Subgroup.zpowers (c : Perm α)) :=
      fun c => ⟨ofSubtype
          (p.1.subtypePerm (Classical.choose (hp c.val c.prop))),
            Classical.choose_spec (hp c.val c.prop)⟩
    use (u, v)
    ext x
    rw [θHom_apply]
    split_ifs with hx
    · rw [cycleOf_mem_cycleFactorsFinset_iff, mem_support] at hx
      rw [ofSubtype_apply_of_mem, subtypePerm_apply]
      rwa [mem_support, cycleOf_apply_self, ne_eq]
    · rw [cycleOf_mem_cycleFactorsFinset_iff, not_mem_support] at hx
      rwa [ofSubtype_apply_of_mem, subtypePerm_apply]

theorem θHom_apply_mem_support_cycle_iff_apply_mem
    (c : Perm α) (hc : c ∈ g.cycleFactorsFinset) (x) :
    x ∈ c.support ↔ θHom g (u, v) x ∈ c.support := by
  simp only [← eq_cycleOf_of_mem_cycleFactorsFinset_iff g c hc]
  rw [θHom_apply]
  split_ifs with hx
  · obtain ⟨m, hm⟩ := (v ⟨g.cycleOf x, hx⟩).prop
    simp only [← hm, cycleOf_zpow_apply_self, cycleOf_self_apply_zpow]
  · simp only [ne_of_mem_of_not_mem hc hx, false_iff]
    suffices g.cycleOf (ofSubtype u x) = 1 by
      rw [mem_cycleFactorsFinset_iff] at hc
      rw [this]
      exact hc.1.ne_one
    rw [cycleOf_mem_cycleFactorsFinset_iff, not_mem_support,
      ← Function.mem_fixedPoints_iff] at hx
    rw [cycleOf_eq_one_iff, ← Function.mem_fixedPoints_iff, ofSubtype_apply_of_mem u hx]
    exact Subtype.coe_prop (u ⟨x, hx⟩)

theorem θHom_apply_mem_centralizer : θHom g (u,v) ∈ Subgroup.centralizer {g} := by
  rw [mem_centralizer_singleton_iff]
  set p := θHom g (u,v) with h
  suffices ∀ c ∈ g.cycleFactorsFinset, p * c = c * p by
    rw [← g.cycleFactorsFinset_noncommProd]
    apply Finset.noncommProd_commute
    intro c hc
    simp only [id_eq]
    exact this c hc
  intro c hc
  ext x
  simp only [id_eq, coe_mul, Function.comp_apply]
  by_cases hx : x ∈ c.support
  · rw [h, θHom_apply_of_mem_support_cycle hc hx,
      θHom_apply_of_mem_support_cycle hc (by simp only [apply_mem_support, hx])]
    simp only [← mul_apply]
    apply DFunLike.congr_fun
    rw [← commute_iff_eq]
    obtain ⟨m, hm⟩ := (v ⟨c, hc⟩).prop
    simp only [← hm]
    exact Commute.zpow_left rfl m
  · rw [not_mem_support.mp hx, eq_comm]
    rw [← not_mem_support, ← θHom_apply_mem_support_cycle_iff_apply_mem c hc]
    exact hx

lemma θHom_range_le_centralizer : (θHom g).range ≤ centralizer {g} := by
  rintro _ ⟨⟨u, v⟩, rfl⟩
  exact θHom_apply_mem_centralizer

theorem mem_θHom_range_iff {p : Perm α} : p ∈ (θHom g).range ↔
    (∃ (hp : p ∈ Subgroup.centralizer {g}),
      (⟨p, hp⟩ : Subgroup.centralizer {g}) ∈ (toPermHom g).ker) := by
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    simp only [mem_ker_toPermHom_iff, IsCycle.forall_commute_iff]
    use θHom_apply_mem_centralizer
    intro c hc
    use θHom_apply_mem_support_cycle_iff_apply_mem c hc
    suffices ofSubtype (subtypePerm (θHom g (u,v)) _) = v ⟨c, hc⟩ by
      rw [this]
      exact (v ⟨c, hc⟩).prop
    ext x
    by_cases hx : x ∈ c.support
    · rw [ofSubtype_apply_of_mem, subtypePerm_apply]
      · dsimp only [id_eq, MonoidHom.coe_mk, OneHom.coe_mk, coe_fn_mk, eq_mpr_eq_cast]
        rw [θHom_apply_of_mem_support_cycle hc hx]
      · exact hx
    · rw [ofSubtype_apply_of_not_mem]
      · obtain ⟨m, hm⟩ := (v ⟨c, hc⟩).prop
        rw [← hm, eq_comm, ← not_mem_support]
        intro hx'
        apply hx
        exact (support_zpow_le c m) hx'
      · exact hx
  · rintro ⟨hp_mem, hp⟩
    set u : Perm (Function.fixedPoints g) :=
      subtypePerm p (fun x ↦ mem_fixedPoints_iff_apply_mem_of_mem_centralizer hp_mem)
    simp only [mem_ker_toPermHom_iff, IsCycle.forall_commute_iff] at hp
    set v : (c : g.cycleFactorsFinset) → (Subgroup.zpowers (c : Perm α)) :=
      fun c => ⟨ofSubtype
          (p.subtypePerm (Classical.choose (hp c.val c.prop))),
            Classical.choose_spec (hp c.val c.prop)⟩
    use (u, v)
    ext x
    rw [θHom_apply]
    split_ifs with hx
    · rw [cycleOf_mem_cycleFactorsFinset_iff, mem_support] at hx
      rw [ofSubtype_apply_of_mem, subtypePerm_apply]
      rwa [mem_support, cycleOf_apply_self, ne_eq]
    · rw [cycleOf_mem_cycleFactorsFinset_iff, not_mem_support] at hx
      rwa [ofSubtype_apply_of_mem, subtypePerm_apply]

/- /-- Alternative proof of `θHom_range_eq` -/
lemma θHom_range_eq' : (θHom g).range = (toPermHom g).ker.map (Subgroup.subtype _) := by
  ext p
  simp only [mem_θHom_range_iff, mem_map, coeSubtype, Subtype.exists,
    exists_and_right, exists_eq_right] -/

theorem θHom_range_card (g : Equiv.Perm α) :
    Fintype.card (θHom g).range = (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod := by
  erw [Set.card_range_of_injective (θHom_injective g)]
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_pi, card_fixedPoints]
  apply congr_arg
  rw [Finset.univ_eq_attach, g.cycleFactorsFinset.prod_attach (fun i ↦ Fintype.card (zpowers i)),
    cycleType, Finset.prod_map_val]
  refine Finset.prod_congr rfl (fun x hx ↦ ?_)
  rw [Fintype.card_zpowers, (mem_cycleFactorsFinset_iff.mp hx).1.orderOf, Function.comp_apply]

end Kernel

end OnCycleFactors

open Nat
variable (g)

-- Should one parenthesize the product ?
/-- Cardinality of the centralizer in `Equiv.Perm α` of a permutation given `cycleType` -/
theorem nat_card_centralizer :
    Nat.card (Subgroup.centralizer {g}) =
      (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!) := by
  rw [← (OnCycleFactors.toPermHom g).ker.card_mul_index, index_ker, nat_card_range_toPermHom,
    ← θHom_range_card, ← Nat.card_eq_fintype_card, θHom_range_eq, card_subtype]

theorem card_isConj_mul_eq (g : Equiv.Perm α) :
    Nat.card {h : Equiv.Perm α | IsConj g h} *
      ((Fintype.card α - g.cycleType.sum)! *
      g.cycleType.prod *
      (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!)) =
    (Fintype.card α)! := by
  classical
  rw [Nat.card_eq_fintype_card, ← nat_card_centralizer g]
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer, Nat.card_eq_fintype_card]
  convert MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct (Perm α)) g
  · ext h
    simp only [Set.mem_setOf_eq, ConjAct.mem_orbit_conjAct, isConj_comm]
  · rw [ConjAct.card, Fintype.card_perm]

/-- Cardinality of a conjugacy class in `Equiv.Perm α` of a given `cycleType` -/
theorem card_isConj_eq (g : Equiv.Perm α) :
    Nat.card {h : Equiv.Perm α | IsConj g h} =
      (Fintype.card α)! /
        ((Fintype.card α - g.cycleType.sum)! *
          g.cycleType.prod *
          (∏ n in g.cycleType.toFinset, (g.cycleType.count n)!)) := by
  rw [← card_isConj_mul_eq g, Nat.div_eq_of_eq_mul_left _]
  · rfl
  -- This is the cardinal of the centralizer
  · rw [← nat_card_centralizer g]
    apply Nat.card_pos

variable (α)

theorem card_of_cycleType_eq_zero_iff {m : Multiset ℕ} :
    (Finset.univ.filter fun g : Equiv.Perm α => g.cycleType = m).card = 0
    ↔ ¬ ((m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a)) := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    ← exists_with_cycleType_iff, not_exists]
  aesop

theorem card_of_cycleType_mul_eq (m : Multiset ℕ) :
    (Finset.univ.filter fun g : Equiv.Perm α => g.cycleType = m).card *
        ((Fintype.card α - m.sum)! * m.prod *
          (∏ n in m.toFinset, (m.count n)!)) =
      if (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) then (Fintype.card α)! else 0 := by
  split_ifs with hm
  · -- nonempty case
    classical
    obtain ⟨g, rfl⟩ := (exists_with_cycleType_iff α).mpr hm
    convert card_isConj_mul_eq g
    simp_rw [Set.coe_setOf, Nat.card_eq_fintype_card, ← Fintype.card_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, ← isConj_iff_cycleType_eq, isConj_comm (g := g)]
  · -- empty case
    convert MulZeroClass.zero_mul _
    exact (card_of_cycleType_eq_zero_iff α).mpr hm

/-- Cardinality of the `Finset` of `Equiv.Perm α` of given `cycleType` -/
theorem card_of_cycleType (m : Multiset ℕ) :
    (Finset.univ.filter
      fun g : Perm α => g.cycleType = m).card =
      if m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! * m.prod * (∏ n in m.toFinset, (m.count n)!))
      else 0 := by
  split_ifs with hm
  · -- nonempty case
    apply symm
    apply Nat.div_eq_of_eq_mul_left
    · apply Nat.mul_pos
      · apply Nat.mul_pos
        · apply Nat.factorial_pos
        · apply Multiset.prod_pos
          exact fun a ha ↦ lt_of_lt_of_le (zero_lt_two) (hm.2 a ha)
      · exact Finset.prod_pos (fun _ _ ↦ Nat.factorial_pos _)
    rw [card_of_cycleType_mul_eq, if_pos hm]
  · -- empty case
    exact (card_of_cycleType_eq_zero_iff α).mpr hm

end Equiv.Perm


