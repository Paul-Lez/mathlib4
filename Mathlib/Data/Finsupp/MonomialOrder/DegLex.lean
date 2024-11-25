/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Finsupp.Weight
import Mathlib.Logic.Equiv.TransferInstance

/-! Homogeneous lexicographic monomial ordering

* `MonomialOrder.degLex`: a variant of the lexicographic ordering that first compares degrees.
For this, `σ` needs to be embedded with an ordering relation which satisfies `WellFoundedGT σ`.
(This last property is automatic when `σ` is finite).

The type synonym is `DegLex (σ →₀ ℕ)` and the two lemmas `MonomialOrder.degLex_le_iff`
and `MonomialOrder.degLex_lt_iff` rewrite the ordering as comparisons in the type `Lex (σ →₀ ℕ)`.

## References

* [Cox, Little and O'Shea, *Ideals, varieties, and algorithms*][coxlittleoshea1997]
* [Becker and Weispfenning, *Gröbner bases*][Becker-Weispfenning1993]

-/

section degLex

/-- A type synonym to equip a type with its lexicographic order sorted by degrees. -/
def DegLex (α : Type*) := α

variable {α : Type*}

/-- `toDegLex` is the identity function to the `DegLex` of a type.  -/
@[match_pattern] def toDegLex : α ≃ DegLex α := Equiv.refl _

theorem toDegLex_injective : Function.Injective (toDegLex (α := α)) := fun _ _ ↦ _root_.id

theorem toDegLex_inj {a b : α} : toDegLex a = toDegLex b ↔ a = b := Iff.rfl

/-- `ofDegLex` is the identity function from the `DegLex` of a type.  -/
@[match_pattern] def ofDegLex : DegLex α ≃ α := Equiv.refl _

theorem ofDegLex_injective : Function.Injective (ofDegLex (α := α)) := fun _ _ ↦ _root_.id

theorem ofDegLex_inj {a b : DegLex α} : ofDegLex a = ofDegLex b ↔ a = b := Iff.rfl

@[simp] theorem ofDegLex_symm_eq : (@ofDegLex α).symm = toDegLex := rfl

@[simp] theorem toDegLex_symm_eq : (@toDegLex α).symm = ofDegLex := rfl

@[simp] theorem ofDegLex_toDegLex (a : α) : ofDegLex (toDegLex a) = a := rfl

@[simp] theorem toDegLex_ofDegLex (a : DegLex α) : toDegLex (ofDegLex a) = a := rfl

/-- A recursor for `DegLex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def DegLex.rec {β : DegLex α → Sort*} (h : ∀ a, β (toDegLex a)) :
    ∀ a, β a := fun a => h (ofDegLex a)

@[simp] lemma DegLex.forall_iff {p : DegLex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toDegLex a) := Iff.rfl
@[simp] lemma DegLex.exists_iff {p : DegLex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toDegLex a) := Iff.rfl

noncomputable instance [AddCommMonoid α] :
    AddCommMonoid (DegLex α) := ofDegLex.addCommMonoid

theorem toDegLex_add [AddCommMonoid α] (a b : α) :
    toDegLex (a + b) = toDegLex a + toDegLex b := rfl

theorem ofDegLex_add [AddCommMonoid α] (a b : DegLex α) :
    ofDegLex (a + b) = ofDegLex a + ofDegLex b := rfl

namespace Finsupp

/-- `Finsupp.DegLex r s` is the homogeneous lexicographic order on `α →₀ M`,
where `α` is ordered by `r` and `M` is ordered by `s`.
The type synonym `DegLex (α →₀ M)` has an order given by `Finsupp.DegLex (· < ·) (· < ·)`. -/
protected def DegLex (r : α → α → Prop) (s : ℕ → ℕ → Prop) :
    (α →₀ ℕ) → (α →₀ ℕ) → Prop :=
  (Prod.Lex s (Finsupp.Lex r s)) on (fun x ↦ (x.degree, x))

theorem degLex_def {r : α → α → Prop} {s : ℕ → ℕ → Prop} {a b : α →₀ ℕ} :
    Finsupp.DegLex r s a b ↔ Prod.Lex s (Finsupp.Lex r s) (a.degree, a) (b.degree, b) :=
  Iff.rfl

theorem DegLex.wellFounded
    {r : α → α → Prop} [IsTrichotomous α r] (hr : WellFounded (Function.swap r))
    {s : ℕ → ℕ → Prop} (hs : WellFounded s) (hs0 : ∀ ⦃n⦄, ¬ s n 0) :
    WellFounded (Finsupp.DegLex r s) := by
  have wft := WellFounded.prod_lex hs (Finsupp.Lex.wellFounded' hs0 hs hr)
  rw [← Set.wellFoundedOn_univ] at wft
  unfold Finsupp.DegLex
  rw [← Set.wellFoundedOn_range]
  exact Set.WellFoundedOn.mono wft (le_refl _) (fun _ _ ↦ trivial)

instance [LT α] : LT (DegLex (α →₀ ℕ)) :=
  ⟨fun f g ↦ Finsupp.DegLex (· < ·) (· < ·) (ofDegLex f) (ofDegLex g)⟩

theorem DegLex.lt_def [LT α] {a b : DegLex (α →₀ ℕ)} :
    a < b ↔ (toLex ((ofDegLex a).degree, toLex (ofDegLex a))) <
        (toLex ((ofDegLex b).degree, toLex (ofDegLex b))) :=
  Iff.rfl

theorem DegLex.lt_iff [LT α] {a b : DegLex (α →₀ ℕ)} :
    a < b ↔ (ofDegLex a).degree < (ofDegLex b).degree ∨
    (((ofDegLex a).degree = (ofDegLex b).degree) ∧ toLex (ofDegLex a) < toLex (ofDegLex b)) := by
  simp only [Finsupp.DegLex.lt_def, Prod.Lex.lt_iff]

variable [LinearOrder α]

instance DegLex.isStrictOrder : IsStrictOrder (DegLex (α →₀ ℕ)) (· < ·) :=
  { irrefl := fun a ↦ by simp [DegLex.lt_def]
    trans := by
      intro a b c hab hbc
      simp only [DegLex.lt_iff] at hab hbc ⊢
      rcases hab with (hab | hab)
      · rcases hbc with (hbc | hbc)
        · left; exact lt_trans hab hbc
        · left; exact lt_of_lt_of_eq hab hbc.1
      · rcases hbc with (hbc | hbc)
        · left; exact lt_of_eq_of_lt hab.1 hbc
        · right; exact ⟨Eq.trans hab.1 hbc.1, lt_trans hab.2 hbc.2⟩ }

/-- The partial order on `Finsupp`s obtained by the homogeneous lexicographic ordering.
See `Finsupp.DegLex.linearOrder` for a proof that this partial order is in fact linear. -/
instance DegLex.partialOrder : PartialOrder (DegLex (α →₀ ℕ)) :=
  PartialOrder.lift
    (fun (f : DegLex (α →₀ ℕ)) ↦ toLex ((ofDegLex f).degree, toLex (ofDegLex f)))
    (fun f g ↦ by simp)

theorem DegLex.le_iff {x y : DegLex (α →₀ ℕ)} :
    x ≤ y ↔ (ofDegLex x).degree < (ofDegLex y).degree ∨
      (ofDegLex x).degree = (ofDegLex y).degree ∧ toLex (ofDegLex x) ≤ toLex (ofDegLex y) := by
  simp only [le_iff_eq_or_lt, DegLex.lt_iff, EmbeddingLike.apply_eq_iff_eq]
  by_cases h : x = y
  · simp [h]
  · by_cases k : (ofDegLex x).degree < (ofDegLex y).degree
    · simp [k]
    · simp only [h, k, false_or]

theorem DegLex.single_strictAnti : StrictAnti (fun (a : α) ↦ toDegLex (single a 1)) := by
  intro _ _ h
  simp only [lt_iff, ofDegLex_toDegLex, degree_single, lt_self_iff_false, Lex.single_lt_iff, h,
    and_self, or_true]

theorem DegLex.single_antitone : Antitone (fun (a : α) ↦ toDegLex (single a 1)) :=
  DegLex.single_strictAnti.antitone

theorem DegLex.single_lt_iff {a b : α} :
    toDegLex (Finsupp.single b 1) < toDegLex (Finsupp.single a 1) ↔ a < b :=
  DegLex.single_strictAnti.lt_iff_lt

theorem DegLex.single_le_iff {a b : α} :
    toDegLex (Finsupp.single b 1) ≤ toDegLex (Finsupp.single a 1) ↔ a ≤ b :=
  DegLex.single_strictAnti.le_iff_le

noncomputable instance : OrderedCancelAddCommMonoid (DegLex (α →₀ ℕ)) where
  toAddCommMonoid := ofDegLex.addCommMonoid
  toPartialOrder := DegLex.partialOrder
  le_of_add_le_add_left a b c h := by
    rw [DegLex.le_iff] at h ⊢
    simpa only [ofDegLex_add, degree_add, add_lt_add_iff_left, add_right_inj, toLex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [DegLex.le_iff] at h ⊢
    simpa [ofDegLex_add, degree_add] using h

/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
instance DegLex.linearOrder : LinearOrder (DegLex (α →₀ ℕ)) :=
  LinearOrder.lift'
    (fun (f : DegLex (α →₀ ℕ)) ↦ toLex ((ofDegLex f).degree, toLex (ofDegLex f)))
    (fun f g ↦ by simp)

/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
noncomputable instance :
    LinearOrderedCancelAddCommMonoid (DegLex (α →₀ ℕ)) where
  toOrderedCancelAddCommMonoid := inferInstance
  le_total := DegLex.linearOrder.le_total
  decidableLE := DegLex.linearOrder.decidableLE
  min_def := DegLex.linearOrder.min_def
  max_def := DegLex.linearOrder.max_def
  compare_eq_compareOfLessAndEq := DegLex.linearOrder.compare_eq_compareOfLessAndEq

theorem DegLex.monotone_degree :
    Monotone (fun (x : DegLex (α →₀ ℕ)) ↦ (ofDegLex x).degree) := by
  intro x y
  rw [DegLex.le_iff]
  rintro (h | h)
  · apply le_of_lt h
  · apply le_of_eq h.1

instance DegLex.orderBot : OrderBot (DegLex (α →₀ ℕ)) where
  bot := toDegLex (0 : α →₀ ℕ)
  bot_le x := by
    simp only [DegLex.le_iff, ofDegLex_toDegLex, toLex_zero, degree_zero]
    rcases eq_zero_or_pos (ofDegLex x).degree with (h | h)
    · simp only [h, lt_self_iff_false, true_and, false_or, ge_iff_le]
      exact bot_le
    · simp [h]

instance DegLex.wellFoundedLT [WellFoundedGT α] :
    WellFoundedLT (DegLex (α →₀ ℕ)) :=
  ⟨DegLex.wellFounded wellFounded_gt wellFounded_lt fun n ↦ (zero_le n).not_lt⟩

/-- for the deg-lexicographic ordering, X 1 < X 0 -/
example : toDegLex (single 1 1) < toDegLex (single 0 1) := by
  rw [DegLex.single_lt_iff]
  exact Nat.one_pos

/-- for the deg-lexicographic ordering, X 0 * X 1 < X 0  ^ 2 -/
example : toDegLex (single 0 2) > toDegLex (single 0 1 + single 1 1) := by
  simp only [gt_iff_lt, DegLex.lt_iff, ofDegLex_toDegLex, degree_add]
  simp only [degree_single, Nat.reduceAdd, lt_self_iff_false, true_and, false_or]
  use 0
  simp

/-- for the deg-lexicographic ordering, X 0 < X 1 ^ 2 -/
example : toDegLex (single 0 1) < toDegLex (single 1 2) := by
  simp only [gt_iff_lt, DegLex.lt_iff, ofDegLex_toDegLex, degree_add]
  simp [degree_single]

end Finsupp

open scoped MonomialOrder

open Finsupp

variable {σ : Type*} [LinearOrder σ]

/-- The deg-lexicographic order on `σ →₀ ℕ`, as a `MonomialOrder` -/
noncomputable def MonomialOrder.degLex [WellFoundedGT σ] :
    MonomialOrder σ where
  syn := DegLex (σ →₀ ℕ)
  toSyn := { toEquiv := toDegLex, map_add' := toDegLex_add }
  toSyn_monotone a b h := by
    change toDegLex a ≤ toDegLex b
    simp only [DegLex.le_iff, ofDegLex_toDegLex]
    by_cases ha : a.degree < b.degree
    · exact Or.inl ha
    · refine Or.inr ⟨le_antisymm ?_ (not_lt.mp ha), toLex_monotone h⟩
      rw [← add_tsub_cancel_of_le h, degree_add]
      exact Nat.le_add_right a.degree (b - a).degree

theorem MonomialOrder.degLex_le_iff [WellFoundedGT σ] {a b : σ →₀ ℕ} :
    a ≼[degLex] b ↔ toDegLex a ≤ toDegLex b :=
  Iff.rfl

theorem MonomialOrder.degLex_lt_iff [WellFoundedGT σ] {a b : σ →₀ ℕ} :
    a ≺[degLex] b ↔ toDegLex a < toDegLex b :=
  Iff.rfl

theorem MonomialOrder.degLex_single_le_iff [WellFoundedGT σ] {a b : σ} :
    single a 1 ≼[degLex] single b 1 ↔ b ≤ a := by
  rw [MonomialOrder.degLex_le_iff, DegLex.single_le_iff]

theorem MonomialOrder.degLex_single_lt_iff [WellFoundedGT σ] {a b : σ} :
    single a 1 ≺[degLex] single b 1 ↔ b < a := by
  rw [MonomialOrder.degLex_lt_iff, DegLex.single_lt_iff]

end degLex

