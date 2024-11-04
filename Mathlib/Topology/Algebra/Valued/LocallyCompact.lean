/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Valuation.Archimedean
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Necessary and sufficient conditions for a locally compact nonarchimedean normed field

## Main Results
* `properSpace_iff_completeSpace_and_discreteValuationRing_integer_and_finite_residueField`:
  when the field is locally compact, it is complete and the valuation ring is a DVR and
  has finite residue field

## Tags

norm, nonarchimedean, rank one, compact, locally compact
-/

variable {X Y : Type*} [UniformSpace X] [UniformSpace Y] {s : Set X}

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

open NNReal

namespace Valued.integer

open scoped NormedField

-- should we do this all in the Valuation namespace instead?

@[simp]
lemma v_eq_valuation (x : K) : Valued.v x = NormedField.valuation x := rfl

/-- An element is in the valuation ring if the norm is bounded by 1. This is a variant of
`Valuation.mem_integer_iff`, phrased using norms instead of the valuation. -/
lemma mem_integer_iff' {x : K} : x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1 := by
  simp [Valuation.mem_integer_iff, v_eq_valuation, NormedField.valuation_apply, ← NNReal.coe_le_coe]

lemma norm_le_one (x : 𝒪[K]) : ‖x‖ ≤ 1 := mem_integer_iff'.mp x.prop

lemma norm_unit (u : 𝒪[K]ˣ) : ‖(u : 𝒪[K])‖ = 1 := by
  rcases (norm_le_one u.val).eq_or_lt with hu|hu
  · exact hu
  suffices ‖(u⁻¹).val‖ > 1 from absurd this (norm_le_one _).not_lt
  rw [← norm_one (α := K), ← OneMemClass.coe_one (𝒪[K]), ← u.mul_inv, Subring.coe_mul]
  simpa using hu

@[simp]
lemma nnnorm_one : ‖(1 : 𝒪[K])‖₊ = 1 := coe_inj.mp (by simp)

@[simp]
lemma norm_coe_unit (u : 𝒪[K]ˣ) : ‖((u : 𝒪[K]) : K)‖ = 1 :=
  norm_unit _

lemma isUnit_iff_norm_eq_one {u : 𝒪[K]} : IsUnit u ↔ ‖u‖ = 1 := by
  constructor
  · rintro ⟨_, rfl⟩
    exact norm_unit _
  · intro h
    rw [isUnit_iff_exists_inv]
    have hu : u ≠ 0 := by
      contrapose! h
      simp [h]
    refine ⟨⟨u⁻¹, ?_⟩, ?_⟩
    · rw [← norm_one (α := K)] at h
      rw [Valuation.mem_integer_iff, map_inv₀, inv_le_one₀]
      · simpa [← NNReal.coe_le_coe] using h.ge
      · simp [hu]
    · ext
      simp only [Subring.coe_mul, Subsemiring.coe_toSubmonoid, Subring.coe_toSubsemiring,
        OneMemClass.coe_one]
      rw [mul_inv_eq_one₀ (by exact_mod_cast hu)]

lemma norm_irreducible_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : ‖ϖ‖ < 1 :=
  lt_of_le_of_ne (norm_le_one ϖ) (mt isUnit_iff_norm_eq_one.mpr h.not_unit)

lemma norm_irreducible_pos {ϖ : 𝒪[K]} (h : Irreducible ϖ) : 0 < ‖ϖ‖ :=
  lt_of_le_of_ne (_root_.norm_nonneg ϖ) (by simp [eq_comm, h.ne_zero])

lemma _root_.Irreducible.span_eq_closedBall [DiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    (Ideal.span {ϖ} : Set 𝒪[K]) = Metric.closedBall 0 ‖ϖ‖ := by
  ext x
  rcases eq_or_ne x 0 with rfl|hx
  · simp
  obtain ⟨n, u, rfl⟩ := DiscreteValuationRing.eq_unit_mul_pow_irreducible hx h
  simp only [SetLike.mem_coe, Ideal.mem_span_singleton, Units.isUnit, IsUnit.dvd_mul_left,
    Metric.mem_closedBall, dist_zero_right]
  cases n with
  | zero => simpa [← isUnit_iff_dvd_one, h.not_unit] using norm_irreducible_lt_one h
  | succ n =>
    suffices ‖ϖ ^ n‖ * ‖ϖ‖ ≤ ‖ϖ‖ by
      simpa [dvd_pow, pow_succ] using this
    simp only [AddSubgroupClass.coe_norm, SubmonoidClass.coe_pow, norm_pow]
    rw [mul_le_iff_le_one_left (by exact_mod_cast norm_irreducible_pos h)]
    exact pow_le_one₀ (_root_.norm_nonneg _) (norm_le_one _)

lemma _root_.Irreducible.maximalIdeal_eq_closedBall [DiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    (𝓂[K] : Set 𝒪[K]) = Metric.closedBall 0 ‖ϖ‖ := by
  rw [← h.span_eq_closedBall, ← h.maximalIdeal_eq]

lemma _root_.Irreducible.maximalIdeal_pow_eq_closedBall_pow [DiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) (n : ℕ) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) = Metric.closedBall 0 (‖ϖ‖ ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top, Submodule.top_coe, AddSubgroupClass.coe_norm]
    ext
    simpa using norm_le_one _
  | succ n IH =>
    ext x
    rw [pow_succ, pow_succ]
    simp only [SetLike.mem_coe, AddSubgroupClass.coe_norm, Metric.mem_closedBall, dist_zero_right]
    rw [Valued.maximalIdeal, h.maximalIdeal_eq, Ideal.mem_mul_span_singleton, ← h.maximalIdeal_eq,
        ← Valued.maximalIdeal]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp only [Subring.coe_mul, Subsemiring.coe_toSubmonoid, Subring.coe_toSubsemiring,
        norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (_root_.norm_nonneg _)
      simpa [← SetLike.mem_coe, IH, Metric.mem_closedBall, dist_eq_norm] using hz
    · intro hx
      rcases eq_or_ne x 0 with rfl|hx'
      · refine ⟨0, ?_⟩
        simp
      obtain ⟨k, u, rfl⟩ := DiscreteValuationRing.eq_unit_mul_pow_irreducible hx' h
      simp only [Subring.coe_mul, Subsemiring.coe_toSubmonoid, Subring.coe_toSubsemiring,
        SubmonoidClass.coe_pow, norm_mul, norm_coe_unit, norm_pow, one_mul, ← pow_succ] at hx
      have : n + 1 ≤ k := by
        contrapose! hx
        exact pow_lt_pow_right_of_lt_one (norm_irreducible_pos h) (norm_irreducible_lt_one h) hx
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' this
      simp_rw [← add_assoc, pow_succ, ← mul_assoc]
      refine ⟨_, ?_, rfl⟩
      simpa [← SetLike.mem_coe, IH, Metric.mem_closedBall]
        using pow_le_pow_of_le_one (_root_.norm_nonneg ϖ) (norm_le_one _) (le_add_self)

section FiniteResidueField

open Valued

lemma finite_quotient_maximalIdeal_pow_of_finite_residueField [DiscreteValuationRing 𝒪[K]]
    (h : Finite 𝓀[K]) (n : ℕ) :
    Finite (𝒪[K] ⧸ 𝓂[K] ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    exact Finite.of_fintype (↥𝒪[K] ⧸ ⊤)
  | succ n ih =>
    have : 𝓂[K] ^ (n + 1) ≤ 𝓂[K] ^ n := Ideal.pow_le_pow_right (by simp)
    replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE this).symm.toEquiv
    suffices Finite (Ideal.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))) (𝓂[K] ^ n)) from
      Finite.of_finite_quot_finite_ideal
        (I := Ideal.map (Ideal.Quotient.mk _) (𝓂[K] ^ n))
    exact @Finite.of_equiv _ _ h
      ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal 𝓂[K])
        (DiscreteValuationRing.not_a_field _) n).trans
        (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ n))

lemma totallyBounded_iff_finite_residueField [DiscreteValuationRing 𝒪[K]] :
    TotallyBounded (Set.univ (α := 𝒪[K])) ↔ Finite 𝓀[K] := by
  constructor
  · intro H
    obtain ⟨p, hp⟩ := DiscreteValuationRing.exists_irreducible 𝒪[K]
    have := Metric.finite_approx_of_totallyBounded H ‖p‖ (norm_pos_iff.mpr hp.ne_zero)
    simp only [Set.subset_univ, Set.univ_subset_iff, true_and] at this
    obtain ⟨t, ht, ht'⟩ := this
    rw [← Set.finite_univ_iff]
    refine (ht.image (LocalRing.residue _)).subset ?_
    rintro ⟨x⟩
    replace ht' := ht'.ge (Set.mem_univ x)
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at ht'
    obtain ⟨y, hy, hy'⟩ := ht'
    simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Set.mem_univ,
      LocalRing.residue, Set.mem_image, true_implies]
    refine ⟨y, hy, ?_⟩
    convert (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := 𝓂[K]) y x).mpr _
    -- TODO: make Valued.maximalIdeal abbreviations instead of def
    rw [Valued.maximalIdeal, hp.maximalIdeal_eq, ← SetLike.mem_coe, hp.span_eq_closedBall]
    rw [dist_comm] at hy'
    simpa [dist_eq_norm] using hy'.le
  · intro H
    rw [Metric.totallyBounded_iff]
    intro ε εpos
    obtain ⟨p, hp⟩ := DiscreteValuationRing.exists_irreducible 𝒪[K]
    have hp' := norm_irreducible_lt_one hp
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖p‖ ^ n < ε := exists_pow_lt_of_lt_one εpos hp'
    have hF := finite_quotient_maximalIdeal_pow_of_finite_residueField H n
    refine ⟨Quotient.out' '' (Set.univ (α := 𝒪[K] ⧸ (𝓂[K] ^ n))), Set.toFinite _, ?_⟩
    simp only [Ideal.univ_eq_iUnion_image_add (𝓂[K] ^ n), hp.maximalIdeal_pow_eq_closedBall_pow,
      AddSubgroupClass.coe_norm, Set.image_add_left, preimage_add_closedBall, sub_neg_eq_add,
      zero_add, Set.image_univ, Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.iUnion_subset_iff, Metric.vadd_closedBall, vadd_eq_add, add_zero]
    intro
    exact (Metric.closedBall_subset_ball hn).trans (Set.subset_iUnion_of_subset _ le_rfl)

end FiniteResidueField

section CompactDVR

open Valued

variable (K) in
lemma exists_norm_coe_lt : ∃ x : 𝒪[K], 0 < ‖(x : K)‖ ∧ ‖(x : K)‖ < 1 := by
  obtain ⟨x, hx, hx'⟩ := NormedField.exists_norm_lt_one K
  refine ⟨⟨x, hx'.le⟩, ?_⟩
  simpa [hx', Subtype.ext_iff] using hx

variable (K) in
lemma exists_norm_lt : ∃ x : 𝒪[K], 0 < ‖x‖ ∧ ‖x‖ < 1 := by
  exact exists_norm_coe_lt K

variable (K) in
lemma exists_nnnorm_lt : ∃ x : 𝒪[K], 0 < ‖x‖₊ ∧ ‖x‖₊ < 1 := by
  exact exists_norm_coe_lt K

lemma discreteValuationRing_of_compactSpace [h : CompactSpace 𝒪[K]] :
    DiscreteValuationRing 𝒪[K] := by
  have hl : LocalRing 𝒪[K] := inferInstance
  obtain ⟨x, hx, hx'⟩ := exists_nnnorm_lt K
  rw [← nnnorm_one (K := K)] at hx'
  have hi : Valuation.Integers (R := K) Valued.v 𝒪[K] := Valuation.integer.integers v
  have key : IsPrincipalIdealRing 𝒪[K]:= by
    rw [hi.isPrincipalIdealRing_iff_not_denselyOrdered]
    intro H
    replace H : DenselyOrdered (Set.range ((‖·‖₊) : 𝒪[K] → ℝ≥0)) := by
      constructor
      rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ h
      replace h : (⟨_, a, rfl⟩ : Set.range (v : K → ℝ≥0)) < ⟨_, b, rfl⟩ := h
      obtain ⟨⟨_, c, rfl⟩, hc⟩ := exists_between h
      refine ⟨⟨_, ⟨c, ?_⟩, rfl⟩, hc⟩
      · rw [mem_integer_iff']
        simp only [v_eq_valuation, NormedField.valuation_apply, Subtype.mk_lt_mk, ← coe_lt_coe,
          coe_nnnorm] at hc
        simpa using hc.right.le.trans (mem_integer_iff'.mp b.prop)
    let U : 𝒪[K] → Set 𝒪[K] := fun y ↦ if ‖y‖₊ < ‖x‖₊
      then Metric.closedBall 0 ‖x‖
      else Metric.sphere 0 ‖y‖
    obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover U <| by
      intro y
      simp only [AddSubgroupClass.coe_norm, U]
      split_ifs with hy
      · refine (IsUltrametricDist.isOpen_closedBall _ ?_).mem_nhds (by simpa using hy.le)
        simpa using hx
      · refine (IsUltrametricDist.isOpen_sphere _ ?_).mem_nhds (by simp)
        simpa using (hx.trans_le (le_of_not_lt hy)).ne'
    have htm : ∀ y : 𝒪[K], ‖x‖₊ < ‖y‖₊ → ∃ z ∈ t, ‖z‖₊ = ‖y‖₊ := by
      intro y hy
      have := ht.ge (Set.mem_univ y)
      simp only [AddSubgroupClass.coe_norm, Set.mem_iUnion, exists_prop', nonempty_prop, U] at this
      obtain ⟨z, hz, hz'⟩ := this
      split_ifs at hz' with h
      · simp only [← coe_lt_coe, coe_nnnorm, AddSubgroupClass.coe_norm] at hy
        simp [hy.not_le] at hz'
      · simp only [mem_sphere_iff_norm, sub_zero, AddSubgroupClass.coe_norm] at hz'
        refine ⟨z, hz, ?_⟩
        simp [← coe_inj, hz']
    obtain ⟨y, _, hy'⟩ : ∃ y : 𝒪[K], y ∈ t ∧ ‖y‖₊ = 1 := by simpa using htm 1 hx'
    obtain ⟨w, hwt, hw1, hxw⟩ : ∃ w : 𝒪[K], w ∈ t ∧ ‖w‖₊ < 1 ∧ ‖x‖₊ < ‖w‖₊ := by
      replace hx' : (⟨_, x, rfl⟩ : Set.range ((‖·‖₊) : 𝒪[K] → ℝ≥0)) < ⟨_, 1, rfl⟩ := hx'
      obtain ⟨⟨_, w, rfl⟩, hw, hw'⟩ := exists_between hx'
      obtain ⟨u, hu, hu'⟩ := htm w hw
      exact ⟨u, hu, hu' ▸ by simpa using hw', hu' ▸ by simpa using hw⟩
    let u := t.filter (fun a ↦ ‖a‖₊ < 1)
    have hwu : w ∈ u := by simp [u, hwt, hw1]
    obtain ⟨l, hl, hl'⟩ := u.sup'_mem (((‖·‖₊) : 𝒪[K] → ℝ≥0) '' u)
      (fun x hx y hy ↦ (max_cases x y).elim
        (fun h ↦ (sup_eq_max (a := x) (b := y) ▸ h).left.symm ▸ hx)
        (fun h ↦ (sup_eq_max (a := x) (b := y) ▸ h).left.symm ▸ hy))
      ⟨w, hwu⟩ (‖·‖₊) (fun _ ↦ Set.mem_image_of_mem _)
    simp only at hl'
    have hm : (⟨‖l‖₊, l, rfl⟩ : Set.range ((‖·‖₊) : 𝒪[K] → ℝ≥0)) < (⟨1, y, hy'⟩) := by
      simp only [Finset.coe_filter, Set.mem_setOf_eq, u] at hl
      simp [hl.right]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := exists_between hm
    simp only [Subtype.mk_lt_mk] at hm
    obtain ⟨n, hn, hn'⟩ : ∃ n ∈ t, ‖n‖₊ = ‖m‖₊ := by
      refine htm m (hxw.trans (hm.left.trans_le' ?_))
      rw [hl', Finset.le_sup'_iff]
      exact ⟨w, hwu, le_rfl⟩
    rw [← hn'] at hm
    refine hm.left.not_le ?_
    rw [hl', Finset.le_sup'_iff]
    refine ⟨n, ?_, le_rfl⟩
    simp [u, hn, hm.right]
  exact {
    __ := hl
    __ := key
    not_a_field' := by
      simp only [ne_eq, Ideal.ext_iff, LocalRing.mem_maximalIdeal, mem_nonunits_iff, Ideal.mem_bot,
        not_forall, isUnit_iff_norm_eq_one]
      refine ⟨x, ?_⟩
      simp only [← coe_lt_coe, coe_zero, coe_nnnorm, norm_pos_iff, ne_eq,
        ZeroMemClass.coe_eq_zero, nnnorm_one, coe_one] at hx hx'
      simpa [hx] using hx'.ne
  }

end CompactDVR

lemma compactSpace_iff_completeSpace_and_discreteValuationRing_and_finite_residueField :
    CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ DiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _, h⟩ ↦ ⟨?_⟩⟩
  · have : DiscreteValuationRing 𝒪[K] := discreteValuationRing_of_compactSpace
    refine ⟨complete_of_compact, by assumption, ?_⟩
    rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete,
        totallyBounded_iff_finite_residueField] at h
    exact h.left
  · rw [← totallyBounded_iff_finite_residueField] at h
    rw [isCompact_iff_totallyBounded_isComplete]
    exact ⟨h, completeSpace_iff_isComplete_univ.mp ‹_›⟩

lemma properSpace_iff_compactSpace_integer :
    ProperSpace K ↔ CompactSpace 𝒪[K] := by
  simp only [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype,
             mem_integer_iff', ← mem_closedBall_zero_iff, Set.setOf_mem_eq]
  constructor <;> intro h
  · exact isCompact_closedBall 0 1
  · suffices LocallyCompactSpace K from .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup h <|
      Metric.closedBall_mem_nhds 0 zero_lt_one

lemma properSpace_iff_completeSpace_and_discreteValuationRing_integer_and_finite_residueField :
    ProperSpace K ↔ CompleteSpace K ∧ DiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  simp only [properSpace_iff_compactSpace_integer,
      compactSpace_iff_completeSpace_and_discreteValuationRing_and_finite_residueField,
      completeSpace_iff_isComplete_univ (α := 𝒪[K]), Subtype.isComplete_iff,
      NormedField.completeSpace_iff_isComplete_closedBall, Set.image_univ,
      Subtype.range_coe_subtype, mem_integer_iff', ← mem_closedBall_zero_iff, Set.setOf_mem_eq]

end Valued.integer
