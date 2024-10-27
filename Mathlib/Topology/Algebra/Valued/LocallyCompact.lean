/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Necessary and sufficient conditions for a locally compact nonarchimedean normed field

## Main Definitions
* `totallyBounded_iff_finite_residueField`: when the valuation ring is a DVR,
  it is totally bounded iff the residue field is finite.

## Tags

norm, nonarchimedean, rank one, compact, locally compact
-/

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

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

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

end Valued.integer
