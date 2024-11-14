/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Docstring

-/

noncomputable section

open Filter Topology Finset Asymptotics Metric MeasureTheory

variable (f : ℕ → ℂ) {l : ℝ}

abbrev S : ℝ → ℂ := fun t ↦ ∑ n ∈ range (⌊t + 1⌋₊), f n

theorem S_at_nat (k : ℕ) :
    S f k = ∑ n ∈ range (k + 1), f n := by
  rw [S, Nat.floor_add_one k.cast_nonneg, Nat.floor_natCast]

theorem S_succ (k : ℕ) :
    S f (k + 1) = f (k + 1) + S f k := by
  rw [S, S,  Nat.floor_add_one (by positivity), sum_range_succ_comm, Nat.floor_add_one
    k.cast_nonneg, Nat.floor_natCast]

theorem S_zero : S f 0 = f 0 := by
  rw [S, zero_add, ← Nat.cast_one, Nat.floor_natCast, range_one, sum_singleton]

theorem S_one : S f 1 = f 1 + f 0 := by
  rw [show (1 : ℝ) = (0 : ℕ) + 1 by norm_num, S_succ, Nat.cast_zero, S_zero]

theorem S_at_neg (r : ℝ) (hr : r ≤ -1) : S f r = 0 := by
  convert sum_range_zero f
  refine Nat.floor_of_nonpos (by linarith)

theorem S_in_Ico {n : ℕ} {x : ℝ} (hx : x ∈ Set.Ico (n : ℝ) (n + 1)) :
    S f x = S f n := by
  rw [S, S, Nat.floor_add_one (n.cast_nonneg.trans hx.1), Nat.floor_add_one n.cast_nonneg,
    Nat.floor_natCast, Nat.floor_eq_on_Ico n x hx]

-- theorem S_bdd_Ioc (a b : ℝ) :
theorem step1 (n : ℕ) :
    f n = S f n - S f (n - 1) := by
  cases n with
  | zero => simp [S]
  | succ n =>
    rw [Nat.cast_add, Nat.cast_one, S_succ, add_sub_cancel_right, add_sub_cancel_right]

theorem step2 (n : ℕ) (b : ℕ → ℂ) :
    ∑ k ∈ range (n + 1), (f k) * (b k) =
      S f n * b n + ∑ k ∈ range n, S f k * (b k - b (k + 1)) := by
  simp_rw [step1 f, sub_mul, sum_sub_distrib]
  conv_lhs =>
    enter [1]
    rw [sum_range_succ_comm]
  conv_lhs =>
    enter [2]
    rw [sum_range_succ']
  simp_rw [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_sub, S_at_neg f (-1 : ℝ) le_rfl,
    zero_mul, add_zero, add_sub_cancel_right]
  rw [add_sub_assoc, ← sum_sub_distrib]
  simp_rw [← mul_sub]

theorem step3_1 (n : ℕ) (s : ℂ) (hn : 0 < n) (hs : s ≠ 0) :
    S f n / (n : ℂ) ^ s - S f n / (n + 1) ^ s =
      s * ∫ t in Set.Ioc (n : ℝ) (n + 1), S f t / t ^ (s + 1) := by
  rw [setIntegral_congr_set Ico_ae_eq_Ioc.symm]
  rw [setIntegral_congr_fun measurableSet_Ico (by
    intro t ht
    simp_rw [S_in_Ico f ht]
    rfl)]
  simp_rw [div_eq_mul_inv, integral_mul_left, ← Complex.cpow_neg,
    setIntegral_congr_set Ico_ae_eq_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith), integral_cpow, neg_add,
    neg_add_cancel_right, div_neg, mul_neg, mul_neg, ← mul_div_assoc, mul_div_cancel₀ _ hs,
    mul_sub, neg_sub, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  right
  constructor
  · rwa [ne_eq, neg_add, add_left_eq_self, neg_eq_zero]
  · exact Set.not_mem_uIcc_of_lt (Nat.cast_pos.mpr hn) (by linarith)

theorem step3_2 (s : ℂ) (hs : 0 < s.re) (n : ℕ) (hn : 0 < n) :
    IntegrableOn (fun t ↦ S f t / ↑t ^ (s + 1)) (Set.Ioc (n : ℝ) (n + 1)) := by
  rw [IntegrableOn, Measure.restrict_congr_set Ico_ae_eq_Ioc.symm, ← IntegrableOn]
  rw [integrableOn_congr_fun (fun t ht ↦ by simp_rw [S_in_Ico f ht]; rfl) measurableSet_Ico]
  rw [IntegrableOn, Measure.restrict_congr_set Ico_ae_eq_Ioc, ← IntegrableOn]
  simp_rw [div_eq_mul_inv, ← Complex.cpow_neg]
  refine Integrable.const_mul ?_ _
  refine  (integrableOn_Ioi_cpow_of_lt ?_ ( Nat.cast_pos.mpr hn)).mono_set  ?_
  · simpa using hs
  · exact Set.Ioc_subset_Ioi_self

theorem step3_3 (s : ℂ) (hs : 0 < s.re) (n m : ℕ) (ha : 0 < n) :
    IntegrableOn (fun t ↦ S f t / t ^ (s + 1)) (Set.Ioc n m) := by
  convert integrableOn_finset_iUnion.mpr
    (fun (k : ℕ) (hk : k ∈ Finset.Ico n m) ↦ step3_2 f s hs k ?_) -- (ha.trans (mem_Ioc.mp hk).1))
  · ext x
    --- look around toIocMod...
    simp_rw [Set.mem_Ioc, mem_Ico, Set.mem_iUnion, Set.Ioc, Set.mem_setOf_eq, exists_and_left,
      exists_prop]
    constructor
    · intro h
      refine ⟨⌊x⌋₊, ?_, ⟨?_, ?_⟩, ?_⟩
      · sorry
      · sorry
      · sorry
      · sorry
    · rintro ⟨i, h₁, ⟨h₂, h₃⟩, h₄⟩
      refine ⟨?_, ?_⟩
      · refine lt_of_le_of_lt ?_ h₁
        rw [Nat.cast_le]
        exact h₂
      · refine le_trans h₄ ?_
        rw [← Nat.cast_add_one, Nat.cast_le]
        exact h₃
  · exact lt_of_lt_of_le ha (mem_Ico.mp hk).1

theorem step3 (hf₀ : f 0 = 0) (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ∑ k ∈ range (n + 1), (f k) / (k : ℂ) ^ s = S f n / (n : ℂ) ^ s +
      s * ∫ t in Set.Ioc (1 : ℝ) n, (S f t) / t ^ (s + 1) := by
  have hs₀ : s ≠ 0 := by
    contrapose! hs
    rw [hs, Complex.zero_re]
  induction n with
  | zero => simp [hs₀]
  | succ n ih =>
      by_cases hn : 1 ≤ n
      · rw [sum_range_succ_comm, ih, step1 f, Nat.cast_add, Nat.cast_one, sub_div, ← add_assoc,
          add_comm_sub, add_assoc, add_right_inj, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
          step3_1 _ _ _ hn hs₀, ← mul_add, ← setIntegral_union, Set.Ioc_union_Ioc, min_eq_right,
          max_eq_left]
        · sorry
        · exact Nat.one_le_cast.mpr hn
        · rw [min_eq_left, max_eq_right]
          · exact Nat.one_le_cast.mpr hn
          · sorry -- linarith
        · rw [min_eq_left, max_eq_right]
          · sorry -- linarith
          · sorry -- linarith
          · exact Nat.one_le_cast.mpr hn
        · exact Set.Ioc_disjoint_Ioc_same.symm
        · exact measurableSet_Ioc
        · convert step3_3 f s hs n (n + 1) hn
          rw [Nat.cast_add, Nat.cast_one]
        · convert step3_3 f s hs 1 n zero_lt_one
          rw [Nat.cast_one]
      · have : n = 0 := Nat.eq_zero_of_not_pos hn
        rw [this, Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, zero_add, Set.Ioc_eq_empty,
          Measure.restrict_empty, integral_zero_measure, mul_zero, add_zero, Nat.cast_one,
          Complex.one_cpow, div_one, S_one, sum_range_succ_comm, sum_range_succ_comm,
          sum_range_zero, add_zero, Nat.cast_one, Nat.cast_zero, Complex.one_cpow, div_one,
          Complex.zero_cpow hs₀, div_zero, hf₀]
        exact gt_irrefl 1

#exit


  simp_rw  (config := {singlePass := true}) [div_eq_mul_inv, step2, ← Complex.cpow_neg,
    Nat.cast_add, Nat.cast_one, ← Complex.ofReal_natCast, step3_1 _ _ sorry sorry,
    neg_mul, neg_neg, mul_rotate' _ s, ← mul_sum, ← integral_mul_right]
  have : ∀ n : ℕ, ∫ t in Set.Ioc (n : ℝ) (n + 1), t ^ (-s - 1) * S f (n + 1) =
      ∫ t in Set.Ioc (n : ℝ) (n + 1), t ^ (-s - 1) * S f t := by
    intro n
    rw [setIntegral_congr_set Ico_ae_eq_Ioc.symm, setIntegral_congr_set Ico_ae_eq_Ioc.symm]
    refine setIntegral_congr_fun measurableSet_Ico fun t ht ↦ ?_
    rw [S_in_Ioc _ ht]
  simp_rw [this, ← intervalIntegral.integral_of_le sorry]

  have := intervalIntegral.sum_integral_adjacent_intervals (n := n) (a := fun k ↦ (k + 1 : ℝ))
    (f := fun t ↦ (t : ℂ) ^ (-s - 1) * S f t) (μ := volume) sorry
  simp at this
  rw [this]


theorem integral_repr (s : ℂ) (hs : LSeriesSummable f s):
    LSeries f s = s * (∫ t in Set.Ioi (1 : ℝ), (S f t) / t ^ (s + 1)) := by
  have : Tendsto (fun n ↦ ∑ k in range n, LSeries.term f s k) atTop (𝓝 (LSeries f s)) :=
    hs.hasSum.tendsto_sum_nat
  sorry

theorem assume1 {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, ‖S f t - l * t‖ ≤ ε := sorry

theorem final_step1 (s : ℝ) (ε : ℝ) :
    ∃ c, ‖(LSeries f s) / s - l / (s - 1)‖ ≤ ε / (s - 1) + c := sorry

theorem final_step2 (ε : ℝ) (hε : 0 < ε) :
    limsup (fun s : ℝ ↦ ‖(s - 1) * LSeries f s - l‖) (𝓝[<] 1) ≤ ε := sorry

theorem final : Tendsto (fun s : ℝ ↦ (s - 1) * LSeries f s) (𝓝[>] 1) (𝓝 l) := sorry
