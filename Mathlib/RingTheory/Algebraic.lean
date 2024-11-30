/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Algebra.MvPolynomial.Supported

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.
The main result in this file proves transitivity of algebraicity:
a tower of algebraic field extensions is algebraic.
-/


universe u v w

open scoped Classical
open Polynomial

section

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- An element of an R-algebra is algebraic over R if it is a root of a nonzero polynomial
with coefficients in R. -/
@[stacks 09GC "Algebraic elements"]
def IsAlgebraic (x : A) : Prop :=
  ∃ p : R[X], p ≠ 0 ∧ aeval x p = 0

/-- An element of an R-algebra is transcendental over R if it is not algebraic over R. -/
def Transcendental (x : A) : Prop :=
  ¬IsAlgebraic R x

@[nontriviality]
theorem is_transcendental_of_subsingleton [Subsingleton R] (x : A) : Transcendental R x :=
  fun ⟨p, h, _⟩ => h <| Subsingleton.elim p 0

theorem IsAlgebraic.nontrivial {a : A} (h : IsAlgebraic R a) : Nontrivial R := by
  contrapose! h
  rw [not_nontrivial_iff_subsingleton] at h
  apply is_transcendental_of_subsingleton

variable {R}

/-- An element `x` is transcendental over `R` if and only if for any polynomial `p`,
`Polynomial.aeval x p = 0` implies `p = 0`. This is similar to `algebraicIndependent_iff`. -/
theorem transcendental_iff {x : A} :
    Transcendental R x ↔ ∀ p : R[X], aeval x p = 0 → p = 0 := by
  rw [Transcendental, IsAlgebraic, not_exists]
  congr! 1; tauto

variable (R) in
theorem Polynomial.transcendental_X : Transcendental R (X (R := R)) := by
  simp [transcendental_iff]

theorem IsAlgebraic.of_aeval {r : A} (f : R[X]) (hf : f.natDegree ≠ 0)
    (hf' : f.leadingCoeff ∈ nonZeroDivisors R) (H : IsAlgebraic R (aeval r f)) :
    IsAlgebraic R r := by
  obtain ⟨p, h1, h2⟩ := H
  have : (p.comp f).coeff (p.natDegree * f.natDegree) ≠ 0 := fun h ↦ h1 <| by
    rwa [coeff_comp_degree_mul_degree hf,
      mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hf' _),
      leadingCoeff_eq_zero] at h
  exact ⟨p.comp f, fun h ↦ this (by simp [h]), by rwa [aeval_comp]⟩

theorem Transcendental.aeval {r : A} (H : Transcendental R r) (f : R[X]) (hf : f.natDegree ≠ 0)
    (hf' : f.leadingCoeff ∈ nonZeroDivisors R) :
    Transcendental R (aeval r f) := fun h ↦ H (h.of_aeval f hf hf')

/-- If `r : A` and `f : R[X]` are transcendental over `R`, then `Polynomial.aeval r f` is also
transcendental over `R`. For the converse, see `Transcendental.of_aeval` and
`transcendental_aeval_iff`. -/
theorem Transcendental.aeval_of_transcendental {r : A} (H : Transcendental R r)
    {f : R[X]} (hf : Transcendental R f) : Transcendental R (Polynomial.aeval r f) := by
  rw [transcendental_iff] at H hf ⊢
  intro p hp
  exact hf _ (H _ (by rwa [← aeval_comp, comp_eq_aeval] at hp))

/-- If `Polynomial.aeval r f` is transcendental over `R`, then `f : R[X]` is also
transcendental over `R`. In fact, the `r` is also transcendental over `R` provided that `R`
is a field (see `transcendental_aeval_iff`). -/
theorem Transcendental.of_aeval {r : A} {f : R[X]}
    (H : Transcendental R (Polynomial.aeval r f)) : Transcendental R f := by
  rw [transcendental_iff] at H ⊢
  intro p hp
  exact H p (by rw [← aeval_comp, comp_eq_aeval, hp, map_zero])

theorem IsAlgebraic.of_aeval_of_transcendental {r : A} {f : R[X]}
    (H : IsAlgebraic R (aeval r f)) (hf : Transcendental R f) : IsAlgebraic R r := by
  contrapose H
  exact Transcendental.aeval_of_transcendental H hf

theorem Polynomial.transcendental (f : R[X]) (hf : f.natDegree ≠ 0)
    (hf' : f.leadingCoeff ∈ nonZeroDivisors R) :
    Transcendental R f := by
  simpa using (transcendental_X R).aeval f hf hf'

/-- If `E / F` is a field extension, `x` is an element of `E` transcendental over `F`,
then `{(x - a)⁻¹ | a : F}` is linearly independent over `F`. -/
theorem Transcendental.linearIndependent_sub_inv
    {F E : Type*} [Field F] [Field E] [Algebra F E] {x : E} (H : Transcendental F x) :
    LinearIndependent F fun a ↦ (x - algebraMap F E a)⁻¹ := by
  rw [transcendental_iff] at H
  refine linearIndependent_iff'.2 fun s m hm i hi ↦ ?_
  have hnz (a : F) : x - algebraMap F E a ≠ 0 := fun h ↦
    X_sub_C_ne_zero a <| H (.X - .C a) (by simp [h])
  let b := s.prod fun j ↦ x - algebraMap F E j
  have h1 : ∀ i ∈ s, m i • (b * (x - algebraMap F E i)⁻¹) =
      m i • (s.erase i).prod fun j ↦ x - algebraMap F E j := fun i hi ↦ by
    simp_rw [b, ← s.prod_erase_mul _ hi, mul_inv_cancel_right₀ (hnz i)]
  replace hm := congr(b * $(hm))
  simp_rw [mul_zero, Finset.mul_sum, mul_smul_comm, Finset.sum_congr rfl h1] at hm
  let p : Polynomial F := s.sum fun i ↦ .C (m i) * (s.erase i).prod fun j ↦ .X - .C j
  replace hm := congr(Polynomial.aeval i $(H p (by simp_rw [← hm, p, map_sum, map_mul, map_prod,
    map_sub, aeval_X, aeval_C, Algebra.smul_def])))
  have h2 : ∀ j ∈ s.erase i, m j * ((s.erase j).prod fun x ↦ i - x) = 0 := fun j hj ↦ by
    have := Finset.mem_erase_of_ne_of_mem (Finset.ne_of_mem_erase hj).symm hi
    simp_rw [← (s.erase j).prod_erase_mul _ this, sub_self, mul_zero]
  simp_rw [map_zero, p, map_sum, map_mul, map_prod, map_sub, aeval_X,
    aeval_C, Algebra.id.map_eq_self, ← s.sum_erase_add _ hi,
    Finset.sum_eq_zero h2, zero_add] at hm
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (Finset.prod_ne_zero_iff.2 fun j hj ↦
    sub_ne_zero.2 (Finset.ne_of_mem_erase hj).symm) hm

/-- A subalgebra is algebraic if all its elements are algebraic. -/
nonrec
def Subalgebra.IsAlgebraic (S : Subalgebra R A) : Prop :=
  ∀ x ∈ S, IsAlgebraic R x

variable (R A)

/-- An algebra is algebraic if all its elements are algebraic. -/
@[stacks 09GC "Algebraic extensions"]
protected class Algebra.IsAlgebraic : Prop where
  isAlgebraic : ∀ x : A, IsAlgebraic R x

/-- An algebra is transcendental if some element is transcendental. -/
protected class Algebra.Transcendental : Prop where
  transcendental : ∃ x : A, Transcendental R x

variable {R A}

instance (priority := low) Algebra.transcendental_of_subsingleton [Subsingleton R] :
    Algebra.Transcendental R A :=
  ⟨⟨0, is_transcendental_of_subsingleton R 0⟩⟩

lemma Algebra.isAlgebraic_def : Algebra.IsAlgebraic R A ↔ ∀ x : A, IsAlgebraic R x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma Algebra.transcendental_def : Algebra.Transcendental R A ↔ ∃ x : A, Transcendental R x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

theorem Algebra.transcendental_iff_not_isAlgebraic :
    Algebra.Transcendental R A ↔ ¬ Algebra.IsAlgebraic R A := by
  simp [isAlgebraic_def, transcendental_def, Transcendental]

/-- A subalgebra is algebraic if and only if it is algebraic as an algebra. -/
theorem Subalgebra.isAlgebraic_iff (S : Subalgebra R A) :
    S.IsAlgebraic ↔ Algebra.IsAlgebraic R S := by
  delta Subalgebra.IsAlgebraic
  rw [Subtype.forall', Algebra.isAlgebraic_def]
  refine forall_congr' fun x => exists_congr fun p => and_congr Iff.rfl ?_
  have h : Function.Injective S.val := Subtype.val_injective
  conv_rhs => rw [← h.eq_iff, map_zero]
  rw [← aeval_algHom_apply, S.val_apply]

/-- An algebra is algebraic if and only if it is algebraic as a subalgebra. -/
theorem Algebra.isAlgebraic_iff : Algebra.IsAlgebraic R A ↔ (⊤ : Subalgebra R A).IsAlgebraic := by
  delta Subalgebra.IsAlgebraic
  simp only [Algebra.isAlgebraic_def, Algebra.mem_top, forall_prop_of_true]

theorem isAlgebraic_iff_not_injective {x : A} :
    IsAlgebraic R x ↔ ¬Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) := by
  simp only [IsAlgebraic, injective_iff_map_eq_zero, not_forall, and_comm, exists_prop]

theorem Algebra.isAlgebraic_of_not_injective (h : ¬ Function.Injective (algebraMap R A)) :
    Algebra.IsAlgebraic R A where
  isAlgebraic a := isAlgebraic_iff_not_injective.mpr
    fun inj ↦ h <| by convert inj.comp C_injective; ext; simp

theorem Algebra.injective_of_transcendental (h : Algebra.Transcendental R A) :
    Function.Injective (algebraMap R A) := by
  rw [transcendental_iff_not_isAlgebraic] at h
  contrapose! h
  exact isAlgebraic_of_not_injective h

/-- An element `x` is transcendental over `R` if and only if the map `Polynomial.aeval x`
is injective. This is similar to `algebraicIndependent_iff_injective_aeval`. -/
theorem transcendental_iff_injective {x : A} :
    Transcendental R x ↔ Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) :=
  isAlgebraic_iff_not_injective.not_left

/-- An element `x` is transcendental over `R` if and only if the kernel of the ring homomorphism
`Polynomial.aeval x` is the zero ideal. This is similar to `algebraicIndependent_iff_ker_eq_bot`. -/
theorem transcendental_iff_ker_eq_bot {x : A} :
    Transcendental R x ↔ RingHom.ker (aeval (R := R) x) = ⊥ := by
  rw [transcendental_iff_injective, RingHom.injective_iff_ker_eq_bot]

end

section zero_ne_one

variable {R : Type u} {S : Type*} {A : Type v} [CommRing R]
variable [CommRing S] [Ring A] [Algebra R A] [Algebra R S] [Algebra S A]
variable [IsScalarTower R S A]

/-- An integral element of an algebra is algebraic. -/
theorem IsIntegral.isAlgebraic [Nontrivial R] {x : A} : IsIntegral R x → IsAlgebraic R x :=
  fun ⟨p, hp, hpx⟩ => ⟨p, hp.ne_zero, hpx⟩

instance Algebra.IsIntegral.isAlgebraic [Nontrivial R] [Algebra.IsIntegral R A] :
    Algebra.IsAlgebraic R A := ⟨fun a ↦ (Algebra.IsIntegral.isIntegral a).isAlgebraic⟩

theorem isAlgebraic_zero [Nontrivial R] : IsAlgebraic R (0 : A) :=
  ⟨_, X_ne_zero, aeval_X 0⟩

/-- An element of `R` is algebraic, when viewed as an element of the `R`-algebra `A`. -/
theorem isAlgebraic_algebraMap [Nontrivial R] (x : R) : IsAlgebraic R (algebraMap R A x) :=
  ⟨_, X_sub_C_ne_zero x, by rw [map_sub, aeval_X, aeval_C, sub_self]⟩

theorem isAlgebraic_one [Nontrivial R] : IsAlgebraic R (1 : A) := by
  rw [← map_one (algebraMap R A)]
  exact isAlgebraic_algebraMap 1

theorem isAlgebraic_nat [Nontrivial R] (n : ℕ) : IsAlgebraic R (n : A) := by
  rw [← map_natCast (_ : R →+* A) n]
  exact isAlgebraic_algebraMap (Nat.cast n)

theorem isAlgebraic_int [Nontrivial R] (n : ℤ) : IsAlgebraic R (n : A) := by
  rw [← map_intCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Int.cast n)

theorem isAlgebraic_rat (R : Type u) {A : Type v} [DivisionRing A] [Field R] [Algebra R A] (n : ℚ) :
    IsAlgebraic R (n : A) := by
  rw [← map_ratCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Rat.cast n)

theorem isAlgebraic_of_mem_rootSet {R : Type u} {A : Type v} [Field R] [Field A] [Algebra R A]
    {p : R[X]} {x : A} (hx : x ∈ p.rootSet A) : IsAlgebraic R x :=
  ⟨p, ne_zero_of_mem_rootSet hx, aeval_eq_zero_of_mem_rootSet hx⟩

open IsScalarTower

protected theorem IsAlgebraic.algebraMap {a : S} :
    IsAlgebraic R a → IsAlgebraic R (algebraMap S A a) := fun ⟨f, hf₁, hf₂⟩ =>
  ⟨f, hf₁, by rw [aeval_algebraMap_apply, hf₂, map_zero]⟩

section

variable {B : Type*} [Ring B] [Algebra R B]

/-- This is slightly more general than `IsAlgebraic.algebraMap` in that it
  allows noncommutative intermediate rings `A`. -/
protected theorem IsAlgebraic.algHom (f : A →ₐ[R] B) {a : A}
    (h : IsAlgebraic R a) : IsAlgebraic R (f a) :=
  let ⟨p, hp, ha⟩ := h
  ⟨p, hp, by rw [aeval_algHom, f.comp_apply, ha, map_zero]⟩

theorem isAlgebraic_algHom_iff (f : A →ₐ[R] B) (hf : Function.Injective f)
    {a : A} : IsAlgebraic R (f a) ↔ IsAlgebraic R a :=
  ⟨fun ⟨p, hp0, hp⟩ ↦ ⟨p, hp0, hf <| by rwa [map_zero, ← f.comp_apply, ← aeval_algHom]⟩,
    IsAlgebraic.algHom f⟩

section RingHom

omit [Algebra R S] [Algebra S A] [IsScalarTower R S A] [Algebra R B]
variable [Algebra S B] {FRS FAB : Type*}

section

variable [FunLike FRS R S] [RingHomClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB) {a : A}

theorem IsAlgebraic.ringHom_of_comp_eq (halg : IsAlgebraic R a)
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    IsAlgebraic S (g a) := by
  obtain ⟨p, h1, h2⟩ := halg
  refine ⟨p.map f, (Polynomial.map_ne_zero_iff hf).2 h1, ?_⟩
  change aeval ((g : A →+* B) a) _ = 0
  rw [← map_aeval_eq_aeval_map h, h2, map_zero]

theorem Transcendental.of_ringHom_of_comp_eq (H : Transcendental S (g a))
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Transcendental R a := fun halg ↦ H (halg.ringHom_of_comp_eq f g hf h)

theorem Algebra.IsAlgebraic.ringHom_of_comp_eq [Algebra.IsAlgebraic R A]
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic S B := by
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hg b
  exact (Algebra.IsAlgebraic.isAlgebraic a).ringHom_of_comp_eq f g hf h

theorem Algebra.Transcendental.of_ringHom_of_comp_eq [H : Algebra.Transcendental S B]
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental R A := by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg ↦ H (halg.ringHom_of_comp_eq f g hf hg h)

theorem IsAlgebraic.of_ringHom_of_comp_eq (halg : IsAlgebraic S (g a))
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    IsAlgebraic R a := by
  obtain ⟨p, h1, h2⟩ := halg
  obtain ⟨q, rfl⟩ := map_surjective f hf p
  refine ⟨q, fun h' ↦ by simp [h'] at h1, hg ?_⟩
  change aeval ((g : A →+* B) a) _ = 0 at h2
  change (g : A →+* B) _ = _
  rw [map_zero, map_aeval_eq_aeval_map h, h2]

theorem Transcendental.ringHom_of_comp_eq (H : Transcendental R a)
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Transcendental S (g a) := fun halg ↦ H (halg.of_ringHom_of_comp_eq f g hf hg h)

theorem Algebra.IsAlgebraic.of_ringHom_of_comp_eq [Algebra.IsAlgebraic S B]
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic R A :=
  ⟨fun a ↦ (Algebra.IsAlgebraic.isAlgebraic (g a)).of_ringHom_of_comp_eq f g hf hg h⟩

theorem Algebra.Transcendental.ringHom_of_comp_eq [H : Algebra.Transcendental R A]
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental S B := by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg ↦ H (halg.of_ringHom_of_comp_eq f g hf hg h)

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB)

theorem isAlgebraic_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) {a : A} :
    IsAlgebraic S (g a) ↔ IsAlgebraic R a :=
  ⟨fun H ↦ H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) hg h,
    fun H ↦ H.ringHom_of_comp_eq f g (EquivLike.injective f) h⟩

theorem transcendental_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) {a : A} :
    Transcendental S (g a) ↔ Transcendental R a :=
  not_congr (isAlgebraic_ringHom_iff_of_comp_eq f g hg h)

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [EquivLike FAB A B] [RingEquivClass FAB A B]
  (f : FRS) (g : FAB)

theorem Algebra.isAlgebraic_ringHom_iff_of_comp_eq
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic S B ↔ Algebra.IsAlgebraic R A :=
  ⟨fun H ↦ H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) (EquivLike.injective g) h,
    fun H ↦ H.ringHom_of_comp_eq f g (EquivLike.injective f) (EquivLike.surjective g) h⟩

theorem Algebra.transcendental_ringHom_iff_of_comp_eq
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental S B ↔ Algebra.Transcendental R A := by
  simp_rw [Algebra.transcendental_iff_not_isAlgebraic,
    Algebra.isAlgebraic_ringHom_iff_of_comp_eq f g h]

end

end RingHom

theorem Algebra.IsAlgebraic.of_injective (f : A →ₐ[R] B) (hf : Function.Injective f)
    [Algebra.IsAlgebraic R B] : Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (isAlgebraic_algHom_iff f hf).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩

/-- Transfer `Algebra.IsAlgebraic` across an `AlgEquiv`. -/
theorem AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B)
    [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic R B :=
  Algebra.IsAlgebraic.of_injective e.symm.toAlgHom e.symm.injective

theorem AlgEquiv.isAlgebraic_iff (e : A ≃ₐ[R] B) :
    Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic R B :=
  ⟨fun _ ↦ e.isAlgebraic, fun _ ↦ e.symm.isAlgebraic⟩

end

theorem isAlgebraic_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    IsAlgebraic R (algebraMap S A a) ↔ IsAlgebraic R a :=
  isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R S A) h

theorem transcendental_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    Transcendental R (algebraMap S A a) ↔ Transcendental R a := by
  simp_rw [Transcendental, isAlgebraic_algebraMap_iff h]

namespace Subalgebra

theorem isAlgebraic_iff_isAlgebraic_val {S : Subalgebra R A} {x : S} :
    _root_.IsAlgebraic R x ↔ _root_.IsAlgebraic R x.1 :=
  (isAlgebraic_algHom_iff S.val Subtype.val_injective).symm

theorem isAlgebraic_of_isAlgebraic_bot {x : S} (halg : _root_.IsAlgebraic (⊥ : Subalgebra R S) x) :
    _root_.IsAlgebraic R x :=
  halg.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id rfl

theorem isAlgebraic_bot_iff (h : Function.Injective (algebraMap R S)) {x : S} :
    _root_.IsAlgebraic (⊥ : Subalgebra R S) x ↔ _root_.IsAlgebraic R x :=
  isAlgebraic_ringHom_iff_of_comp_eq (Algebra.botEquivOfInjective h).symm (RingHom.id S)
    Function.injective_id (by rfl)

variable (R S) in
theorem algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left
    [Algebra.IsAlgebraic (⊥ : Subalgebra R S) S] : Algebra.IsAlgebraic R S :=
  Algebra.IsAlgebraic.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id (by ext; rfl)

theorem algebra_isAlgebraic_bot_left_iff (h : Function.Injective (algebraMap R S)) :
    Algebra.IsAlgebraic (⊥ : Subalgebra R S) S ↔ Algebra.IsAlgebraic R S := by
  simp_rw [Algebra.isAlgebraic_def, isAlgebraic_bot_iff h]

instance algebra_isAlgebraic_bot_right [Nontrivial R] :
    Algebra.IsAlgebraic R (⊥ : Subalgebra R S) :=
  ⟨by rintro ⟨_, x, rfl⟩; exact isAlgebraic_algebraMap _⟩

end Subalgebra

theorem IsAlgebraic.of_pow {r : A} {n : ℕ} (hn : 0 < n) (ht : IsAlgebraic R (r ^ n)) :
    IsAlgebraic R r := by
  obtain ⟨p, p_nonzero, hp⟩ := ht
  refine ⟨Polynomial.expand _ n p, ?_, ?_⟩
  · rwa [Polynomial.expand_ne_zero hn]
  · rwa [Polynomial.expand_aeval n p r]

theorem Transcendental.pow {r : A} (ht : Transcendental R r) {n : ℕ} (hn : 0 < n) :
    Transcendental R (r ^ n) := fun ht' ↦ ht <| ht'.of_pow hn

lemma IsAlgebraic.invOf {x : S} [Invertible x] (h : IsAlgebraic R x) : IsAlgebraic R (⅟ x) := by
  obtain ⟨p, hp, hp'⟩ := h
  refine ⟨p.reverse, by simpa using hp, ?_⟩
  rwa [Polynomial.aeval_def, Polynomial.eval₂_reverse_eq_zero_iff, ← Polynomial.aeval_def]

lemma IsAlgebraic.invOf_iff {x : S} [Invertible x] :
    IsAlgebraic R (⅟ x) ↔ IsAlgebraic R x :=
  ⟨IsAlgebraic.invOf, IsAlgebraic.invOf⟩

lemma IsAlgebraic.inv_iff {K} [Field K] [Algebra R K] {x : K} :
    IsAlgebraic R (x⁻¹) ↔ IsAlgebraic R x := by
  by_cases hx : x = 0
  · simp [hx]
  letI := invertibleOfNonzero hx
  exact IsAlgebraic.invOf_iff (R := R) (x := x)

alias ⟨_, IsAlgebraic.inv⟩ := IsAlgebraic.inv_iff

end zero_ne_one

section Field

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

/-- An element of an algebra over a field is algebraic if and only if it is integral. -/
theorem isAlgebraic_iff_isIntegral {x : A} : IsAlgebraic K x ↔ IsIntegral K x := by
  refine ⟨?_, IsIntegral.isAlgebraic⟩
  rintro ⟨p, hp, hpx⟩
  refine ⟨_, monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [← aeval_def, map_mul, hpx, zero_mul]

protected theorem Algebra.isAlgebraic_iff_isIntegral :
    Algebra.IsAlgebraic K A ↔ Algebra.IsIntegral K A := by
  rw [Algebra.isAlgebraic_def, Algebra.isIntegral_def,
      forall_congr' fun _ ↦ isAlgebraic_iff_isIntegral]

alias ⟨IsAlgebraic.isIntegral, _⟩ := isAlgebraic_iff_isIntegral

/-- This used to be an `alias` of `Algebra.isAlgebraic_iff_isIntegral` but that would make
`Algebra.IsAlgebraic K A` an explicit parameter instead of instance implicit. -/
protected instance Algebra.IsAlgebraic.isIntegral [Algebra.IsAlgebraic K A] :
    Algebra.IsIntegral K A := Algebra.isAlgebraic_iff_isIntegral.mp ‹_›

variable (K) in
theorem Algebra.IsAlgebraic.of_isIntegralClosure (R B C : Type*) [CommRing R] [Nontrivial R]
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra B C]
    [IsScalarTower R B C] [IsIntegralClosure B R C] : Algebra.IsAlgebraic R B :=
  have := IsIntegralClosure.isIntegral_algebra R (A := B) C
  inferInstance

/-- If `K` is a field, `r : A` and `f : K[X]`, then `Polynomial.aeval r f` is
transcendental over `K` if and only if `r` and `f` are both transcendental over `K`.
See also `Transcendental.aeval_of_transcendental` and `Transcendental.of_aeval`. -/
@[simp]
theorem transcendental_aeval_iff {r : A} {f : K[X]} :
    Transcendental K (Polynomial.aeval r f) ↔ Transcendental K r ∧ Transcendental K f := by
  refine ⟨fun h ↦ ⟨?_, h.of_aeval⟩, fun ⟨h1, h2⟩ ↦ h1.aeval_of_transcendental h2⟩
  rw [Transcendental] at h ⊢
  contrapose! h
  rw [isAlgebraic_iff_isIntegral] at h ⊢
  exact .of_mem_of_fg _ h.fg_adjoin_singleton _ (aeval_mem_adjoin_singleton _ _)

end Field

section

variable {K L R S A : Type*}

section Ring

section CommRing

variable [CommRing R] [CommRing S] [Ring A]
variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- If `x` is algebraic over `R`, then `x` is algebraic over `S` when `S` is an extension of `R`,
  and the map from `R` to `S` is injective. -/
theorem IsAlgebraic.extendScalars (hinj : Function.Injective (algebraMap R S)) {x : A}
    (A_alg : IsAlgebraic R x) : IsAlgebraic S x :=
  let ⟨p, hp₁, hp₂⟩ := A_alg
  ⟨p.map (algebraMap _ _), by
    rwa [Ne, ← degree_eq_bot, degree_map_eq_of_injective hinj, degree_eq_bot], by simpa⟩

@[deprecated (since := "2024-11-18")]
alias IsAlgebraic.tower_top_of_injective := IsAlgebraic.extendScalars

/-- A special case of `IsAlgebraic.extendScalars`. This is extracted as a theorem
  because in some cases `IsAlgebraic.extendScalars` will just runs out of memory. -/
theorem IsAlgebraic.tower_top_of_subalgebra_le
    {A B : Subalgebra R S} (hle : A ≤ B) {x : S}
    (h : IsAlgebraic A x) : IsAlgebraic B x := by
  letI : Algebra A B := (Subalgebra.inclusion hle).toAlgebra
  haveI : IsScalarTower A B S := .of_algebraMap_eq fun _ ↦ rfl
  exact h.extendScalars (Subalgebra.inclusion_injective hle)

/-- If `x` is transcendental over `S`, then `x` is transcendental over `R` when `S` is an extension
  of `R`, and the map from `R` to `S` is injective. -/
theorem Transcendental.restrictScalars (hinj : Function.Injective (algebraMap R S)) {x : A}
    (h : Transcendental S x) : Transcendental R x := fun H ↦ h (H.extendScalars hinj)

@[deprecated (since := "2024-11-18")]
alias Transcendental.of_tower_top_of_injective := Transcendental.restrictScalars

/-- A special case of `Transcendental.restrictScalars`. This is extracted as a theorem
  because in some cases `Transcendental.restrictScalars` will just runs out of memory. -/
theorem Transcendental.of_tower_top_of_subalgebra_le
    {A B : Subalgebra R S} (hle : A ≤ B) {x : S}
    (h : Transcendental B x) : Transcendental A x :=
  fun H ↦ h (H.tower_top_of_subalgebra_le hle)

/-- If A is an algebraic algebra over R, then A is algebraic over S when S is an extension of R,
  and the map from `R` to `S` is injective. -/
theorem Algebra.IsAlgebraic.extendScalars (hinj : Function.Injective (algebraMap R S))
    [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic S A :=
  ⟨fun _ ↦ _root_.IsAlgebraic.extendScalars hinj (Algebra.IsAlgebraic.isAlgebraic _)⟩

@[deprecated (since := "2024-11-18")]
alias Algebra.IsAlgebraic.tower_top_of_injective := Algebra.IsAlgebraic.extendScalars

theorem Algebra.IsAlgebraic.tower_bot_of_injective [Algebra.IsAlgebraic R A]
    (hinj : Function.Injective (algebraMap S A)) :
    Algebra.IsAlgebraic R S where
  isAlgebraic x := by
    simpa [isAlgebraic_algebraMap_iff hinj] using isAlgebraic (R := R) (A := A) (algebraMap _ _ x)

end CommRing

section Field

variable [Field K] [Field L] [Ring A]
variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
variable (L)

/-- If `x` is algebraic over `K`, then `x` is algebraic over `L` when `L` is an extension of `K` -/
@[stacks 09GF "part one"]
theorem IsAlgebraic.tower_top {x : A} (A_alg : IsAlgebraic K x) :
    IsAlgebraic L x :=
  A_alg.extendScalars (algebraMap K L).injective

variable {L} (K) in
/-- If `x` is transcendental over `L`, then `x` is transcendental over `K` when
  `L` is an extension of `K` -/
theorem Transcendental.of_tower_top {x : A} (h : Transcendental L x) :
    Transcendental K x := fun H ↦ h (H.tower_top L)

/-- If A is an algebraic algebra over K, then A is algebraic over L when L is an extension of K -/
@[stacks 09GF "part two"]
theorem Algebra.IsAlgebraic.tower_top [Algebra.IsAlgebraic K A] : Algebra.IsAlgebraic L A :=
  Algebra.IsAlgebraic.extendScalars (algebraMap K L).injective

variable (K)

theorem IsAlgebraic.of_finite (e : A) [FiniteDimensional K A] : IsAlgebraic K e :=
  (IsIntegral.of_finite K e).isAlgebraic

variable (A)

/-- A field extension is algebraic if it is finite. -/
@[stacks 09GG "first part"]
instance Algebra.IsAlgebraic.of_finite [FiniteDimensional K A] : Algebra.IsAlgebraic K A :=
  (IsIntegral.of_finite K A).isAlgebraic

theorem Algebra.IsAlgebraic.tower_bot (K L A : Type*) [CommRing K] [Field L] [Ring A]
    [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
    [Nontrivial A] [Algebra.IsAlgebraic K A] :
    Algebra.IsAlgebraic K L :=
  tower_bot_of_injective (algebraMap L A).injective

end Field

end Ring

section CommRing

variable [Field K] [Field L] [Ring A]
variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

/-- If L is an algebraic field extension of K and A is an algebraic algebra over L,
then A is algebraic over K. -/
@[stacks 09GJ]
protected theorem Algebra.IsAlgebraic.trans
    [L_alg : Algebra.IsAlgebraic K L] [A_alg : Algebra.IsAlgebraic L A] :
    Algebra.IsAlgebraic K A := by
  rw [Algebra.isAlgebraic_iff_isIntegral] at L_alg A_alg ⊢
  exact Algebra.IsIntegral.trans L

end CommRing

section NoZeroSMulDivisors

namespace Algebra.IsAlgebraic

variable [CommRing K] [Field L]
variable [Algebra K L]

theorem algHom_bijective [NoZeroSMulDivisors K L] [Algebra.IsAlgebraic K L] (f : L →ₐ[K] L) :
    Function.Bijective f := by
  refine ⟨f.injective, fun b ↦ ?_⟩
  obtain ⟨p, hp, he⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) b
  let f' : p.rootSet L → p.rootSet L := (rootSet_maps_to' (fun x ↦ x) f).restrict f _ _
  have : f'.Surjective := Finite.injective_iff_surjective.1
    fun _ _ h ↦ Subtype.eq <| f.injective <| Subtype.ext_iff.1 h
  obtain ⟨a, ha⟩ := this ⟨b, mem_rootSet.2 ⟨hp, he⟩⟩
  exact ⟨a, Subtype.ext_iff.1 ha⟩

theorem algHom_bijective₂ [NoZeroSMulDivisors K L] [Field R] [Algebra K R]
    [Algebra.IsAlgebraic K L] (f : L →ₐ[K] R) (g : R →ₐ[K] L) :
    Function.Bijective f ∧ Function.Bijective g :=
  (g.injective.bijective₂_of_surjective f.injective (algHom_bijective <| g.comp f).2).symm

theorem bijective_of_isScalarTower [NoZeroSMulDivisors K L] [Algebra.IsAlgebraic K L]
    [Field R] [Algebra K R] [Algebra L R] [IsScalarTower K L R] (f : R →ₐ[K] L) :
    Function.Bijective f :=
  (algHom_bijective₂ (IsScalarTower.toAlgHom K L R) f).2

theorem bijective_of_isScalarTower' [Field R] [Algebra K R]
    [NoZeroSMulDivisors K R]
    [Algebra.IsAlgebraic K R] [Algebra L R] [IsScalarTower K L R] (f : R →ₐ[K] L) :
    Function.Bijective f :=
  (algHom_bijective₂ f (IsScalarTower.toAlgHom K L R)).1

variable (K L)

/-- Bijection between algebra equivalences and algebra homomorphisms -/
@[simps]
noncomputable def algEquivEquivAlgHom [NoZeroSMulDivisors K L] [Algebra.IsAlgebraic K L] :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) where
  toFun ϕ := ϕ.toAlgHom
  invFun ϕ := AlgEquiv.ofBijective ϕ (algHom_bijective ϕ)
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := rfl

end Algebra.IsAlgebraic

end NoZeroSMulDivisors

section Field

variable [Field K] [Field L]
variable [Algebra K L]

theorem AlgHom.bijective [FiniteDimensional K L] (ϕ : L →ₐ[K] L) : Function.Bijective ϕ :=
  (Algebra.IsAlgebraic.of_finite K L).algHom_bijective ϕ

variable (K L)

/-- Bijection between algebra equivalences and algebra homomorphisms -/
noncomputable abbrev algEquivEquivAlgHom [FiniteDimensional K L] :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) :=
  Algebra.IsAlgebraic.algEquivEquivAlgHom K L

end Field

end

section

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]

theorem IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero
    {s : S} (hRs : IsAlgebraic R s) (hs : s ∈ nonZeroDivisors S) :
    ∃ q : R[X], q.coeff 0 ≠ 0 ∧ aeval s q = 0 := by
  obtain ⟨p, hp0, hp⟩ := hRs
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  simp only [C_0, sub_zero, X_pow_mul, X_dvd_iff] at hpq hq
  rw [hpq, map_mul, aeval_X_pow] at hp
  exact ⟨q, hq, (nonZeroDivisors S).pow_mem hs (rootMultiplicity 0 p) (aeval s q) hp⟩

theorem IsAlgebraic.exists_nonzero_eq_adjoin_mul
    {s : S} (hRs : IsAlgebraic R s) (hs : s ∈ nonZeroDivisors S) :
    ∃ᵉ (t ∈ Algebra.adjoin R {s}) (r ≠ (0 : R)), s * t = algebraMap R S r := by
  obtain ⟨q, hq0, hq⟩ := hRs.exists_nonzero_coeff_and_aeval_eq_zero hs
  have ⟨p, hp⟩ := X_dvd_sub_C (p := q)
  refine ⟨aeval s p, aeval_mem_adjoin_singleton _ _, _, neg_ne_zero.mpr hq0, ?_⟩
  apply_fun aeval s at hp
  rwa [map_sub, hq, zero_sub, map_mul, aeval_X, aeval_C, ← map_neg, eq_comm] at hp

theorem IsAlgebraic.exists_nonzero_dvd
    {s : S} (hRs : IsAlgebraic R s) (hs : s ∈ nonZeroDivisors S) :
    ∃ r : R, r ≠ 0 ∧ s ∣ algebraMap R S r := by
  obtain ⟨q, hq0, hq⟩ := hRs.exists_nonzero_coeff_and_aeval_eq_zero hs
  have key := map_dvd (aeval s) (X_dvd_sub_C (p := q))
  rw [map_sub, hq, zero_sub, dvd_neg, aeval_X, aeval_C] at key
  exact ⟨q.coeff 0, hq0, key⟩

/-- A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `b` is algebraic over `R`. -/
theorem IsAlgebraic.exists_smul_eq_mul
    (a : S) {b : S} (hRb : IsAlgebraic R b) (hb : b ∈ nonZeroDivisors S) :
    ∃ᵉ (c : S) (d ≠ (0 : R)), d • a = b * c :=
  have ⟨r, hr, s, h⟩ := hRb.exists_nonzero_dvd hb
  ⟨s * a, r, hr, by rw [Algebra.smul_def, h, mul_assoc]⟩

variable (R)

/-- A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `b` is algebraic over `R`. -/
theorem Algebra.IsAlgebraic.exists_smul_eq_mul [IsDomain S] [Algebra.IsAlgebraic R S]
    (a : S) {b : S} (hb : b ≠ 0) :
    ∃ᵉ (c : S) (d ≠ (0 : R)), d • a = b * c :=
  (isAlgebraic b).exists_smul_eq_mul a (mem_nonZeroDivisors_iff_ne_zero.mpr hb)

end

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable {z : S}

namespace IsAlgebraic

theorem exists_integral_multiple (hz : IsAlgebraic R z)
    (inj : ∀ x, algebraMap R S x = 0 → x = 0) :
    ∃ᵉ (x : integralClosure R S) (y ≠ (0 : R)), z * algebraMap R S y = x := by
  rcases hz with ⟨p, p_ne_zero, px⟩
  set a := p.leadingCoeff
  have a_ne_zero : a ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.mp p_ne_zero
  have x_integral : IsIntegral R (z * algebraMap R S a) :=
    ⟨p.integralNormalization, monic_integralNormalization p_ne_zero,
      integralNormalization_aeval_eq_zero px inj⟩
  exact ⟨⟨_, x_integral⟩, a, a_ne_zero, rfl⟩

@[deprecated (since := "2024-11-30")]
alias _root_.exists_integral_multiple := exists_integral_multiple

theorem exists_smul_integral (hz : IsAlgebraic R z)
    (inj : Function.Injective (algebraMap R S)) :
    ∃ y ≠ (0 : R), IsIntegral R (y • z) := by
  simp_rw [Algebra.smul_def, Algebra.commutes]
  obtain ⟨⟨_, int⟩, y, hy, rfl⟩ := exists_integral_multiple hz fun _ ↦ (map_eq_zero_iff _ inj).mp
  exact ⟨y, hy, int⟩

theorem of_smul_integral {y : R} (hy : ¬ IsNilpotent y)
    (h : IsIntegral R (y • z)) : IsAlgebraic R z := by
  have ⟨p, monic, eval0⟩ := h
  refine ⟨p.comp (C y * X), fun h ↦ ?_, by simpa [aeval_comp, Algebra.smul_def] using eval0⟩
  apply_fun (coeff · p.natDegree) at h
  have hy0 : y ≠ 0 := by rintro rfl; exact hy .zero
  rw [coeff_zero, ← mul_one p.natDegree, ← natDegree_C_mul_X y hy0,
    coeff_comp_degree_mul_degree, monic, one_mul, leadingCoeff_C_mul_X] at h
  · exact hy ⟨_, h⟩
  · rw [natDegree_C_mul_X _ hy0]; rintro ⟨⟩

theorem of_smul {y : R} (hy : y ∈ nonZeroDivisors R)
    (h : IsAlgebraic R (y • z)) : IsAlgebraic R z := by
  sorry -- need coefficients of p.comp (C y * X)

theorem of_mul [NoZeroDivisors R] {y : S} (hy : y ∈ nonZeroDivisors S)
    (alg_y : IsAlgebraic R y) (alg_yz : IsAlgebraic R (y * z)) : IsAlgebraic R z := by
  have ⟨t, ht, r, hr, eq⟩ := alg_y.exists_nonzero_eq_adjoin_mul hy
  sorry

theorem iff_exists_smul_integral [IsReduced R] (inj : Function.Injective (algebraMap R S)) :
    IsAlgebraic R z ↔ ∃ y ≠ (0 : R), IsIntegral R (y • z) :=
  ⟨(exists_smul_integral · inj), fun ⟨_, hy, int⟩ ↦
    of_smul_integral (by rwa [isNilpotent_iff_eq_zero]) int⟩

theorem trans_isIntegral [IsReduced R] [NoZeroDivisors S] [int : Algebra.IsIntegral R S] {a : A}
    (inj : Function.Injective (algebraMap S A)) (h : IsAlgebraic S a) :
    IsAlgebraic R a := by
  have ⟨s, hs, int_s⟩ := h.exists_smul_integral inj
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R S
    exact (is_transcendental_of_subsingleton _ _ h).elim
  have ⟨r, hr, _, e⟩ := (int.1 s).isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hs)
  refine .of_smul_integral (y := r) (by rwa [isNilpotent_iff_eq_zero]) ?_
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R S,
    e, ← Algebra.smul_def, mul_comm, mul_smul]
  exact isIntegral_trans _ (int_s.smul _)

protected theorem trans [NoZeroDivisors R] [NoZeroDivisors S]
    (hRS : Function.Injective (algebraMap R S)) (hSA : Function.Injective (algebraMap S A))
    [alg : Algebra.IsAlgebraic R S] {a : A} (h : IsAlgebraic S a) : IsAlgebraic R a := by
  have ⟨p, hp, eval0⟩ := h
  have := (alg.1 0).nontrivial
  choose r hr int using fun s ↦ (alg.1 s).exists_smul_integral hRS
  let r0 := ∏ n ∈ p.support, r (coeff p n)
  let p := (r0 • p).toSubring (integralClosure R S).toSubring fun s hs ↦ by
    obtain ⟨n, hn, rfl⟩ := mem_coeffs_iff.mp hs
    replace hn := support_smul _ _ hn
    classical
    simp_rw [coeff_smul, r0, ← Finset.prod_erase_mul _ _ hn, mul_smul]
    exact (int _).smul _
  have : IsAlgebraic (integralClosure R S) a := by
    refine ⟨p, ?_, ?_⟩
    · have := NoZeroSMulDivisors.of_algebraMap_injective hRS
      rw [← Polynomial.map_ne_zero_iff (f := Subring.subtype _) Subtype.val_injective,
        map_toSubring, smul_ne_zero_iff, Finset.prod_ne_zero_iff]
      exact ⟨fun _ _ ↦ hr _, hp⟩
    rw [← eval_map_algebraMap, Subalgebra.algebraMap_eq, ← map_map, ← Subalgebra.toSubring_subtype,
      map_toSubring, eval_map_algebraMap, ← AlgHom.restrictScalars_apply R,
      map_smul, AlgHom.restrictScalars_apply, eval0, smul_zero]
  exact trans_isIntegral (by exact hSA.comp Subtype.val_injective) this

variable {a b : S} (ha : IsAlgebraic R a) (hb : IsAlgebraic R b)
include ha

protected lemma neg : IsAlgebraic R (-a) :=
  have ⟨p, h, eval0⟩ := ha
  ⟨algEquivAevalNegX p, EmbeddingLike.map_ne_zero_iff.mpr h, by simpa [← comp_eq_aeval, aeval_comp]⟩

include hb

protected lemma mul [NoZeroDivisors R] : IsAlgebraic R (a * b) := by
  refine (em _).by_cases (fun h ↦ ?_) fun h ↦ (Algebra.isAlgebraic_of_not_injective h).1 _
  have ⟨ra, a0, int_a⟩ := ha.exists_smul_integral h
  have ⟨rb, b0, int_b⟩ := hb.exists_smul_integral h
  refine (IsAlgebraic.iff_exists_smul_integral h).mpr ⟨_, mul_ne_zero a0 b0, ?_⟩
  simp_rw [Algebra.smul_def, map_mul, mul_mul_mul_comm, ← Algebra.smul_def]
  exact int_a.mul int_b

protected lemma add [NoZeroDivisors R] : IsAlgebraic R (a + b) := by
  refine (em _).by_cases (fun h ↦ ?_) fun h ↦ (Algebra.isAlgebraic_of_not_injective h).1 _
  have ⟨ra, a0, int_a⟩ := ha.exists_smul_integral h
  have ⟨rb, b0, int_b⟩ := hb.exists_smul_integral h
  refine (IsAlgebraic.iff_exists_smul_integral h).mpr ⟨_, mul_ne_zero b0 a0, ?_⟩
  rw [smul_add, mul_smul, mul_comm, mul_smul]
  exact (int_a.smul _).add (int_b.smul _)

protected lemma sub [NoZeroDivisors R] : IsAlgebraic R (a - b) :=
  sub_eq_add_neg a b ▸ ha.add hb.neg

omit hb
protected lemma pow [NoZeroDivisors R] (n : ℕ) : IsAlgebraic R (a ^ n) :=
  have := ha.nontrivial
  n.rec (pow_zero a ▸ isAlgebraic_one) fun _ h ↦ pow_succ a _ ▸ h.mul ha

/-- A version of `IsAlgebraic.smul` that only assumes the scalar is not a zero divisor
rather than the whole base ring has no zero divisors. -/
protected lemma smul' {r : R} (hr : r ∈ nonZeroDivisors R) : IsAlgebraic R (r • a) := by
  have ⟨p, hp, eval0⟩ := ha
  refine ⟨p.scaleRoots r, fun h ↦ hp <| ext fun n ↦ ?_,
    Algebra.smul_def r a ▸ scaleRoots_aeval_eq_zero eval0⟩
  apply_fun (coeff · n) at h
  rwa [coeff_scaleRoots, coeff_zero, mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hr _)] at h

lemma nsmul [NoZeroSMulDivisors ℕ R] (n : ℕ) : IsAlgebraic R (n • a) := by
  sorry

lemma zsmul [NoZeroSMulDivisors ℤ R] (n : ℤ) : IsAlgebraic R (n • a) := by
  sorry

protected lemma smul [NoZeroDivisors R] (r : R) : IsAlgebraic R (r • a) :=
  have := ha.nontrivial
  Algebra.smul_def r a ▸ (isAlgebraic_algebraMap r).mul ha

end IsAlgebraic

/-- Transitivity of algebraicity for algebras over domains. -/
theorem Algebra.IsAlgebraic.trans' [NoZeroDivisors R] [NoZeroDivisors S]
    (hRS : Function.Injective (algebraMap R S)) (hSA : Function.Injective (algebraMap S A))
    [Algebra.IsAlgebraic R S] [alg : Algebra.IsAlgebraic S A] : Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ .trans hRS hSA <| alg.1 _⟩

variable (R S)
def Subalgebra.algebraicClosure [IsDomain R] : Subalgebra R S where
  carrier := {s | _root_.IsAlgebraic R s}
  mul_mem' ha hb := ha.mul hb
  add_mem' ha hb := ha.add hb
  algebraMap_mem' := isAlgebraic_algebraMap

lemma integralClosure_le_algebraicClosure [IsDomain R] :
    integralClosure R S ≤ Subalgebra.algebraicClosure R S :=
  fun _ ↦ IsIntegral.isAlgebraic

instance [IsDomain R] : Algebra.IsAlgebraic R (Subalgebra.algebraicClosure R S) :=
  (Subalgebra.isAlgebraic_iff _).mp fun _ ↦ id

namespace Transcendental

variable {R S} {a : A} (ha : Transcendental R a)
include ha

lemma tower_top_of_isIntegral [IsReduced R] [NoZeroDivisors S] [Algebra.IsIntegral R S]
    (inj : Function.Injective (algebraMap S A)) : Transcendental S a := by
  contrapose ha
  rw [Transcendental, not_not] at ha ⊢
  exact ha.trans_isIntegral inj

lemma tower_top [NoZeroDivisors R] [NoZeroDivisors S]
    (hRS : Function.Injective (algebraMap R S)) (hSA : Function.Injective (algebraMap S A))
    [Algebra.IsAlgebraic R S] : Transcendental S a := by
  contrapose ha
  rw [Transcendental, not_not] at ha ⊢
  exact ha.trans hRS hSA

protected lemma integralClosure [IsReduced R] [NoZeroDivisors A] :
    Transcendental (integralClosure R A) a :=
  ha.tower_top_of_isIntegral Subtype.val_injective

protected lemma algebraicClosure [IsDomain R] [NoZeroDivisors A]
    (hRS : Function.Injective (algebraMap R A)) :
    Transcendental (Subalgebra.algebraicClosure R A) a :=
  ha.tower_top (fun _ _ eq ↦ hRS <| congr($eq.1)) Subtype.val_injective

end Transcendental

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : Subalgebra K L)

theorem inv_eq_of_aeval_divX_ne_zero {x : L} {p : K[X]} (aeval_ne : aeval x (divX p) ≠ 0) :
    x⁻¹ = aeval x (divX p) / (aeval x p - algebraMap _ _ (p.coeff 0)) := by
  rw [inv_eq_iff_eq_inv, inv_div, eq_comm, div_eq_iff, sub_eq_iff_eq_add, mul_comm]
  conv_lhs => rw [← divX_mul_X_add p]
  · rw [map_add, map_mul, aeval_X, aeval_C]
  · exact aeval_ne

theorem inv_eq_of_root_of_coeff_zero_ne_zero {x : L} {p : K[X]} (aeval_eq : aeval x p = 0)
    (coeff_zero_ne : p.coeff 0 ≠ 0) : x⁻¹ = -(aeval x (divX p) / algebraMap _ _ (p.coeff 0)) := by
  convert inv_eq_of_aeval_divX_ne_zero (p := p) (L := L)
    (mt (fun h => (algebraMap K L).injective ?_) coeff_zero_ne) using 1
  · rw [aeval_eq, zero_sub, div_neg]
  rw [RingHom.map_zero]
  convert aeval_eq
  conv_rhs => rw [← divX_mul_X_add p]
  rw [map_add, map_mul, h, zero_mul, zero_add, aeval_C]

theorem Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero {x : A} {p : K[X]}
    (aeval_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 ≠ 0) : (x⁻¹ : L) ∈ A := by
  suffices (x⁻¹ : L) = (-p.coeff 0)⁻¹ • aeval x (divX p) by
    rw [this]
    exact A.smul_mem (aeval x _).2 _
  have : aeval (x : L) p = 0 := by rw [Subalgebra.aeval_coe, aeval_eq, Subalgebra.coe_zero]
  -- Porting note: this was a long sequence of `rw`.
  rw [inv_eq_of_root_of_coeff_zero_ne_zero this coeff_zero_ne, div_eq_inv_mul, Algebra.smul_def]
  simp only [aeval_coe, Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, coe_toSubsemiring,
    coe_algebraMap]
  rw [map_inv₀, map_neg, inv_neg, neg_mul]

theorem Subalgebra.inv_mem_of_algebraic {x : A} (hx : _root_.IsAlgebraic K (x : L)) :
    (x⁻¹ : L) ∈ A := by
  obtain ⟨p, ne_zero, aeval_eq⟩ := hx
  rw [Subalgebra.aeval_coe, Subalgebra.coe_eq_zero] at aeval_eq
  revert ne_zero aeval_eq
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a hp ha _ih _ne_zero aeval_eq
    refine A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq ?_
    rwa [coeff_add, hp, zero_add, coeff_C, if_pos rfl]
  · intro p hp ih _ne_zero aeval_eq
    rw [map_mul, aeval_X, mul_eq_zero] at aeval_eq
    cases' aeval_eq with aeval_eq x_eq
    · exact ih hp aeval_eq
    · rw [x_eq, Subalgebra.coe_zero, inv_zero]
      exact A.zero_mem

/-- In an algebraic extension L/K, an intermediate subalgebra is a field. -/
@[stacks 0BID]
theorem Subalgebra.isField_of_algebraic [Algebra.IsAlgebraic K L] : IsField A :=
  { show Nontrivial A by infer_instance, Subalgebra.toCommRing A with
    mul_inv_cancel := fun {a} ha =>
      ⟨⟨a⁻¹, A.inv_mem_of_algebraic (Algebra.IsAlgebraic.isAlgebraic (a : L))⟩,
        Subtype.ext (mul_inv_cancel₀ (mt (Subalgebra.coe_eq_zero _).mp ha))⟩ }

end Field

section Pi

variable (R' : Type u) (S' : Type v) (T' : Type w)

/-- This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details. -/
def Polynomial.hasSMulPi [Semiring R'] [SMul R' S'] : SMul R'[X] (R' → S') :=
  ⟨fun p f x => eval x p • f x⟩

/-- This is not an instance as it forms a diamond with `Pi.instSMul`.

See the `instance_diamonds` test for details. -/
noncomputable def Polynomial.hasSMulPi' [CommSemiring R'] [Semiring S'] [Algebra R' S']
    [SMul S' T'] : SMul R'[X] (S' → T') :=
  ⟨fun p f x => aeval x p • f x⟩

attribute [local instance] Polynomial.hasSMulPi Polynomial.hasSMulPi'

@[simp]
theorem polynomial_smul_apply [Semiring R'] [SMul R' S'] (p : R'[X]) (f : R' → S') (x : R') :
    (p • f) x = eval x p • f x :=
  rfl

@[simp]
theorem polynomial_smul_apply' [CommSemiring R'] [Semiring S'] [Algebra R' S'] [SMul S' T']
    (p : R'[X]) (f : S' → T') (x : S') : (p • f) x = aeval x p • f x :=
  rfl

variable [CommSemiring R'] [CommSemiring S'] [CommSemiring T'] [Algebra R' S'] [Algebra S' T']

-- Porting note: the proofs in this definition used `funext` in term-mode, but I was not able
-- to get them to work anymore.
/-- This is not an instance for the same reasons as `Polynomial.hasSMulPi'`. -/
noncomputable def Polynomial.algebraPi : Algebra R'[X] (S' → T') :=
  { Polynomial.hasSMulPi' R' S' T' with
    toFun := fun p z => algebraMap S' T' (aeval z p)
    map_one' := by
      funext z
      simp only [Polynomial.aeval_one, Pi.one_apply, map_one]
    map_mul' := fun f g => by
      funext z
      simp only [Pi.mul_apply, map_mul]
    map_zero' := by
      funext z
      simp only [Polynomial.aeval_zero, Pi.zero_apply, map_zero]
    map_add' := fun f g => by
      funext z
      simp only [Polynomial.aeval_add, Pi.add_apply, map_add]
    commutes' := fun p f => by
      funext z
      exact mul_comm _ _
    smul_def' := fun p f => by
      funext z
      simp only [polynomial_smul_apply', Algebra.algebraMap_eq_smul_one, RingHom.coe_mk,
        MonoidHom.coe_mk, OneHom.coe_mk, Pi.mul_apply, Algebra.smul_mul_assoc, one_mul] }

attribute [local instance] Polynomial.algebraPi

@[simp]
theorem Polynomial.algebraMap_pi_eq_aeval :
    (algebraMap R'[X] (S' → T') : R'[X] → S' → T') = fun p z => algebraMap _ _ (aeval z p) :=
  rfl

@[simp]
theorem Polynomial.algebraMap_pi_self_eq_eval :
    (algebraMap R'[X] (R' → R') : R'[X] → R' → R') = fun p z => eval z p :=
  rfl

end Pi

namespace MvPolynomial

variable {σ : Type*} (R : Type*) [CommRing R]

-- TODO: move to suitable place
private theorem rename_polynomial_aeval_X
    {σ τ R : Type*} [CommSemiring R] (f : σ → τ) (i : σ) (p : R[X]) :
    rename f (Polynomial.aeval (X i) p) = Polynomial.aeval (X (f i) : MvPolynomial τ R) p := by
  rw [← AlgHom.comp_apply]
  congr 1; ext1; simp

theorem transcendental_supported_polynomial_aeval_X {i : σ} {s : Set σ} (h : i ∉ s)
    {f : R[X]} (hf : Transcendental R f) :
    Transcendental (supported R s) (Polynomial.aeval (X i : MvPolynomial σ R) f) := by
  rw [transcendental_iff_injective] at hf ⊢
  let g := MvPolynomial.mapAlgHom (R := R) (σ := s) (Polynomial.aeval (R := R) f)
  replace hf : Function.Injective g := MvPolynomial.map_injective _ hf
  let u := (Subalgebra.val _).comp
    ((optionEquivRight R s).symm |>.trans
      (renameEquiv R (Set.subtypeInsertEquivOption h).symm) |>.trans
      (supportedEquivMvPolynomial _).symm).toAlgHom |>.comp
    g |>.comp
    ((optionEquivLeft R s).symm.trans (optionEquivRight R s)).toAlgHom
  let v := ((Polynomial.aeval (R := supported R s)
    (Polynomial.aeval (X i : MvPolynomial σ R) f)).restrictScalars R).comp
      (Polynomial.mapAlgEquiv (supportedEquivMvPolynomial s).symm).toAlgHom
  replace hf : Function.Injective u := by
    simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, Subalgebra.coe_val,
      AlgHom.coe_coe, AlgEquiv.coe_trans, Function.comp_assoc, u]
    apply Subtype.val_injective.comp
    simp only [EquivLike.comp_injective]
    apply hf.comp
    simp only [EquivLike.comp_injective, EquivLike.injective]
  have h1 : Polynomial.aeval (X i : MvPolynomial σ R) = ((Subalgebra.val _).comp
      (supportedEquivMvPolynomial _).symm.toAlgHom |>.comp
      (Polynomial.aeval (X ⟨i, s.mem_insert i⟩ : MvPolynomial ↑(insert i s) R))) := by
    ext1; simp
  have h2 : u = v := by
    simp only [u, v, g]
    ext1
    · ext1
      simp [Set.subtypeInsertEquivOption, Subalgebra.algebraMap_eq]
    · simp [Set.subtypeInsertEquivOption, rename_polynomial_aeval_X, h1]
  simpa only [h2, v, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_comp, AlgHom.coe_coe,
    EquivLike.injective_comp, AlgHom.coe_restrictScalars'] using hf

theorem transcendental_polynomial_aeval_X (i : σ) {f : R[X]} (hf : Transcendental R f) :
    Transcendental R (Polynomial.aeval (X i : MvPolynomial σ R) f) := by
  have := transcendental_supported_polynomial_aeval_X R (Set.not_mem_empty i) hf
  let g := (Algebra.botEquivOfInjective (MvPolynomial.C_injective σ R)).symm.trans
    (Subalgebra.equivOfEq _ _ supported_empty).symm
  rwa [Transcendental, ← isAlgebraic_ringHom_iff_of_comp_eq g (RingHom.id (MvPolynomial σ R))
    Function.injective_id (by ext1; rfl), RingHom.id_apply, ← Transcendental]

theorem transcendental_polynomial_aeval_X_iff (i : σ) {f : R[X]} :
    Transcendental R (Polynomial.aeval (X i : MvPolynomial σ R) f) ↔ Transcendental R f := by
  refine ⟨?_, transcendental_polynomial_aeval_X R i⟩
  simp_rw [Transcendental, not_imp_not]
  exact fun h ↦ h.algHom _

theorem transcendental_supported_polynomial_aeval_X_iff
    [Nontrivial R] {i : σ} {s : Set σ} {f : R[X]} :
    Transcendental (supported R s) (Polynomial.aeval (X i : MvPolynomial σ R) f) ↔
    i ∉ s ∧ Transcendental R f := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h, hf⟩ ↦ transcendental_supported_polynomial_aeval_X R h hf⟩
  · rw [Transcendental] at h
    contrapose! h
    refine isAlgebraic_algebraMap (⟨Polynomial.aeval (X i) f, ?_⟩ : supported R s)
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_image_of_mem _ h))
      (Polynomial.aeval_mem_adjoin_singleton _ _)
  · rw [← transcendental_polynomial_aeval_X_iff R i]
    refine h.restrictScalars fun _ _ heq ↦ MvPolynomial.C_injective σ R ?_
    simp_rw [← MvPolynomial.algebraMap_eq]
    exact congr($(heq).1)

theorem transcendental_supported_X {i : σ} {s : Set σ} (h : i ∉ s) :
    Transcendental (supported R s) (X i : MvPolynomial σ R) := by
  simpa using transcendental_supported_polynomial_aeval_X R h (Polynomial.transcendental_X R)

theorem transcendental_X (i : σ) : Transcendental R (X i : MvPolynomial σ R) := by
  simpa using transcendental_polynomial_aeval_X R i (Polynomial.transcendental_X R)

theorem transcendental_supported_X_iff [Nontrivial R] {i : σ} {s : Set σ} :
    Transcendental (supported R s) (X i : MvPolynomial σ R) ↔ i ∉ s := by
  simpa [Polynomial.transcendental_X] using
    transcendental_supported_polynomial_aeval_X_iff R (i := i) (s := s) (f := Polynomial.X)

end MvPolynomial
