module

public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.NatCastEqZeroOfNotDvd

@[expose] public section

namespace Formalism.MainNotions.N.Ln34

open Finset

section GradNPfVal

variable {L O : Type*} [Field L] [CommRing O] (v : AddValuation L (WithTop ℚ)) (ι : O →+* L)
  (hι : Function.Injective ι) (hR : ∀ x : L, 0 ≤ v x ↔ ∃ a : O, ι a = x)

include hR in
theorem gradNPf_v_nonneg (a : O) : 0 ≤ v (ι a) := (hR (ι a)).2 ⟨a, rfl⟩

include hι hR in
theorem gradNPf_isUnit_of_v (a : O) (ha : v (ι a) = 0) : IsUnit a := by
  have hne : ι a ≠ 0 := by
    intro h0
    rw [h0, v.map_zero] at ha
    first
      | simp at ha
  have hinv : v (ι a)⁻¹ = 0 := by
    have h1 : v (ι a * (ι a)⁻¹) = 0 := by rw [mul_inv_cancel₀ hne, v.map_one]
    rwa [v.map_mul, ha, zero_add] at h1
  obtain ⟨b, hb⟩ := (hR _).1 (le_of_eq hinv.symm)
  have hab : a * b = 1 := hι (by rw [_root_.map_mul, _root_.map_one, hb, mul_inv_cancel₀ hne])
  first
    | exact isUnit_iff_exists_inv.2 ⟨b, hab⟩

include hι hR in
private theorem exists_isUnit_mul_of_v_eq (a b : O) (hb : ι b ≠ 0) (h : v (ι a) = v (ι b)) :
    ∃ ε : O, IsUnit ε ∧ a = b * ε := by
  have hq : v (ι a * (ι b)⁻¹) = 0 := by
    rw [v.map_mul, h, ← v.map_mul, mul_inv_cancel₀ hb, v.map_one]
  obtain ⟨ε, hε⟩ := (hR _).1 hq.ge
  exact ⟨ε, gradNPf_isUnit_of_v v ι hι hR ε (by rw [hε, hq]), hι (by
    rw [_root_.map_mul, hε, mul_comm (ι a), ← mul_assoc, mul_inv_cancel₀ hb, one_mul])⟩

theorem gradNPf_zero_lt_one : (0 : WithTop ℚ) < 1 := by
  first
    | exact WithTop.coe_lt_coe.2 zero_lt_one

include hι hR in
theorem gradNPf_unit_one_add (lO d : O) (hl : v (ι lO) = 1) : IsUnit (1 + lO * d) := by
  apply gradNPf_isUnit_of_v v ι hι hR
  have h0 : 0 ≤ v (ι d) := gradNPf_v_nonneg v ι hR d
  have hy : v (ι lO * ι d) = 1 + v (ι d) := by rw [v.map_mul, hl]
  have hle : (1 : WithTop ℚ) ≤ 1 + v (ι d) := by
    first
      | exact le_add_of_nonneg_right h0
  have hlt : v (1 : L) < v (ι lO * ι d) := by
    rw [v.map_one, hy]
    exact lt_of_lt_of_le gradNPf_zero_lt_one hle
  rw [_root_.map_add (f := _), _root_.map_one, _root_.map_mul, v.map_add_eq_of_lt_left hlt, v.map_one]

include hι hR in
theorem gradNPf_unit_nat (l : ℕ) (hp : l.Prime) (hl : v (l : L) = 1) (m : ℕ) (hm : ¬ l ∣ m) :
    IsUnit (m : O) := by
  refine gradNPf_isUnit_of_v v ι hι hR _ ?_
  rw [_root_.map_natCast]
  exact UnusedSlot80.LTE.natCast_eq_zero_of_not_dvd v hp hl hm

include hι hR in
theorem gradNPf_sub_one (lO x : O) (hl : v (ι lO) = 1) (hx : v (ι x - 1) = 1) :
    ∃ t : O, IsUnit t ∧ x - 1 = lO * t := by
  have hne : ι lO ≠ 0 := by
    intro h0
    rw [h0, v.map_zero] at hl
    first
      | simp at hl
  exact exists_isUnit_mul_of_v_eq v ι hι hR _ _ hne (by rw [_root_.map_sub, _root_.map_one, hx, hl])


include hι hR in
theorem gradNPf_lte (l : ℕ) [hp : Fact l.Prime] (hl2 : l ≠ 2) (hl : v (l : L) = 1)
    (x t : O) (ht : IsUnit t) (hxt : x - 1 = (l : O) * t) :
    ∀ m : ℕ, m ≠ 0 → ∃ ε : O, IsUnit ε ∧ x ^ m - 1 = (l : O) ^ (1 + padicValNat l m) * ε := by
  intro m hm
  have hlO : v (ι (l : O)) = 1 := by rw [_root_.map_natCast]; exact hl
  have hl0 : (l : L) ≠ 0 := fun h0 => by
    rw [h0, v.map_zero] at hl
    simp at hl
  have ht0 : v (ι t) = 0 := by
    obtain ⟨u, rfl⟩ := ht
    refine le_antisymm ?_ (gradNPf_v_nonneg v ι hR _)
    have h1 : v (ι u) + v (ι ↑u⁻¹) = 0 := by
      rw [← v.map_mul, ← _root_.map_mul, Units.mul_inv, _root_.map_one, v.map_one]
    rw [← h1]
    exact le_add_of_nonneg_right (gradNPf_v_nonneg v ι hR _)
  have hx1 : v (ι x - 1) = 1 := by
    rw [← _root_.map_one ι, ← _root_.map_sub, hxt, _root_.map_mul, v.map_mul, hlO, ht0, add_zero]
  have h1 : v (ι (x ^ m - 1)) = 1 + (padicValNat l m : WithTop ℚ) := by
    rw [_root_.map_sub, _root_.map_pow, _root_.map_one,
      UnusedSlot80.LTE.val_pow_sub_one_nat v hp.out hl2 hl hx1.ge hm, hx1]
  have hne : ι ((l : O) ^ (1 + padicValNat l m)) ≠ 0 := by
    rw [_root_.map_pow, _root_.map_natCast]
    exact pow_ne_zero _ hl0
  refine exists_isUnit_mul_of_v_eq v ι hι hR _ _ hne ?_
  rw [h1, _root_.map_pow, v.map_pow, hlO]
  simp

theorem gradNPf_sum_val (l : ℕ) [hp : Fact l.Prime] (N : ℕ) :
    ∑ y ∈ Ico 1 (N + 1), (1 + padicValNat l y) = N + padicValNat l N.factorial := by
  induction N with
  | zero =>
    have hz : padicValNat l 1 = 0 := by
      simpa only [← Nat.padicValNat_def] using (multiplicity_one_right (a := l))
    simp [hz]
  | succ N ih =>
    rw [sum_Ico_succ_top (by omega : 1 ≤ N + 1), ih, Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero N) (Nat.factorial_ne_zero N)]
    ring


include hι hR in
theorem gradNPf_prod (l : ℕ) [hp : Fact l.Prime] (hl2 : l ≠ 2) (hl : v (l : L) = 1)
    (x t : O) (ht : IsUnit t) (hxt : x - 1 = (l : O) * t) (s : ℕ) (hs : s ≠ 0) (hsl : ¬ l ∣ s)
    (N : ℕ) : ∃ a : O, (l : O) ^ (N + padicValNat l N.factorial) =
      a * ∏ y ∈ Ico 1 (N + 1), ((x ^ s) ^ y - 1) := by
  have key : ∀ n : ℕ, ∃ E : O, IsUnit E ∧ ∏ y ∈ Ico 1 (n + 1), ((x ^ s) ^ y - 1) =
      (l : O) ^ (∑ y ∈ Ico 1 (n + 1), (1 + padicValNat l y)) * E := by
    intro n
    induction n with
    | zero => exact ⟨1, isUnit_one, by simp⟩
    | succ n ih =>
      obtain ⟨E, hE, hEq⟩ := ih
      obtain ⟨ε, hε, he⟩ := gradNPf_lte v ι hι hR l hl2 hl x t ht hxt
        (s * (n + 1)) (Nat.mul_ne_zero hs (Nat.succ_ne_zero n))
      rw [Nat.padicValNat_def, Nat.multiplicity_mul hs (Nat.succ_ne_zero n),
        multiplicity_eq_zero_of_not_dvd hsl, zero_add, ← Nat.padicValNat_def] at he
      refine ⟨E * ε, hE.mul hε, ?_⟩
      rw [prod_Ico_succ_top (by omega : 1 ≤ n + 1), sum_Ico_succ_top (by omega : 1 ≤ n + 1),
        hEq, ← pow_mul, he]
      ring
  obtain ⟨E, hE, hEq⟩ := key N
  obtain ⟨u, rfl⟩ := hE
  refine ⟨↑u⁻¹, ?_⟩
  rw [hEq, gradNPf_sum_val l N]
  linear_combination (-((l : O) ^ (N + padicValNat l N.factorial))) * Units.inv_mul u

end GradNPfVal

end Formalism.MainNotions.N.Ln34
