module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.EigenRingInvariants

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.LTB

open PowerSeries

section Roots

variable {O : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]

theorem root_eq (l : ℕ) [hp : Fact l.Prime] {x₀ y w : O} (hx : x₀ ≠ 0)
    (hrx : (1 + x₀) ^ l = 1) (hry : (1 + y) ^ l = 1)
    (hw : w ∈ IsLocalRing.maximalIdeal O) (hyw : y - x₀ = x₀ * w) : y = x₀ := by
  have hζ1 : (1 + x₀) ≠ 1 := fun h => hx (by linear_combination h)
  have hprim : IsPrimitiveRoot (1 + x₀) l := by
    have h := IsPrimitiveRoot.orderOf (1 + x₀)
    rwa [orderOf_eq_prime hrx hζ1] at h
  have hmem : ∀ z : O, (1 + z) ^ l = 1 → 1 + z ∈ Polynomial.nthRootsFinset l (1 : O) := fun z hz => by
    rw [Polynomial.mem_nthRootsFinset hp.out.pos]
    exact hz
  by_contra hne
  obtain ⟨u, hu⟩ := hprim.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hp.out
    (hmem y hry) (hmem x₀ hrx) fun h => hne (by linear_combination h)
  have hwu : w = u := mul_left_cancel₀ hx (by linear_combination -hu - hyw)
  exact (IsLocalRing.mem_maximalIdeal w).1 hw (hwu ▸ u.isUnit)

end Roots

section Main

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem mem_max (l : ℕ) [hp : Fact l.Prime] (hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    {x₀ : O} (hroot : (1 + x₀) ^ l = 1) : x₀ ∈ IsLocalRing.maximalIdeal O := by
  have hk : ((l : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hl
  haveI : CharP (IsLocalRing.ResidueField O) l := by
    first
    | exact (CharP.charP_iff_prime_eq_zero hp.out).2 hk
  have h := congrArg (IsLocalRing.residue O) hroot
  simp only [map_pow, map_add (f := _), map_one] at h
  rw [add_pow_char, one_pow] at h
  have h2 : (IsLocalRing.residue O x₀) ^ l = 0 := by linear_combination h
  exact (IsLocalRing.residue_eq_zero_iff _).1 (pow_eq_zero_iff hp.out.ne_zero |>.1 h2)

theorem map_res {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) :
    PowerSeries.map (IsLocalRing.residue O) (X - C x₀) = X :=
  DualFramesAlt.eigenRingInvariants.map_residue_X_sub_C hx

theorem map_mk {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) :
    PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (X - C x₀) = X :=
  map_res hx

theorem decomp {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) (p : O⟦X⟧) :
    ∃ c : O, ∃ q : O⟦X⟧, p = (X - C x₀) * q + C c := by
  obtain ⟨c, hc⟩ := DualFramesAlt.eigenRingInvariants.ev_exists hx p
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hc)
  exact ⟨c, q, by linear_combination hq⟩

theorem uniq {x₀ : O} (hx : x₀ ∈ IsLocalRing.maximalIdeal O) {c : O}
    (hc : C c ∈ Ideal.span {X - C x₀}) : c = 0 :=
  DualFramesAlt.eigenRingInvariants.ev_zero hx (Ideal.Quotient.eq_zero_iff_mem.2 hc)

def Fs (l : ℕ) (x₀ : O) (a : O⟦X⟧) : O⟦X⟧ :=
  ∑ i ∈ Finset.range l, (1 + a) ^ i * (1 + C x₀) ^ (l - 1 - i)

theorem Fs_mul (l : ℕ) {x₀ : O} (hroot : (1 + x₀) ^ l = 1) (a : O⟦X⟧) :
    (1 + a) ^ l - 1 = Fs l x₀ a * (a - C x₀) := by
  have hy : (1 + C x₀ : O⟦X⟧) ^ l = 1 := by
    simpa [map_pow, map_add (f := _), map_one] using congrArg (C : O →+* O⟦X⟧) hroot
  have h := geom_sum₂_mul (1 + a) (1 + C x₀) l
  rw [hy] at h
  unfold Fs
  rw [← h]
  congr 1
  ring

end Main

end Formalism.MainNotions.N.FrobeniusPowerSeries.LTB
