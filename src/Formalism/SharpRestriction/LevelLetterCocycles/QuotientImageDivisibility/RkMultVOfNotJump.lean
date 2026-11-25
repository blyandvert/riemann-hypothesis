module

import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrMultVOfNotJump
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.Data.Int.Interval
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

section Fil

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem rk_filV_succ (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  apply +allowSynthFailures _root_.Formalism.MainNotions.N.Ln34.UniversalFiltration.fr_filV_succ <;> assumption

theorem rk_filV_anti : Antitone (fun a : ℤ => FilV PD (LL := LL) (V := V) a) := by
  exact antitone_int_of_succ_le fun a => rk_filV_succ PD a

theorem rk_filV_exh (x : V ⊗[Qp] BdR) : ∃ a : ℤ, x ∈ FilV PD (LL := LL) (V := V) a := by
  apply +allowSynthFailures _root_.Formalism.MainNotions.N.Ln34.UniversalFiltration.fr_filV_exh <;> assumption

theorem rk_filV_fd (U : Submodule LL (V ⊗[Qp] BdR)) [FiniteDimensional LL ↥U] :
    ∃ a : ℤ, U ≤ FilV PD (LL := LL) (V := V) a := by
  apply +allowSynthFailures _root_.Formalism.MainNotions.N.Ln34.UniversalFiltration.fr_filV_fd <;> assumption

theorem rk_filV_sep (x : V ⊗[Qp] BdR) (hx : ∀ a, x ∈ FilV PD (LL := LL) (V := V) a) : x = 0 :=
  Ln34.UniversalFiltration.fr_filV_sep PD x hx

variable (ρ : Representation LL G V)

theorem rk_fildR_anti (τ : K →ₐ[Qp] LL) : Antitone (FildR PD ρ τ) := by
  exact fun a b hab => inf_le_inf_left _ (rk_filV_anti PD hab)

theorem rk_fildR_lo (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ lo : ℤ, ∀ a ≤ lo, FildR PD ρ τ a = DdRE PD ρ τ := by
  obtain ⟨lo, hlo⟩ := rk_filV_fd PD (DdRE PD ρ τ)
  exact ⟨lo, fun a ha => inf_eq_left.2 (hlo.trans (rk_filV_anti PD ha))⟩

theorem rk_fildR_hi (τ : K →ₐ[Qp] LL) [FiniteDimensional LL ↥(DdRE PD ρ τ)] :
    ∃ hi : ℤ, ∀ a, hi ≤ a → FildR PD ρ τ a = ⊥ :=
  Ln34.UniversalFiltration.fr_fildR_hi PD ρ τ

theorem rk_multV_of_not_jump (τ : K →ₐ[Qp] LL) (a : ℤ) (h : ¬ IsJumpV PD ρ τ a) :
    multV PD ρ τ a = 0 := by
  unfold IsJumpV at h
  push Not at h
  unfold multV
  rw [h, sub_self]

theorem rk_sum_multV (τ : K →ₐ[Qp] LL) (m k : ℤ) (hmk : m ≤ k) :
    ∑ a ∈ Finset.Ico m k, multV PD ρ τ a =
      (finrank LL ↥(FildR PD ρ τ m) : ℤ) - finrank LL ↥(FildR PD ρ τ k) := by
  apply +allowSynthFailures _root_.Formalism.MainNotions.N.Ln34.UniversalFiltration.fr_sum_multV <;> assumption

end Fil

end Formalism.MainNotions.N.Pv.LocalLengthBound
