module

public import ReciprocityTheory.AnalyticForms.AnalyticCharts.MaDensCompEqZeroOfRankLt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian

@[expose] public section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas Complex
open scoped ContDiff ComplexOrder Matrix

noncomputable section

theorem leviC_conj_of_symm {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ)
    (hs : ∀ v w, H v w = H w v) (a b : Fin e → ℂ) :
    starRingEnd ℂ (leviC H a b) = leviC H b a := by
  have hflip : H.flip = H := by ext v w; exact hs w v
  simpa only [hflip] using conj_leviC_flip H a b

theorem leviC_self_of_symm {e : ℕ} (H : (Fin e → ℂ) →L[ℝ] (Fin e → ℂ) →L[ℝ] ℝ)
    (hs : ∀ v w, H v w = H w v) (a : Fin e → ℂ) :
    leviC H a a = (((H a a + H (I • a) (I • a)) / 4 : ℝ) : ℂ) := by
  simp only [leviC]
  rw [hs a (I • a), sub_self]
  push_cast
  ring

theorem hessC_posSemidef_of_levi {e : ℕ} (f : (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (hf : ContDiffAt ℝ 2 f z) (hl : ∀ w, 0 ≤ levi f z w) : (hessC f z).PosSemidef :=
  hessC_posSemidef f z hf hl

theorem pot_contDiffAt_two {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (x : X) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (hyU : (A.chart j).symm y ∈ P.U x) :
    ContDiffAt ℝ 2 (P.φ x ∘ (A.chart j).symm) y := by
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (P.isOpen_U x)
  exact ((hP.1 x j).contDiffAt (hopen.mem_nhds ⟨hy, hyU⟩)).of_le (by first | exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))

theorem hessC_locPot_posSemidef {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P : LocPot X} (hP : IsPotential A P) (hPsh : IsPsh A P) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) :
    (hessC (fun y' => P.φ ((A.chart j).symm y) ((A.chart j).symm y')) y).PosSemidef := by
  exact hessC_posSemidef_of_levi _ y (pot_contDiffAt_two hP _ j hy (P.mem_U _))
    (fun w => hPsh _ j y ⟨hy, P.mem_U _⟩ w)

theorem locDens_nonneg_of_psh {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hPsh : ∀ i, IsPsh A (Φ i))
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) : 0 ≤ locDens A Φ j y := by
  exact ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ y
    (fun i => hessC_locPot_posSemidef (hΦ i) (hPsh i) j hy)

theorem locDens_le_add {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ Θ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hΦp : ∀ i, IsPsh A (Φ i))
    (hΘ : ∀ i, IsPotential A (Θ i)) (hΘp : ∀ i, IsPsh A (Θ i))
    (j : Fin A.n) {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) :
    locDens A Φ j y ≤ locDens A (fun i => Φ i + Θ i) j y := by
  unfold locDens maDens
  refine mul_le_mul_of_nonneg_left (ReciprocityTheory.AnForm.A.mdisc_re_mono _ _
    (fun k => hessC_locPot_posSemidef (hΦ k) (hΦp k) j hy) fun k => ?_) (by positivity)
  show (hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
      (Θ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y -
    hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y).PosSemidef
  rw [_root_.ReciprocityTheory.AnForm.A.TraceConjugationCover.complexHessian_add_of_contDiffAt (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y'))
    (fun y' => (Θ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y (pot_contDiffAt_two (hΦ k) _ j hy ((Φ k).mem_U _))
    (pot_contDiffAt_two (hΘ k) _ j hy ((Θ k).mem_U _)), add_sub_cancel_left]
  exact hessC_locPot_posSemidef (hΘ k) (hΘp k) j hy

end

end ReciprocityTheory.AnForm.M
