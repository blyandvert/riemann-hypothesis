module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Order.Archimedean.Defs
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.CvZeroTerm

@[expose] public section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

def LB (m : ℤ) (f : ℤ → V) : Prop := ∀ k < m, f k = 0

def smulS (g : PowerSeries LL) (f : ℤ → V) : ℤ → V :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j g • f (k - j)

theorem smulS_eq_sum {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (k : ℤ) (N : ℕ)
    (hN : k - m < N) : smulS g f k = ∑ j ∈ Finset.range N, PowerSeries.coeff j g • f (k - j) :=
  Ln03.Pf.ConvolutionAlt.cv_eq_sum g f m hf k N hN

theorem LB_mono {m m' : ℤ} {f : ℤ → V} (hf : LB m f) (h : m' ≤ m) : LB m' f := by
  intro k hk
  exact hf k (lt_of_lt_of_le hk h)

theorem LB_smulS {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) : LB m (smulS g f) := by
  intro k hk
  rw [smulS_eq_sum hf g k 0 (by omega)]
  simp

theorem LB_add {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') : LB m (f + f') := by
  intro k hk
  simp [hf k hk, hf' k hk]

theorem LB_sub {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') : LB m (f - f') := by
  intro k hk
  simp [hf k hk, hf' k hk]

theorem LB_smul {m : ℤ} {f : ℤ → V} (hf : LB m f) (c : LL) : LB m (c • f) := by
  intro k hk
  simp [hf k hk]

theorem smulS_add {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') (g : PowerSeries LL) :
    smulS g (f + f') = smulS g f + smulS g f' := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  rw [Pi.add_apply, smulS_eq_sum (LB_add hf hf') g k N hN,
    smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, smul_add]

theorem smulS_sub {m : ℤ} {f f' : ℤ → V} (hf : LB m f) (hf' : LB m f') (g : PowerSeries LL) :
    smulS g (f - f') = smulS g f - smulS g f' := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  rw [Pi.sub_apply, smulS_eq_sum (LB_sub hf hf') g k N hN,
    smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply, smul_sub]

theorem smulS_smul {m : ℤ} {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (c : LL) :
    smulS g (c • f) = c • smulS g f := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  rw [Pi.smul_apply, smulS_eq_sum (LB_smul hf c) g k N hN,
    smulS_eq_sum hf g k N hN, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply]
  exact smul_comm _ _ _

private theorem smulS_C_eq_smul_of_LB {m : ℤ} {f : ℤ → V} (hf : LB m f) (c : LL) :
    smulS (PowerSeries.C c) f = c • f := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  rw [smulS_eq_sum hf _ k (N + 1) (by omega), Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [PowerSeries.coeff_C, hj]
  · intro h0
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h0

theorem smulS_one {m : ℤ} {f : ℤ → V} (hf : LB m f) : smulS (1 : PowerSeries LL) f = f := by
  first
  | simpa using smulS_C_eq_smul_of_LB hf (1 : LL)

alias smulS_C := _root_.Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_C_eq_smul_of_LB

theorem smulS_X_pow {m : ℤ} {f : ℤ → V} (hf : LB m f) (K : ℕ) :
    smulS ((PowerSeries.X : PowerSeries LL) ^ K) f = fun k => f (k - K) := by
  funext k
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  rw [smulS_eq_sum hf _ k (N + K + 1) (by omega), Finset.sum_eq_single K]
  · simp [PowerSeries.coeff_X_pow]
  · intro j _ hj
    simp [PowerSeries.coeff_X_pow, hj]
  · intro hK
    exact absurd (Finset.mem_range.mpr (by omega)) hK

theorem smulS_mul {m : ℤ} {f : ℤ → V} (hf : LB m f) (g h : PowerSeries LL) :
    smulS (g * h) f = smulS g (smulS h f) :=
  funext (Ln03.Pf.ConvolutionAlt.cv_mul g h f m hf)

theorem smulS_inv {m : ℤ} {f : ℤ → V} (hf : LB m f) (u : PowerSeries LL)
    (hu : PowerSeries.constantCoeff u ≠ 0) : smulS u⁻¹ (smulS u f) = f := by
  have h1 : u⁻¹ * u = 1 := by
    first
    | exact PowerSeries.inv_mul_cancel u hu
  rw [← smulS_mul hf, h1, smulS_one hf]

def Dg (Fil : ℤ → Submodule LL V) (s : ℤ) (f : ℤ → V) : Prop := ∀ k, f k ∈ Fil (s - k)

theorem Dg_smulS {Fil : ℤ → Submodule LL V} (hF : Antitone Fil) {m s : ℤ} {f : ℤ → V}
    (hf : LB m f) (hD : Dg Fil s f) (g : PowerSeries LL) : Dg Fil s (smulS g f) := by
  intro k
  obtain ⟨N, hN⟩ := exists_nat_gt (k - m)
  rw [smulS_eq_sum hf g k N hN]
  refine sum_mem fun j _ => Submodule.smul_mem _ _ ?_
  exact hF (by omega : s - k ≤ s - (k - (j : ℤ))) (hD (k - j))

def resc (χ : LL) (f : ℤ → V) : ℤ → V := fun k => (χ ^ k) • f k

theorem LB_resc {m : ℤ} {f : ℤ → V} (hf : LB m f) (χ : LL) : LB m (resc χ f) := by
  intro k hk
  show (χ ^ k) • f k = 0
  rw [hf k hk, smul_zero]

theorem smulS_rescale {m : ℤ} {f : ℤ → V} (hf : LB m f) (χ : LL) (hχ : χ ≠ 0)
    (g : PowerSeries LL) : smulS (PowerSeries.rescale χ g) (resc χ f) = resc χ (smulS g f) :=
  funext fun k => (Ln03.Pf.ConvolutionAlt.cv_twist LinearMap.id χ hχ g f m hf k).symm

end Formalism.MainNotions.N.Pv.LocalLengthBound.Ser
