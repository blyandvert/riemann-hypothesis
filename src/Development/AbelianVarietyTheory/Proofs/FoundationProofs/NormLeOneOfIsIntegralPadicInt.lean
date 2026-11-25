module

public import Formalism.ConjugateSelfDual.Statement
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormLeOneOfIntegralInt

@[expose] public section

namespace GlobalTheory.PadicIntegralNorm

theorem norm_le_one_of_isIntegral {R K : Type*} [CommRing R] [NormedField K] [IsUltrametricDist K] [Algebra R K]
    (hR : ∀ r : R, ‖algebraMap R K r‖ ≤ 1) (x : K) (hx : IsIntegral R x) : ‖x‖ ≤ 1 :=
  ReciprocityTheory.ChartRestriction.L1.KE.norm_le_one_of_integral hR x hx

theorem norm_le_one_of_isIntegral_padicInt {l : ℕ} [inst : Fact (Nat.Prime l)] (x : Formalism.ConjugateSelfDual.Qbar l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  refine norm_le_one_of_isIntegral (R := ℤ_[l]) (fun r => ?_) x hx
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Formalism.ConjugateSelfDual.Qbar l), norm_algebraMap']
  exact PadicInt.norm_le_one r

end GlobalTheory.PadicIntegralNorm
