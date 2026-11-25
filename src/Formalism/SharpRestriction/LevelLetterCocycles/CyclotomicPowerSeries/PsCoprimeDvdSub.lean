module

public import Formalism.SharpRestriction.LevelLetterCocycles.CyclotomicPowerSeries.ConstSectionStatement

@[expose] public section

noncomputable section

namespace LevelStatements.Lv

open PowerSeries IsLocalRing

theorem psCoprime : PsCoprimeStatement := by
  intro O _ l φ h
  have step n := map_dvd (φ ^ n) h
  simp only [← AlgHom.coe_pow, map_mul, map_add, map_natCast] at *
  have chain := Nat.rel_of_forall_rel_succ_of_le (· ∣ ·) fun n => dvd_of_mul_right_dvd (step n)
  have mem_span {x y : PowerSeries O} (hxy : x ∣ y) :
      (l : PowerSeries O) ∈ Ideal.span {y + l, x} := by
    obtain ⟨q, rfl⟩ := hxy
    exact Ideal.mem_span_pair.mpr ⟨1, -q, by ring⟩
  constructor
  · intro s
    apply mem_span
    simpa using chain (Nat.zero_le s)
  · intro s t hst
    rcases lt_or_gt_of_ne hst with h | h
    · rw [Set.pair_comm]
      exact mem_span ((dvd_of_mul_left_dvd (step s)).trans (chain h))
    · exact mem_span ((dvd_of_mul_left_dvd (step t)).trans (chain h))

end LevelStatements.Lv
