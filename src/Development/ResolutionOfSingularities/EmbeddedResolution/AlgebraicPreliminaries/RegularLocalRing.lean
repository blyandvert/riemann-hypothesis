module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.SpanSingletonProduct
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne
public import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace IsRegularLocalRing

open IsLocalRing
open PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing
  (spanFinrank_maximalIdeal_quotient_succ_le spanFinrank_quotient_eq_and_ringKrullDim_add_one
    isLocalRing_quotient_span_singleton isDomain_of_spanFinrank_le)

universe u

theorem isRegularLocalRing_quotient_span_singleton {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) := by
  have := isLocalRing_quotient_span_singleton hx
  rw [isRegularLocalRing_iff]
  exact_mod_cast (spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).1

theorem ringKrullDim_quotient_span_singleton_add_one {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ IsLocalRing.maximalIdeal R ^ 2) :
    ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  have := isLocalRing_quotient_span_singleton hx
  exact (spanFinrank_quotient_eq_and_ringKrullDim_add_one R hx hx2).2

theorem isDomain (R : Type*) [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  isDomain_of_spanFinrank_le (Submodule.spanFinrank (IsLocalRing.maximalIdeal R)) R le_rfl

instance (priority := 100) instIsDomain {R : Type*} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain R

private theorem false_of_eq_smul_of_linearIndependent {K M : Type*} {ι : Type*} [Field K]
    [AddCommGroup M] [Module K M] {v : ι → M} (h : LinearIndependent K v) {i j : ι}
    (hij : i ≠ j) (c : K) (he : v j = c • v i) : False := by
  classical
  have key : ∑ k ∈ ({i, j} : Finset ι),
      (fun k => if k = i then c else if k = j then (-1 : K) else 0) k • v k = 0 := by
    rw [Finset.sum_pair hij]
    simp [Ne.symm hij, he]
  have h2 := linearIndependent_iff'.mp h {i, j}
      (fun k => if k = i then c else if k = j then (-1 : K) else 0) key j (by simp)
  simp [Ne.symm hij] at h2

private theorem toCotangent_mul_eq_smul {R : Type*} [CommRing R] [IsLocalRing R] (r a : R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) (hra : r * a ∈ IsLocalRing.maximalIdeal R) :
    ((IsLocalRing.maximalIdeal R).toCotangent ⟨r * a, hra⟩ : IsLocalRing.CotangentSpace R) =
      algebraMap R (IsLocalRing.ResidueField R) r •
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩ : IsLocalRing.CotangentSpace R) := by
  have h1 : (⟨r * a, hra⟩ : IsLocalRing.maximalIdeal R)
      = r • (⟨a, ha⟩ : IsLocalRing.maximalIdeal R) := Subtype.ext rfl
  rw [algebraMap_smul, h1, map_smul]

theorem notMem_maximalIdeal_sq {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    (i : ι) : x i ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  intro hmem
  have h0 : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
      IsLocalRing.CotangentSpace R) = 0 := by
    rw [Ideal.toCotangent_eq_zero]
    exact hmem
  exact hli.ne_zero i h0

theorem isPrime_span_singleton {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    (i : ι) : (Ideal.span ({x i} : Set R)).IsPrime := by
  have : IsRegularLocalRing (R ⧸ Ideal.span ({x i} : Set R)) :=
    isRegularLocalRing_quotient_span_singleton (hx i) (notMem_maximalIdeal_sq x hx hli i)
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact IsRegularLocalRing.isDomain _

theorem notMem_span_singleton {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R))
    {i j : ι} (hij : i ≠ j) : x j ∉ Ideal.span ({x i} : Set R) := by
  intro hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  have hmem2 : r * x i ∈ IsLocalRing.maximalIdeal R := by
    rw [hr]
    exact hx j
  have key : ((IsLocalRing.maximalIdeal R).toCotangent ⟨x j, hx j⟩ :
      IsLocalRing.CotangentSpace R)
      = algebraMap R (IsLocalRing.ResidueField R) r •
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
          IsLocalRing.CotangentSpace R) := by
    have hsub : (⟨x j, hx j⟩ : IsLocalRing.maximalIdeal R) = ⟨r * x i, hmem2⟩ :=
      Subtype.ext hr.symm
    rw [hsub]
    exact toCotangent_mul_eq_smul r (x i) (hx i) hmem2
  exact false_of_eq_smul_of_linearIndependent hli hij _ key

theorem isRadical_span_singleton_prod {R : Type*} [CommRing R] [IsRegularLocalRing R] {ι : Type*}
    [Fintype ι] (x : ι → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
    (hli : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ⟨x i, hx i⟩ :
        ι → IsLocalRing.CotangentSpace R)) :
    (Ideal.span ({∏ i, x i} : Set R)).IsRadical := by
  classical
  exact FunctorialResolution.EmbeddedResolution.isRadical_span_singleton_prod_finset x Finset.univ
    (fun i _ => isPrime_span_singleton x hx hli i)
    (fun i _ j _ hij => notMem_span_singleton x hx hli hij)

end IsRegularLocalRing
