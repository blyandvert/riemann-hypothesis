module

import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.SimpleModule.Basic

@[expose] public section

noncomputable def UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr.{u_1, u_2, u_3} :
    {k : Type u_1} → [Field k] → {n : Type u_2} → [Fintype n] → [DecidableEq n] → {G : Type u_3} → (G → Matrix n n k) → Prop :=
    fun {k : Type u_1} [Field k] {n : Type u_2} [Fintype n] [DecidableEq n] {G : Type u_3} (ρ : G → Matrix n n k) ↦
      (∀ (W : Submodule k (n → k)), (∀ (g : G), ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
        ∀ (M : Matrix n n k), (∀ (g : G), M * ρ g = ρ g * M) → ∃ (c : k), M = c • (1 : Matrix n n k)

noncomputable def UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.StatOntoSpan :
    Prop :=
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (n : Type) [Fintype n] [DecidableEq n]
      (G : Type) [Monoid G] (ρ : G →* Matrix n n O),
      (UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr fun (g : G) ↦
          ((ρ : G → Matrix n n O) g).map (⇑(IsLocalRing.residue O) : O → IsLocalRing.ResidueField O)) →
        Submodule.span O (Set.range (⇑ρ : G → Matrix n n O)) = ⊤

private theorem UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.adjoin_top {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
    {G : Type} (ρ : G → Matrix n n k) (h : UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr ρ) :
    Algebra.adjoin k (Set.range ρ) = ⊤ := by
  classical
  obtain ⟨h1, h2⟩ := h
  set A : Subalgebra k (Module.End k (n → k)) :=
    (Algebra.adjoin k (Set.range ρ)).map (Matrix.toLinAlgEquiv' (R := k) (n := n)).toAlgHom with hA
  have hmem : ∀ g, Matrix.toLin' (ρ g) ∈ A := fun g =>
    ⟨ρ g, Algebra.subset_adjoin ⟨g, rfl⟩, rfl⟩
  have hsm : ∀ (a : A) (v : n → k), a • v = (a : Module.End k (n → k)) v := fun _ _ => rfl
  have hk : ∀ (c : k) (v : n → k), (algebraMap k A c) • v = c • v := fun c v => by
    rw [hsm]; simp
  haveI : IsSemisimpleModule A (n → k) := by
    rw [isSemisimpleModule_iff]
    constructor
    intro W
    let W' : Submodule k (n → k) :=
      { carrier := W
        add_mem' := fun ha hb => W.add_mem ha hb
        zero_mem' := W.zero_mem
        smul_mem' := fun c v hv => by
          rw [← hk]; exact W.smul_mem _ hv }
    have hW := h1 W' (fun g v hv => by
      have := W.smul_mem (⟨_, hmem g⟩ : A) hv
      rw [hsm] at this
      exact this)
    rcases hW with hW | hW
    · have : W = ⊥ := by
        ext v
        have : v ∈ W' ↔ v ∈ (⊥ : Submodule k (n → k)) := by rw [hW]
        exact this
      exact ⟨⊤, this ▸ isCompl_bot_top⟩
    · have : W = ⊤ := by
        ext v
        have : v ∈ W' ↔ v ∈ (⊤ : Submodule k (n → k)) := by rw [hW]
        exact this
      exact ⟨⊥, this ▸ isCompl_top_bot⟩
  have hsc : ∀ φ : Module.End A (n → k), ∃ c : k, ∀ v, φ v = c • v := by
    intro φ
    let ψ : Module.End k (n → k) :=
      { toFun := φ
        map_add' := φ.map_add
        map_smul' := fun c v => by
          rw [← hk, φ.map_smul, hk]; rfl }
    obtain ⟨c, hc⟩ := h2 (LinearMap.toMatrix' ψ) (fun g => by
      apply Matrix.toLin'.injective
      rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
      refine LinearMap.ext fun v => ?_
      exact φ.map_smul (⟨_, hmem g⟩ : A) v)
    refine ⟨c, fun v => ?_⟩
    have h3 : ψ = Matrix.toLin' (c • (1 : Matrix n n k)) := by
      rw [← hc, Matrix.toLin'_toMatrix']
    have h4 : φ v = ψ v := rfl
    rw [h4, h3]
    simp
  rw [eq_top_iff]
  intro M _
  let f : Module.End (Module.End A (n → k)) (n → k) :=
    { toFun := Matrix.toLin' M
      map_add' := (Matrix.toLin' M).map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := hsc φ
        change Matrix.toLin' M (φ v) = φ (Matrix.toLin' M v)
        rw [hc, hc, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density (R := A) f
    (Finset.univ.image fun i : n => (Pi.single i 1 : n → k))
  obtain ⟨r, N, hN, rfl⟩ := r
  have : M = N := by
    apply Matrix.toLin'.injective
    apply (Pi.basisFun k n).ext
    intro i
    rw [Pi.basisFun_apply]
    exact hr _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  exact this ▸ hN

theorem UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.span_range
    {k n G : Type} [Field k] [Fintype n] [DecidableEq n] [Monoid G]
    (ρ : G →* Matrix n n k) (h : UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.AbsIrr ρ) :
    Submodule.span k (Set.range ρ) = ⊤ := by
  rw [← Algebra.adjoin_eq_span_of_subset]
  · exact (congrArg Subalgebra.toSubmodule (UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.adjoin_top _ h)).trans rfl
  · intro x hx
    apply Submodule.subset_span
    exact (Submonoid.closure_le (S := MonoidHom.mrange ρ)).mpr (fun _ hg => hg) hx

theorem UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.ontoSpan :
    UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.StatOntoSpan := by
  intro O _ _ n _ _ G _ ρ h
  apply KStar.Schema.span_range_eq_top_of_residue ρ
  exact UpperTheory.Reformulated.B.AbsolutelyIrreducibleSpan.span_range
    ((IsLocalRing.residue O).mapMatrix.toMonoidHom.comp ρ) h
