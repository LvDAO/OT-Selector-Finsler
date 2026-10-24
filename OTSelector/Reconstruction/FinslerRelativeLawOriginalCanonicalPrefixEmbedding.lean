import OTSelector.Reconstruction.FinslerRelativeLawOriginalPrefixOptimizer
import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergy

/-! Canonical original retained optimizers are exact embedded prefix optimizers. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- A class mask induces the literal same class graph on every original
ordered subcloud, including empty source or target prefixes. -/
theorem PartialMatching.inducedLegalGraph_classMask
    {A B : Type*} {N m n : ℕ} (allowed : A → B → Prop)
    (s : Fin N → A) (t : Fin N → B) (e : Fin m ↪ Fin N) (f : Fin n ↪ Fin N) :
    PartialMatching.inducedLegalGraph
      (Finset.univ.filter fun p : Fin N × Fin N ↦ allowed (s p.1) (t p.2)) e f =
      Finset.univ.filter (fun p : Fin m × Fin n ↦ allowed (s (e p.1)) (t (f p.2))) := by
  classical
  ext p
  simp [PartialMatching.inducedLegalGraph]

/-- Embedding the restricted canonical optimizer preserves its full ORIGINAL
physical cost. No equality of different first-optimum tie rules is required. -/
theorem originalRetainedCellOptimizer_prefix_embedded_cost_eq
    {X Z C T : Type*} {N : ℕ}
    (a : X → Z) (cell : C → Set Z)
    (extra : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Finset (Fin N × Fin N))
    (model : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Fin N → Fin N → ℝ) (c : C)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T)))
    (physical : Fin N → Fin N → ℝ) :
    let e := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.1
    let f := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.2
    let σ := originalRetainedCellOptimizer a cell extra model c sample
    ((σ.comapEmbedding e f).embedIndices e f e.injective f.injective).cost physical = σ.cost physical := by
  dsimp only
  rw [OTSelector.PartialMatching.cost_embedIndices]
  apply OTSelector.PartialMatching.cost_comapEmbedding
  intro p hp
  have hs := originalRetainedCellOptimizer_support a cell extra model c sample p hp
  exact ⟨(finiteOriginalRestrictedEmbedding_range _ _ _).mpr ⟨hs.2.1, hs.2.2.2.1⟩,
    (finiteOriginalRestrictedEmbedding_range _ _ _).mpr ⟨hs.2.2.1, hs.2.2.2.2⟩⟩

end OTSelector.Reconstruction
