import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellSubcloud
import OTSelector.Reconstruction.FinslerRelativeLawOriginalMarkedCellPrefix

/-! The actual ordered original retained prefix supplies the finite optimizer
restriction and Hall-defect identities without a caller enumeration premise. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

section Finite
variable {X Z C T : Type*} {N : ℕ}
  (a : X → Z) (cell : C → Set Z)
  (extra : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
    Finset (Fin N × Fin N))
  (model : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
    Fin N → Fin N → ℝ) (c : C)
  (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T)))

/-- The canonical optimizer on original ambient indices restricts to an exact
legal optimum on the literal ordered retained cell observations. -/
theorem originalRetainedCellOptimizer_prefix_isLegalOptimal :
    let e := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.1
    let f := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.2
    PartialMatching.IsLegalOptimal (PartialMatching.inducedLegalGraph (extra c sample) e f)
      (fun i j ↦ model c sample (e i) (f j))
      ((originalRetainedCellOptimizer a cell extra model c sample).comapEmbedding e f) := by
  exact originalRetainedCellOptimizer_comap_isLegalOptimal a cell extra c sample _ _
    (fun i ↦ finiteOriginalRestrictedEmbedding_range _ _ i)
    (fun j ↦ finiteOriginalRestrictedEmbedding_range _ _ j) model

/-- The original prefix has exactly the ambient retained graph's legal rank. -/
theorem originalRetainedCellGraph_card_eq_prefix :
    let e := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.1
    let f := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.2
    PartialMatching.legalMaximumCard (originalRetainedCellGraph a cell extra c sample) =
      PartialMatching.legalMaximumCard (PartialMatching.inducedLegalGraph (extra c sample) e f) := by
  exact originalRetainedCellGraph_card_eq_subcloud a cell extra c sample _ _
    (fun i ↦ finiteOriginalRestrictedEmbedding_range _ _ i)
    (fun j ↦ finiteOriginalRestrictedEmbedding_range _ _ j)

/-- The literal ordered prefix realizes the exact signed frozen model value. -/
theorem originalRetainedCellGraph_value_eq_prefix :
    let e := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.1
    let f := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.2
    PartialMatching.legalMaximumValue (originalRetainedCellGraph a cell extra c sample) (model c sample) =
      PartialMatching.legalMaximumValue (PartialMatching.inducedLegalGraph (extra c sample) e f)
        (fun i j ↦ model c sample (e i) (f j)) := by
  exact originalRetainedCellGraph_value_eq_subcloud a cell extra c sample _ _
    (fun i ↦ finiteOriginalRestrictedEmbedding_range _ _ i)
    (fun j ↦ finiteOriginalRestrictedEmbedding_range _ _ j) _

end Finite

/-- On the same actual original marked experiment, every retained-cell real
source defect is exactly the Hall deficit of its literal ordered original
prefix. Proper original type coverage and enumeration completeness are both
discharged before any cell or matching is selected. -/
theorem PopulationTypedCostData.original_retained_cell_defect_eq_prefix_ae
    {X Z C T : Type*} [MeasurableSpace X] [Fintype T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {π : Measure (X × X)} [IsFiniteMeasure π] {q : ℕ} {cost : X → X → ℝ}
    (D : PopulationTypedCostData π μ ν T q cost) (hπ : Vlasov.IsCoupling π μ ν)
    (ξ : Measure (X × X)) (hξ : ξ ≤ π) (N : ℕ)
    (a : X → Z) (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell))
    (extra : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Finset (Fin N × Fin N))
    (model : C → ((Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) →
      Fin N → Fin N → ℝ) :
    let R := D.refineSubplan ξ hξ
    ∀ᵐ sample ∂R.markedLaw N, ∀ c : C,
      let dataS := finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.1
      let e := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.1
      let f := finiteOriginalRestrictedEmbedding (retainedMarkedCellEvent (a ⁻¹' cell c)) sample.2
      partitionCount (fun i ↦ originalRetainedCellTag a cell
          (PopulationTypedCostData.selectedSubplanTags (T := T)) (sample.1 i)) (some c) -
        (originalRetainedCellOptimizer a cell extra model c sample).card =
        ((dataS.1 - PartialMatching.legalMaximumCard
          (PartialMatching.inducedLegalGraph (extra c sample) e f) : ℕ) : ℝ) := by
  have h := D.original_retained_cell_defect_eq_subcloud_ae hπ ξ hξ N a cell hdisj extra model
  filter_upwards [h] with sample hs
  intro c
  exact hs c _ _ _ _ (fun i ↦ finiteOriginalRestrictedEmbedding_range _ _ i)
    (fun j ↦ finiteOriginalRestrictedEmbedding_range _ _ j)

end OTSelector.Reconstruction
