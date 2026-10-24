import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineResidualEnergy
import OTSelector.Reconstruction.FinslerRelativeLawDeterministicLabelRestriction
import OTSelector.Reconstruction.FinslerRelativeLawGlobalRetainedCell

/-! Original retained marginal properties hold on all fine retained vertices before selection. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- Every property of the original retained marginals holds on every good or
bad fine retained vertex, on one common event for the entire unchanged sample. -/
theorem rnCellRefinedTypes_retained_endpoint_properties
    (Ps : X → Prop) (Pt : Y → Prop)
    (hs : ∀ᵐ x ∂(π - η).map Prod.fst, Ps x)
    (ht : ∀ᵐ y ∂(π - η).map Prod.snd, Pt y) {I J : Type*} [Fintype I] [Fintype J] :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    ∀ᵐ sample ∂(Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν)),
      (∀ i, subplanRetentionFlag ((sample.1 i).2.map cellRefinedSubplanType) = false →
        Ps (sample.1 i).1) ∧
      (∀ j, subplanRetentionFlag ((sample.2 j).2.map cellRefinedSubplanType) = false →
        Pt (sample.2 j).1) := by
  letI : MeasurableSpace (Option T) := ⊤
  letI : MeasurableSingletonClass (Option T) := ⟨fun _ ↦ trivial⟩
  letI : MeasurableSpace (Option (Bool × T)) := ⊤
  letI : MeasurableSingletonClass (Option (Bool × T)) := ⟨fun _ ↦ trivial⟩
  let A := D.refineSubplan η hη
  have hsFalse : ∀ᵐ p ∂(A.types.sourceMarkedLaw μ).restrict
      {p | subplanRetentionFlag p.2 = false}, Ps p.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [(D.refineSubplan_retained_physical_laws η hη).1]
    exact hs
  have htFalse : ∀ᵐ p ∂(A.types.targetMarkedLaw ν).restrict
      {p | subplanRetentionFlag p.2 = false}, Pt p.1 := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [(D.refineSubplan_retained_physical_laws η hη).2]
    exact ht
  have hsArray : ∀ᵐ xs ∂Measure.pi (fun _ : I ↦ A.types.sourceMarkedLaw μ),
      ∀ i, subplanRetentionFlag (xs i).2 = false → Ps (xs i).1 :=
    ae_all_iff.mpr fun i ↦ (Measure.quasiMeasurePreserving_eval
      (fun _ : I ↦ A.types.sourceMarkedLaw μ) i).ae (ae_imp_of_ae_restrict hsFalse)
  have htArray : ∀ᵐ ys ∂Measure.pi (fun _ : J ↦ A.types.targetMarkedLaw ν),
      ∀ j, subplanRetentionFlag (ys j).2 = false → Pt (ys j).1 :=
    ae_all_iff.mpr fun j ↦ (Measure.quasiMeasurePreserving_eval
      (fun _ : J ↦ A.types.targetMarkedLaw ν) j).ae (ae_imp_of_ae_restrict htFalse)
  have hcoarse : ∀ᵐ sample ∂(Measure.pi (fun _ : I ↦ A.types.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ A.types.targetMarkedLaw ν)),
      (∀ i, subplanRetentionFlag (sample.1 i).2 = false → Ps (sample.1 i).1) ∧
      (∀ j, subplanRetentionFlag (sample.2 j).2 = false → Pt (sample.2 j).1) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsArray,
      Measure.quasiMeasurePreserving_snd.ae htArray] with sample hsource htarget
    exact ⟨hsource, htarget⟩
  have hlaw := D.types.rnCellRefinedTypes_iid_subplan_law (I := I) (J := J)
    η hη good bad hsplit μ ν
  dsimp only [A, refineSubplan] at hcoarse
  rw [← hlaw] at hcoarse
  exact ae_of_ae_map (measurable_cellRefinedSubplanObservation
    (X := X) (Y := Y) (C := C) (T := T) (I := I) (J := J)).aemeasurable hcoarse

end OTSelector.Reconstruction.PopulationTypedCostData

namespace OTSelector.Reconstruction.PopulationTypedCostData

/-- Prescribed deterministic truncations inherit every actual retained marginal
property from the SAME base original population, for all good/bad fine vertices. -/
theorem original_truncated_fine_retained_endpoint_properties
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype C] [Fintype T]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (a : X → Z) (ha : Measurable a) {G : Set Z} (hG : MeasurableSet G)
    (good : T → Measure (X × X)) (bad : C → T → Measure (X × X))
    (hsplit : ∀ t, good t + ∑ c, bad c t =
      (D.types.rnSubplanTypes (restrictOriginalRetainedResidual χ ξ a G)
        (restrictOriginalRetainedResidual_le χ ξ a ha hG)).component (false, t))
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (Ps Pt : X → Prop) (hs : ∀ᵐ x ∂χ.map Prod.fst, Ps x)
    (ht : ∀ᵐ y ∂χ.map Prod.snd, Pt y) {I J : Type*} [Fintype I] [Fintype J] :
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    ∀ᵐ sample ∂(Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν)),
      (∀ i, subplanRetentionFlag ((sample.1 i).2.map cellRefinedSubplanType) = false →
        Ps (sample.1 i).1) ∧
      (∀ j, subplanRetentionFlag ((sample.2 j).2.map cellRefinedSubplanType) = false →
        Pt (sample.2 j).1) := by
  let η := restrictOriginalRetainedResidual χ ξ a G
  let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
  have hs' : ∀ᵐ x ∂((χ + ξ) - η).map Prod.fst, Ps x := by
    rw [original_retained_label_restriction_complement χ ξ a ha hG]
    exact ae_mono (Measure.map_mono Measure.restrict_le_self measurable_fst) hs
  have ht' : ∀ᵐ y ∂((χ + ξ) - η).map Prod.snd, Pt y := by
    rw [original_retained_label_restriction_complement χ ξ a ha hG]
    exact ae_mono (Measure.map_mono Measure.restrict_le_self measurable_snd) ht
  exact D.rnCellRefinedTypes_retained_endpoint_properties η hη good bad hsplit Ps Pt hs' ht'

/-- Original physical cell marginal activity gives precisely the active source
and target class facts needed by the actual finite model comparator, on every
retained vertex of the SAME fine sample after any deterministic truncation. -/
theorem original_truncated_fine_retained_cell_class_active
    {X Z C T SClass TClass : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype C] [Fintype T]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (a : X → Z) (ha : Measurable a) {G : Set Z} (hG : MeasurableSet G)
    (good : T → Measure (X × X)) (bad : C → T → Measure (X × X))
    (hsplit : ∀ t, good t + ∑ c, bad c t =
      (D.types.rnSubplanTypes (restrictOriginalRetainedResidual χ ξ a G)
        (restrictOriginalRetainedResidual_le χ ξ a ha hG)).component (false, t))
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (L : Set Z) (classS : X → SClass) (classT : X → TClass)
    (allowed : SClass → TClass → Prop)
    (hs : ∀ᵐ x ∂(χ.map Prod.fst).restrict (a ⁻¹' L), ∃ j, allowed (classS x) j)
    (ht : ∀ᵐ y ∂(χ.map Prod.snd).restrict (a ⁻¹' L), ∃ i, allowed i (classT y))
    {I J : Type*} [Fintype I] [Fintype J] :
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    ∀ᵐ sample ∂(Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν)),
      (∀ i, subplanRetentionFlag ((sample.1 i).2.map cellRefinedSubplanType) = false →
        a (sample.1 i).1 ∈ L → ∃ j, allowed (classS (sample.1 i).1) j) ∧
      (∀ j, subplanRetentionFlag ((sample.2 j).2.map cellRefinedSubplanType) = false →
        a (sample.2 j).1 ∈ L → ∃ i, allowed i (classT (sample.2 j).1)) :=
  original_truncated_fine_retained_endpoint_properties χ ξ D a ha hG good bad hsplit
    (fun x ↦ a x ∈ L → ∃ j, allowed (classS x) j)
    (fun y ↦ a y ∈ L → ∃ i, allowed i (classT y))
    (ae_imp_of_ae_restrict hs) (ae_imp_of_ae_restrict ht)

end OTSelector.Reconstruction.PopulationTypedCostData
