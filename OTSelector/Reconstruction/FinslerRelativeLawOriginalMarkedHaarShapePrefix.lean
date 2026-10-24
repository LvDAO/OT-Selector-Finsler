import OTSelector.Probability.SubcouplingTypedIID
import OTSelector.Reconstruction.FinslerRelativeLawOriginalHaarShapePrefix

/-! Exact two-color Haar shape prefixes in the unchanged original global residual experiment. -/
open Set Function MeasureTheory ProbabilityTheory BoxIntegral
open scoped Topology ENNReal NNReal BigOperators unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- Original unnormalized Haar/class observations determine the exact paired
binomial shape prefixes in the same residual marked experiment, including all
null subcells. The original sample marginals and original indices are kept. -/
theorem PopulationTypedCostData.original_retained_haar_shape_prefix_law
    {X Y A B T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace A] [MeasurableSpace B] [Fintype T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    {π : Measure (X × Y)} [IsFiniteMeasure π]
    {νS : Measure X} [IsProbabilityMeasure νS] {νT : Measure Y} [IsProbabilityMeasure νT]
    {qAtlas : ℕ} {cost : X → Y → ℝ} (Cst : PopulationTypedCostData π νS νT T qAtlas cost)
    (hπ : Vlasov.IsCoupling π νS νT) (ξ : Measure (X × Y)) (hξ : ξ ≤ π) (N : ℕ)
    {AS : Set X} {AT : Set Y} (hAS : MeasurableSet AS) (hAT : MeasurableSet AT)
    (readS : X → E × A) (readT : Y → E × B) (hmS : Measurable readS) (hmT : Measurable readT)
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ))
    (n : ℕ) [NeZero n] (index : Fin q → ℤ) (s : Set E) (hs : MeasurableSet s)
    (τS : Measure A) [IsFiniteMeasure τS] (τT : Measure B) [IsFiniteMeasure τT]
    (hτS : 0 < τS.real univ) (hτT : 0 < τT.real univ) (htotal : τT univ = τS univ)
    (hsource : (((π - ξ).map Prod.fst).restrict AS).map readS =
      (μ.restrict (s ∩ e ⁻¹' (unitPartition.box n index : Set (Fin q → ℝ)))).prod τS)
    (htarget : (((π - ξ).map Prod.snd).restrict AT).map readT =
      (μ.restrict (s ∩ e ⁻¹' (unitPartition.box n index : Set (Fin q → ℝ)))).prod τT)
    (hbox : (μ (e ⁻¹' (unitPartition.box n index : Set (Fin q → ℝ))) * τS univ).toNNReal ≤ 1) :
    let R := Cst.refineSubplan ξ hξ
    let _instS := normalizedFiniteLaw_probability τS hτS
    let _instT := normalizedFiniteLaw_probability τT hτT
    let normalize := affineHaarCubeCoord e (fun l ↦ (index l : ℝ) / n) (n : ℝ≥0)⁻¹
    let p : unitInterval := ⟨(μ (e ⁻¹' (unitPartition.box n index : Set (Fin q → ℝ))) * τS univ).toNNReal,
      NNReal.coe_nonneg _, (by exact_mod_cast hbox)⟩
    (R.markedLaw N).map (Prod.map
      (fun x ↦ mapBlockData (Prod.map normalize id ∘ readS ∘ Prod.fst)
        (finiteOriginalRestrictedData (retainedMarkedCellEvent AS) x))
      (fun y ↦ mapBlockData (Prod.map normalize id ∘ readT ∘ Prod.fst)
        (finiteOriginalRestrictedData (retainedMarkedCellEvent AT) y))) =
      (binomialShapeBlockLaw q (normalizedFiniteLaw τS) N p (originalMicrocellShape e n index s)).prod
        (binomialShapeBlockLaw q (normalizedFiniteLaw τT) N p (originalMicrocellShape e n index s)) := by
  let R := Cst.refineSubplan ξ hξ
  letI := normalizedFiniteLaw_probability τS hτS
  letI := normalizedFiniteLaw_probability τT hτT
  letI : IsProbabilityMeasure (R.types.sourceMarkedLaw νS) := (R.types.marked_probabilities hπ).1
  letI : IsProbabilityMeasure (R.types.targetMarkedLaw νT) := (R.types.marked_probabilities hπ).2.1
  have hphysical := Cst.refineSubplan_retained_cell_observation_laws ξ hξ hAS hAT readS readT hmS hmT
  have hS := finiteOriginalRestrictedData_haar_shape_law (R.types.sourceMarkedLaw νS) N
    (measurableSet_retainedMarkedCellEvent hAS) (readS ∘ Prod.fst) (hmS.comp measurable_fst)
    μ e n index s hs τS hτS (hphysical.1.trans hsource) hbox
  have hT := finiteOriginalRestrictedData_haar_shape_law (R.types.targetMarkedLaw νT) N
    (measurableSet_retainedMarkedCellEvent hAT) (readT ∘ Prod.fst) (hmT.comp measurable_fst)
    μ e n index s hs τT hτT (hphysical.2.trans htarget) (by rwa [htotal])
  simp only [htotal] at hT
  let normalize := affineHaarCubeCoord e (fun l ↦ (index l : ℝ) / n) (n : ℝ≥0)⁻¹
  have hnormS : Measurable (Prod.map normalize (id : A → A)) :=
    (measurable_affineHaarCubeCoord e _ _).prodMap measurable_id
  have hnormT : Measurable (Prod.map normalize (id : B → B)) :=
    (measurable_affineHaarCubeCoord e _ _).prodMap measurable_id
  have hobsS : Measurable (fun x : Fin N → X × Option (Bool × T) ↦
      mapBlockData (Prod.map normalize id ∘ readS ∘ Prod.fst)
        (finiteOriginalRestrictedData (retainedMarkedCellEvent AS) x)) :=
    (measurable_mapBlockData (hnormS.comp (hmS.comp measurable_fst))).comp
      (measurable_finiteOriginalRestrictedData (measurableSet_retainedMarkedCellEvent hAS))
  have hobsT : Measurable (fun y : Fin N → Y × Option (Bool × T) ↦
      mapBlockData (Prod.map normalize id ∘ readT ∘ Prod.fst)
        (finiteOriginalRestrictedData (retainedMarkedCellEvent AT) y)) :=
    (measurable_mapBlockData (hnormT.comp (hmT.comp measurable_fst))).comp
      (measurable_finiteOriginalRestrictedData (measurableSet_retainedMarkedCellEvent hAT))
  dsimp only at hS hT ⊢
  rw [show R.markedLaw N = (Measure.pi (fun _ : Fin N ↦ R.types.sourceMarkedLaw νS)).prod
      (Measure.pi (fun _ : Fin N ↦ R.types.targetMarkedLaw νT)) from rfl,
    ← Measure.map_prod_map _ _ hobsS hobsT, hS, hT]

end OTSelector.Reconstruction
