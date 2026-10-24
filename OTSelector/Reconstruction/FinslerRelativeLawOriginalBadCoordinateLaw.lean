import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellBadMarkObservation
import OTSelector.Reconstruction.FinslerPopulationTypedCostData

/-! The cell/old-type bad hierarchy reads actual old coordinates from the same fine experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-- Read the old coordinate only from a bad retained fine mark. -/
def populationFineBadCoordinate {X Z C T : Type*} (coord : C × T → X → Z) (origin : Z)
    (p : X × Option (CellRefinedType C T)) : Option (C × T) × Z :=
  populationTypedCoordinate coord origin (p.1, p.2.bind cellRefinedBadType)

theorem measurable_populationFineBadCoordinate {X Z C T : Type*}
    [MeasurableSpace X] [MeasurableSpace Z] [Fintype C] [Fintype T]
    [MeasurableSpace (Option (C × T))] [MeasurableSingletonClass (Option (C × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (coord : C × T → X → Z) (origin : Z) (hm : ∀ t, Measurable (coord t)) :
    Measurable (populationFineBadCoordinate (C := C) coord origin) := by
  apply (measurable_populationTypedCoordinate coord origin hm).comp
  exact measurable_fst.prodMk ((measurable_of_countable
    (fun t : Option (CellRefinedType C T) ↦ t.bind cellRefinedBadType)).comp measurable_snd)

namespace PopulationTypedCostData
variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))

/-- Paired original coordinates give the bad source/target common coordinate law internally. -/
theorem rnCellBadTypes_common_coordinate (t : C × T) :
    let G := D.types.rnCellBadTypes η hη good bad hsplit
    (G.source t).map (D.sourceCoordinate t.2) = (G.target t).map (D.targetCoordinate t.2) := by
  dsimp only
  rw [PopulationSubcouplingTypes.source, PopulationSubcouplingTypes.target,
    Measure.map_map (D.measurable_sourceCoordinate t.2) measurable_fst,
    Measure.map_map (D.measurable_targetCoordinate t.2) measurable_snd]
  exact Measure.map_congr (ae_mono (D.types.rnCellBadTypes_component_le_old η hη good bad hsplit t)
    (D.paired_coordinate t.2))

variable [MeasurableSpace (Option (C × T))] [MeasurableSingletonClass (Option (C × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- The bad hierarchy reads its entire coordinate array from the original fine sample. -/
theorem rnCellRefinedTypes_bad_coordinate_joint_law {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let G := D.types.rnCellBadTypes η hη good bad hsplit
    let L := G.typeCoordinateLaw μ (fun p : C × T ↦ D.sourceCoordinate p.2) (cubeOrigin (q := q))
    ((Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν))).map
        (Prod.map (fun sample i ↦ populationFineBadCoordinate
            (fun p : C × T ↦ D.sourceCoordinate p.2)
           
      (cubeOrigin (q := q)) (sample i))
          (fun sample j ↦ populationFineBadCoordinate (fun p : C × T ↦ D.targetCoordinate p.2)
           
      (cubeOrigin (q := q)) (sample j))) =
      (Measure.pi (fun _ : I ↦ L)).prod (Measure.pi (fun _ : J ↦ L)) := by
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let G := D.types.rnCellBadTypes η hη good bad hsplit
  let dropX := fun sample : I → X × Option (CellRefinedType C T) ↦
    fun i ↦ ((sample i).1, (sample i).2.bind cellRefinedBadType)
  let dropY := fun sample : J → Y × Option (CellRefinedType C T) ↦
    fun j ↦ ((sample j).1, (sample j).2.bind cellRefinedBadType)
  let readX := fun sample : I → X × Option (C × T) ↦
    fun i ↦ populationTypedCoordinate (fun p : C × T ↦ D.sourceCoordinate p.2)
      (cubeOrigin (q := q)) (sample i)
  let readY := fun sample : J → Y × Option (C × T) ↦
    fun j ↦ populationTypedCoordinate (fun p : C × T ↦ D.targetCoordinate p.2)
      (cubeOrigin (q := q)) (sample j)
  have hdropX : Measurable dropX := measurable_pi_lambda _ (fun i ↦
    (((measurable_pi_apply i).fst).prodMk ((measurable_of_countable
      (fun t : Option (CellRefinedType C T) ↦ t.bind cellRefinedBadType)).comp
        (measurable_pi_apply i).snd)))
  have hdropY : Measurable dropY := measurable_pi_lambda _ (fun j ↦
    (((measurable_pi_apply j).fst).prodMk ((measurable_of_countable
      (fun t : Option (CellRefinedType C T) ↦ t.bind cellRefinedBadType)).comp
        (measurable_pi_apply j).snd)))
  have hreadX : Measurable readX := measurable_pi_lambda _ (fun i ↦
    (measurable_populationTypedCoordinate _ _
      (fun p : C × T ↦ D.measurable_sourceCoordinate p.2)).comp
      (measurable_pi_apply i))
  have hreadY : Measurable readY := measurable_pi_lambda _ (fun j ↦
    (measurable_populationTypedCoordinate _ _
      (fun p : C × T ↦ D.measurable_targetCoordinate p.2)).comp
      (measurable_pi_apply j))
  have h := congrArg (fun ρ ↦ ρ.map (Prod.map readX readY))
    (D.types.rnCellRefinedTypes_iid_bad_law (I := I) (J := J) η hη good bad hsplit hπ)
  rw [Measure.map_map (hreadX.prodMap hreadY) (hdropX.prodMap hdropY)] at h
  exact h.trans (G.iid_type_coordinate_law hπ
    (fun p : C × T ↦ D.sourceCoordinate p.2) (fun p : C × T ↦ D.targetCoordinate p.2)
    (cubeOrigin (q := q)) (fun p : C × T ↦ D.measurable_sourceCoordinate p.2)
    (fun p : C × T ↦ D.measurable_targetCoordinate p.2)
      (D.rnCellBadTypes_common_coordinate η hη good bad hsplit))

end PopulationTypedCostData
end OTSelector.Reconstruction
