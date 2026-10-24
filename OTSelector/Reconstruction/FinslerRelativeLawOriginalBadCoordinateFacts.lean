import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.FinslerRelativeLawOriginalBadCoordinateLaw

/-! Actual iid and selected-bad quadratic inputs for the cell/old-type hierarchy. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
    (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
    [MeasurableSpace (Option (C × T))] [MeasurableSingletonClass (Option (C × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- All selected-bad quadratic estimates use the original old-type constants.
No bound is imposed on the none coordinate in this bad-only observation. -/
theorem rnCellRefinedTypes_bad_quadratic (n : ℕ) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let xs := fun i (sample : (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → Y × Option (CellRefinedType C T))) ↦
      populationFineBadCoordinate (fun p : C × T ↦ D.sourceCoordinate p.2)
        (cubeOrigin (q := q)) (sample.1 i)
    let ys := fun j (sample : (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → Y × Option (CellRefinedType C T))) ↦
      populationFineBadCoordinate (fun p : C × T ↦ D.targetCoordinate p.2)
        (cubeOrigin (q := q)) (sample.2 j)
    ∀ t : C × T, ∀ᵐ sample ∂P, ∀ i j, (xs i sample).1 = some t → (ys j sample).1 = some t →
      cost (sample.1 i).1 (sample.2 j).1 ≤ D.quadraticConstant *
        ‖dyadicCubePoint (xs i sample).2 - dyadicCubePoint (ys j sample).2‖ ^ 2 := by
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  have hs (tag : CellRefinedType C T) :
      ∀ᵐ x ∂R.source tag, D.sourceGood (cellRefinedOldType tag) x :=
    ae_mono (Measure.map_mono
      (D.types.rnCellRefinedTypes_component_le_old η hη good bad hsplit tag) measurable_fst)
      (D.source_good _)
  have ht (tag : CellRefinedType C T) :
      ∀ᵐ y ∂R.target tag, D.targetGood (cellRefinedOldType tag) y :=
    ae_mono (Measure.map_mono
      (D.types.rnCellRefinedTypes_component_le_old η hη good bad hsplit tag) measurable_snd)
      (D.target_good _)
  have hg := R.iid_marked_type_properties (μ := μ) (ν := ν) (I := Fin n) (J := Fin n)
    (fun tag ↦ D.sourceGood (cellRefinedOldType tag))
    (fun tag ↦ D.targetGood (cellRefinedOldType tag)) hs ht
  dsimp only
  intro t
  filter_upwards [hg] with sample hgood
  intro i j hi hj
  have hsi := (cellRefinedBadType_bind_some_iff (sample.1 i).2 t).mp hi
  have htj := (cellRefinedBadType_bind_some_iff (sample.2 j).2 t).mp hj
  have h := D.quadratic t.2 _ _ (hgood.1 i (.inr t) hsi)
    (hgood.2 j (.inr t) htj)
  simpa only [populationFineBadCoordinate, populationTypedCoordinate, hsi, htj,
    Option.bind_some, cellRefinedBadType, Option.elim_some] using h


omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
/-- All raw iid and cross-color independence facts are produced from the same fine experiment,
with the actual common bad coordinate law and no common-law premise. -/
theorem rnCellRefinedTypes_bad_iid_facts [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) (n : ℕ) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let G := D.types.rnCellBadTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let L := G.typeCoordinateLaw μ (fun p : C × T ↦ D.sourceCoordinate p.2) (cubeOrigin (q := q))
    let xs := fun i (sample : (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → Y × Option (CellRefinedType C T))) ↦
      populationFineBadCoordinate (fun p : C × T ↦ D.sourceCoordinate p.2)
        (cubeOrigin (q := q)) (sample.1 i)
    let ys := fun j (sample : (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → Y × Option (CellRefinedType C T))) ↦
      populationFineBadCoordinate (fun p : C × T ↦ D.targetCoordinate p.2)
        (cubeOrigin (q := q)) (sample.2 j)
    IsProbabilityMeasure P ∧ IsProbabilityMeasure L ∧
      (∀ i, Measurable (xs i)) ∧ (∀ j, Measurable (ys j)) ∧
      iIndepFun xs P ∧ iIndepFun ys P ∧
      (∀ i, P.map (xs i) = L) ∧ (∀ j, P.map (ys j) = L) ∧
      IndepFun (fun sample i ↦ xs i sample) (fun sample j ↦ ys j sample) P := by
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let G := D.types.rnCellBadTypes η hη good bad hsplit
  have hp := R.marked_probabilities hπ
  let : IsProbabilityMeasure (R.sourceMarkedLaw μ) := hp.1
  let : IsProbabilityMeasure (R.targetMarkedLaw ν) := hp.2.1
  let : IsProbabilityMeasure
      (G.typeCoordinateLaw μ (fun p : C × T ↦ D.sourceCoordinate p.2) (cubeOrigin (q := q))) :=
    G.typeCoordinateLaw_isProbability hπ _ _ (fun p : C × T ↦ D.measurable_sourceCoordinate p.2)
  have has := measurable_populationFineBadCoordinate (C := C)
    (fun p : C × T ↦ D.sourceCoordinate p.2)
    (cubeOrigin (q := q)) (fun p : C × T ↦ D.measurable_sourceCoordinate p.2)
  have hat := measurable_populationFineBadCoordinate (C := C)
    (fun p : C × T ↦ D.targetCoordinate p.2)
    (cubeOrigin (q := q)) (fun p : C × T ↦ D.measurable_targetCoordinate p.2)
  have hx : Measurable (fun sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → Y × Option (CellRefinedType C T)) ↦
      fun i ↦ populationFineBadCoordinate (fun p : C × T ↦ D.sourceCoordinate p.2)
        (cubeOrigin (q := q)) (sample.1 i)) :=
    measurable_pi_lambda _ (fun i ↦ has.comp ((measurable_pi_apply i).comp measurable_fst))
  have hy : Measurable (fun sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → Y × Option (CellRefinedType C T)) ↦
      fun j ↦ populationFineBadCoordinate (fun p : C × T ↦ D.targetCoordinate p.2)
        (cubeOrigin (q := q)) (sample.2 j)) :=
    measurable_pi_lambda _ (fun j ↦ hat.comp ((measurable_pi_apply j).comp measurable_snd))
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro i; exact (measurable_pi_apply i).comp hx
  · intro j; exact (measurable_pi_apply j).comp hy
  · exact iid_facts_of_array_product_law _ _ _ _ hx hy
      (D.rnCellRefinedTypes_bad_coordinate_joint_law η hη good bad hsplit hπ)

end OTSelector.Reconstruction.PopulationTypedCostData
