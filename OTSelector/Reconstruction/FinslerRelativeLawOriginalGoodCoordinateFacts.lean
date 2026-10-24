import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.FinslerRelativeLawOriginalGoodCoordinateLaw

/-! Actual iid and selected-good quadratic inputs for the original-T hierarchy. -/
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
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- All selected-good quadratic estimates use the original old-type constants.
No bound is imposed on the none coordinate in this good-only observation. -/
theorem rnCellRefinedTypes_good_quadratic (n : ℕ) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let xs := fun i (sample : (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → Y × Option (CellRefinedType C T))) ↦
      populationFineGoodCoordinate D.sourceCoordinate (cubeOrigin (q := q)) (sample.1 i)
    let ys := fun j (sample : (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → Y × Option (CellRefinedType C T))) ↦
      populationFineGoodCoordinate D.targetCoordinate (cubeOrigin (q := q)) (sample.2 j)
    ∀ t, ∀ᵐ sample ∂P, ∀ i j, (xs i sample).1 = some t → (ys j sample).1 = some t →
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
  have hsi := (cellRefinedGoodType_bind_some_iff (sample.1 i).2 t).mp hi
  have htj := (cellRefinedGoodType_bind_some_iff (sample.2 j).2 t).mp hj
  have h := D.quadratic t _ _ (hgood.1 i (.inl (true, t)) hsi)
    (hgood.2 j (.inl (true, t)) htj)
  simpa only [populationFineGoodCoordinate, populationTypedCoordinate, hsi, htj,
    Option.bind_some, cellRefinedGoodType, ↓reduceIte, Option.elim_some] using h


/-- Original global cost bounds hold on the same fine experiment's physical points. -/
theorem rnCellRefinedTypes_cost_bounds (hπ : Vlasov.IsCoupling π μ ν) (n : ℕ) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    ∀ᵐ sample ∂P, ∀ i j,
      0 ≤ cost (sample.1 i).1 (sample.2 j).1 ∧
        cost (sample.1 i).1 (sample.2 j).1 ≤ D.globalBound := by
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
  letI : MeasurableSpace (Option (Bool × T)) := ⊤
  letI : MeasurableSingletonClass (Option (Bool × T)) := ⟨fun _ ↦ trivial⟩
  let dropX := fun sample : Fin n → X × Option (CellRefinedType C T) ↦
    fun i ↦ ((sample i).1, (sample i).2.map cellRefinedOldType)
  let dropY := fun sample : Fin n → Y × Option (CellRefinedType C T) ↦
    fun j ↦ ((sample j).1, (sample j).2.map cellRefinedOldType)
  have hx : Measurable dropX := measurable_pi_lambda _ (fun i ↦
    ((measurable_pi_apply i).fst).prodMk ((measurable_of_countable
      (Option.map (cellRefinedOldType (C := C) (T := T)))).comp (measurable_pi_apply i).snd))
  have hy : Measurable dropY := measurable_pi_lambda _ (fun j ↦
    ((measurable_pi_apply j).fst).prodMk ((measurable_of_countable
      (Option.map (cellRefinedOldType (C := C) (T := T)))).comp (measurable_pi_apply j).snd))
  have hm := D.types.rnCellRefinedTypes_iid_old_law (I := Fin n) (J := Fin n)
    η hη good bad hsplit μ ν
  have hb : ∀ᵐ sample ∂P.map (Prod.map dropX dropY),
      ∀ i j, 0 ≤ cost (sample.1 i).1 (sample.2 j).1 ∧
        cost (sample.1 i).1 (sample.2 j).1 ≤ D.globalBound := by
    dsimp only [P]
    rw [hm]
    filter_upwards [(D.iid_cost_bounds hπ n).1, (D.iid_cost_bounds hπ n).2] with sample hn hb
    exact fun i j ↦ ⟨hn i j, hb i j⟩
  exact ae_of_ae_map (hx.prodMap hy).aemeasurable hb

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
/-- All raw iid and cross-color independence facts are produced from the same fine experiment,
with the actual common good coordinate law and no common-law premise. -/
theorem rnCellRefinedTypes_good_iid_facts [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) (n : ℕ) :
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let G := D.types.rnCellGoodTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let L := G.typeCoordinateLaw μ D.sourceCoordinate (cubeOrigin (q := q))
    let xs := fun i (sample : (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → Y × Option (CellRefinedType C T))) ↦
      populationFineGoodCoordinate D.sourceCoordinate (cubeOrigin (q := q)) (sample.1 i)
    let ys := fun j (sample : (Fin n → X × Option (CellRefinedType C T)) ×
        (Fin n → Y × Option (CellRefinedType C T))) ↦
      populationFineGoodCoordinate D.targetCoordinate (cubeOrigin (q := q)) (sample.2 j)
    IsProbabilityMeasure P ∧ IsProbabilityMeasure L ∧
      (∀ i, Measurable (xs i)) ∧ (∀ j, Measurable (ys j)) ∧
      iIndepFun xs P ∧ iIndepFun ys P ∧
      (∀ i, P.map (xs i) = L) ∧ (∀ j, P.map (ys j) = L) ∧
      IndepFun (fun sample i ↦ xs i sample) (fun sample j ↦ ys j sample) P := by
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let G := D.types.rnCellGoodTypes η hη good bad hsplit
  have hp := R.marked_probabilities hπ
  let : IsProbabilityMeasure (R.sourceMarkedLaw μ) := hp.1
  let : IsProbabilityMeasure (R.targetMarkedLaw ν) := hp.2.1
  let : IsProbabilityMeasure (G.typeCoordinateLaw μ D.sourceCoordinate (cubeOrigin (q := q))) :=
    G.typeCoordinateLaw_isProbability hπ _ _ D.measurable_sourceCoordinate
  have has := measurable_populationFineGoodCoordinate (C := C) D.sourceCoordinate
    (cubeOrigin (q := q)) D.measurable_sourceCoordinate
  have hat := measurable_populationFineGoodCoordinate (C := C) D.targetCoordinate
    (cubeOrigin (q := q)) D.measurable_targetCoordinate
  have hx : Measurable (fun sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → Y × Option (CellRefinedType C T)) ↦
      fun i ↦ populationFineGoodCoordinate D.sourceCoordinate (cubeOrigin (q := q)) (sample.1 i)) :=
    measurable_pi_lambda _ (fun i ↦ has.comp ((measurable_pi_apply i).comp measurable_fst))
  have hy : Measurable (fun sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → Y × Option (CellRefinedType C T)) ↦
      fun j ↦ populationFineGoodCoordinate D.targetCoordinate (cubeOrigin (q := q)) (sample.2 j)) :=
    measurable_pi_lambda _ (fun j ↦ hat.comp ((measurable_pi_apply j).comp measurable_snd))
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro i; exact (measurable_pi_apply i).comp hx
  · intro j; exact (measurable_pi_apply j).comp hy
  · exact iid_facts_of_array_product_law _ _ _ _ hx hy
      (D.rnCellRefinedTypes_good_coordinate_joint_law η hη good bad hsplit hπ)

end OTSelector.Reconstruction.PopulationTypedCostData
