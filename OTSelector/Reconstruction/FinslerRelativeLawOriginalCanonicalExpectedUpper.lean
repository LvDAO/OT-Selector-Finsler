import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineCellOptimizerIntegrability
import OTSelector.Finite.MeasurableIndexedGraph
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineRetainedProperties
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCompactCanonicalFullAssignment
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineTypeProperties
import OTSelector.Reconstruction.FinslerConcreteUpperFineEnergyBudget

/-! The actual original iid assignment mean is controlled by canonical retained costs,
the true original residual mass, and explicit square-root count repair. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false

/-- Original endpoint properties and the original atlas geometry suffice for the
canonical expected upper bound. All selected-core legality, canonical support,
source-defect, edge integrability and iid-expectation transfers are proved internally. -/
theorem original_compact_canonical_assignment_expectation_le
    {X Z C T : Type*} [MetricSpace X] [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (C × T))] [MeasurableSingletonClass (Option (C × T))]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling (χ + ξ) μ ν)
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (a : X → Z) (ha : Measurable a) (u : X → ℝ) {A : Set X}
    (horder : ∀ x ∈ A, ∀ y ∈ A, (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνA : ∀ᵐ y ∂ν, y ∈ A)
    (hcal : ∀ᵐ p ∂χ + ξ, u p.2 - u p.1 = dist p.1 p.2)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (compact : T → C → Set (DyadicUnitCube q))
    (hcompact : ∀ t c, MeasurableSet (compact t c))
    {k : ℕ} (hk : 0 < k)
    (hcarriers : let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c)
      let hη := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
      let coord := fun t (p : X × X) ↦ D.sourceCoordinate t p.1
      ∀ t, ∀ᵐ p ∂D.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell compact t,
        ∃ c, a p.1 ∈ cell c ∧ a p.2 ∈ cell c ∧
          D.sourceCoordinate t p.1 ∈ compact t c ∧ D.targetCoordinate t p.2 ∈ compact t c)
    (hsep : ∀ t c c', ∀ x ∈ compact t c, ∀ y ∈ compact t c',
      dyadicCubeCell k x = dyadicCubeCell k y → c = c')
    (Ps Pt : X → Prop) (hs : ∀ᵐ x ∂χ.map Prod.fst, Ps x)
    (ht : ∀ᵐ y ∂χ.map Prod.snd, Pt y)
    (legal : C → X → X → Prop)
    (hlegal : ∀ c, MeasurableSet {p : X × X | legal c p.1 p.2})
    (hcompatible : ∀ c t x y, D.sourceGood t x → D.targetGood t y → Ps x → Pt y →
      a x ∈ cell c → a y ∈ cell c → legal c x y)
    (model : ℝ → C → X → X → ℝ)
    (hmodel : ∀ tilt c, Measurable (Function.uncurry (model tilt c)))
    {n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (probe : X → X → ℝ) (hprobe : Measurable (Function.uncurry probe))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ p ∂μ.prod ν, |probe p.1 p.2| ≤ B) :
    let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c)
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
    let coord := fun t (p : X × X) ↦ D.sourceCoordinate t p.1
    let good := D.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell compact
    let bad := D.types.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell compact
    let hsplit := D.types.rn_truncated_compact_split χ ξ a ha cell hcell coord
      (fun t ↦ (D.measurable_sourceCoordinate t).comp measurable_fst) hdisj compact hcompact
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    ∀ tilt : ℝ,
    let actualCost := fun sample i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      cost (sample.1 i).1 (sample.2 j).1 + tilt * probe (sample.1 i).1 (sample.2 j).1
    let canonical := fun (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → X × Option (CellRefinedType C T))) c ↦ PartialMatching.firstLegalOptimalMatching
      (originalAmbientCellLegalGraph (fun i ↦ fineOriginalRetainedCellTag a cell (sample.1 i))
        (fun j ↦ fineOriginalRetainedCellTag a cell (sample.2 j))
        (originalFinePhysicalGraph legal sample) c)
      (fun i j ↦ model tilt c (sample.1 i).1 (sample.2 j).1)
    let retainedCost := fun sample ↦ ∑ c, (canonical sample c).cost (actualCost sample)
    let value := fun sample : (Fin n → X) × (Fin n → X) ↦ perturbedAssignmentValue
      (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i) (sample.2 j) +
        tilt * probe (sample.1 i) (sample.2 j)) 0 0
    Integrable value P₀ ∧ Integrable retainedCost P ∧
    (∫ sample, value sample ∂P₀) / (n : ℝ) ≤
      (∫ sample, retainedCost sample ∂P) / (n : ℝ) +
      (D.quadraticConstant * dyadicMatchingConstant q *
        (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * (η univ).toReal ^ (1 - 2 / (q : ℝ)) +
      D.globalBound * Real.sqrt (2 * Fintype.card T) *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (η univ).toReal +
      2 * |tilt| * B * (η univ).toReal) +
      ((n : ℝ) ^ (2 / (q : ℝ)) * D.globalBound + |tilt| * B) *
        (((Fintype.card T : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ k + 1) ^ q) +
          (Fintype.card (C × T) : ℝ) *
            Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q)) / (n : ℝ) +
          Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (Bool × T))) / (n : ℝ)) := by
  let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c)
  let hη := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
  let coord := fun t (p : X × X) ↦ D.sourceCoordinate t p.1
  let good := D.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell compact
  let bad := D.types.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell compact
  have hcoord t : Measurable (coord t) := (D.measurable_sourceCoordinate t).comp measurable_fst
  have hsplit := D.types.rn_truncated_compact_split χ ξ a ha cell hcell coord hcoord
    hdisj compact hcompact
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
  obtain ⟨K, hpressure, hcount, hfull⟩ :=
    D.exists_original_truncated_compact_canonical_full_assignment χ ξ hπ a ha u
      horder hμA hνA hcal cell hcell hdisj compact hcompact hq hn probe hprobe hB hb
  obtain ⟨KG, KB, hKG, hKB, hEI, hEbound, hDI, hDbound, hcores⟩ :=
    D.exists_original_good_bad_expected_core_packet η hη good bad hsplit hq hn hk hπ
      a a ha ha cell hcell hdisj compact hcompact hcarriers hsep
  have hold := D.rnCellRefinedTypes_iid_old_properties η hη good bad hsplit
    (I := Fin n) (J := Fin n)
  have hret := D.original_truncated_fine_retained_endpoint_properties χ ξ a ha
    (MeasurableSet.iUnion hcell) good bad hsplit Ps Pt hs ht (I := Fin n) (J := Fin n)
  have hlabel : ∀ᵐ p ∂χ + ξ, a p.1 = a p.2 :=
    (original_calibrated_coupling_labels μ ν (χ + ξ) (χ + ξ) hπ le_rfl
      a u horder hμA hνA hcal).mono fun _ h ↦ h.1
  have hbad := D.types.rnCellRefinedTypes_bad_cell_properties (μ := μ) (ν := ν)
    η hη good bad hsplit a a ha ha cell hcell hdisj
    (original_rn_compact_bad_joint_cells D.types η hη a ha hlabel coord hcoord
      cell hcell compact hcompact) n
  dsimp only
  intro tilt
  let actualCost := fun (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → X × Option (CellRefinedType C T))) i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      cost (sample.1 i).1 (sample.2 j).1 + tilt * probe (sample.1 i).1 (sample.2 j).1
  let canonical := fun (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → X × Option (CellRefinedType C T))) c ↦ PartialMatching.firstLegalOptimalMatching
    (originalAmbientCellLegalGraph (fun i ↦ fineOriginalRetainedCellTag a cell (sample.1 i))
      (fun j ↦ fineOriginalRetainedCellTag a cell (sample.2 j))
      (originalFinePhysicalGraph legal sample) c)
    (fun i j ↦ model tilt c (sample.1 i).1 (sample.2 j).1)
  let retainedCost := fun sample ↦ ∑ c, (canonical sample c).cost (actualCost sample)
  let value := fun sample : (Fin n → X) × (Fin n → X) ↦ perturbedAssignmentValue
    (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i) (sample.2 j) +
      tilt * probe (sample.1 i) (sample.2 j)) 0 0
  let pressure := fun (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → X × Option (CellRefinedType C T))) ↦ D.originalResidualPressureBudget η hη n K probe tilt
    (cellRefinedSubplanObservation sample)
  let count := fun (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → X × Option (CellRefinedType C T))) ↦ D.originalResidualCountBudget η hη n
    (cellRefinedSubplanObservation sample)
  let discrepancy := fun (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → X × Option (CellRefinedType C T))) ↦ fineGoodDiscrepancy D.sourceCoordinate D.targetCoordinate k sample +
    fineBadDiscrepancy D.sourceCoordinate D.targetCoordinate sample
  let completionBound := (n : ℝ) ^ (2 / (q : ℝ)) * D.globalBound + |tilt| * B
  have hcompletion : 0 ≤ completionBound := add_nonneg
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) D.bound_nonneg)
    (mul_nonneg (abs_nonneg tilt) hB)
  have hvalue := D.rnCellRefinedTypes_original_tilted_assignment_integral η hη good bad hsplit
    hπ n probe hprobe hb tilt
  have hcost : Integrable retainedCost P :=
    D.rnCellRefinedTypes_canonical_cell_cost_integrable η hη good bad hsplit hπ n a a ha ha
      cell hcell hdisj (originalFinePhysicalGraph legal)
      (measurableSet_originalFinePhysicalGraph_eq legal hlegal)
      (fun sample c i j ↦ model tilt c (sample.1 i).1 (sample.2 j).1)
      (fun c i j ↦ (hmodel tilt c).comp (show Measurable (fun sample :
        (Fin n → X × Option (CellRefinedType C T)) ×
          (Fin n → X × Option (CellRefinedType C T)) ↦
            ((sample.1 i).1, (sample.2 j).1)) by fun_prop)) probe hprobe hb tilt
  refine ⟨hvalue.1, hcost, ?_⟩
  have hpoint : ∀ᵐ sample ∂P,
      value ((fun i ↦ (sample.1 i).1), (fun j ↦ (sample.2 j).1)) ≤
        retainedCost sample + pressure sample + completionBound * (discrepancy sample + count sample) := by
    filter_upwards [hfull, hcores, hold, hret, hbad] with sample hfull hc ho hr hbCells
    obtain ⟨g, b, hg, hbCore, _, _, hgd, hbd⟩ := hc
    have hgLegal : ∀ c e, e ∈ g.edges →
        fineOriginalRetainedCellTag a cell (sample.1 e.1) = some c →
          e ∈ originalFinePhysicalGraph legal sample c := by
      intro c e he hsource
      obtain ⟨t, hgs, hgt, d, hds, hdt⟩ := hg e he
      have hxs := (cellRefinedGoodType_bind_some_iff _ _).mp hgs
      have hyt := (cellRefinedGoodType_bind_some_iff _ _).mp hgt
      have htarget : fineOriginalRetainedCellTag a cell (sample.2 e.2) = some c := by
        have hs' := (fineOriginalRetainedCellTag_eq_goodCell a cell _ hgs).trans hds
        have hdc : d = c := Option.some.inj (hs'.symm.trans hsource)
        exact (fineOriginalRetainedCellTag_eq_goodCell a cell _ hgt).trans (hdc ▸ hdt)
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hcompatible c t _ _ ?_ ?_ ?_ ?_ ?_ ?_⟩
      · exact ho.1 _ _ hxs
      · exact ho.2 _ _ hyt
      · apply hr.1 e.1
        simp only [hxs, Option.map_some, cellRefinedSubplanType, Bool.not_true]
        rfl
      · apply hr.2 e.2
        simp only [hyt, Option.map_some, cellRefinedSubplanType, Bool.not_true]
        rfl
      · exact ((fineOriginalRetainedCellTag_eq_some_iff a cell hdisj _ c).mp hsource).2
      · exact ((fineOriginalRetainedCellTag_eq_some_iff a cell hdisj _ c).mp htarget).2
    have hbLegal : ∀ c e, e ∈ b.edges →
        fineOriginalRetainedCellTag a cell (sample.1 e.1) = some c →
          e ∈ originalFinePhysicalGraph legal sample c := by
      intro c e he hsource
      obtain ⟨⟨d,t⟩, hbs, hbt⟩ := hbCore e he
      have hxs := (cellRefinedBadType_bind_some_iff _ _).mp hbs
      have hyt := (cellRefinedBadType_bind_some_iff _ _).mp hbt
      have hds := (hbCells.1 e.1 d t hbs).2
      have hdt := (hbCells.2 e.2 d t hbt).2
      have hdc : d = c := Option.some.inj (hds.symm.trans hsource)
      have htarget := hdc ▸ hdt
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hcompatible c t _ _ ?_ ?_ ?_ ?_ ?_ ?_⟩
      · exact ho.1 _ _ hxs
      · exact ho.2 _ _ hyt
      · apply hr.1 e.1
        simp only [hxs, Option.map_some, cellRefinedSubplanType]
        rfl
      · apply hr.2 e.2
        simp only [hyt, Option.map_some, cellRefinedSubplanType]
        rfl
      · exact ((fineOriginalRetainedCellTag_eq_some_iff a cell hdisj _ c).mp hsource).2
      · exact ((fineOriginalRetainedCellTag_eq_some_iff a cell hdisj _ c).mp htarget).2
    obtain ⟨full, hf⟩ := hfull tilt (originalFinePhysicalGraph legal sample)
      (fun c i j ↦ model tilt c (sample.1 i).1 (sample.2 j).1) g b hg hbCore hgLegal hbLegal
    apply (perturbedAssignmentValue_le _ 0 0 full).trans
    have hdefect : (fineGoodSourceCount sample - g.card) + (fineBadSourceCount sample - b.card) ≤
        discrepancy sample := add_le_add hgd hbd
    have hf' : assignmentCost (actualCost sample) full ≤ retainedCost sample + pressure sample +
        completionBound * ((fineGoodSourceCount sample - g.card) +
          (fineBadSourceCount sample - b.card) + count sample) := hf
    rw [perturbedEdgeCost_zero]
    exact hf'.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add hdefect le_rfl) hcompletion))
  have hint := integral_mono_ae hvalue.2.1
    ((hcost.add (hpressure tilt).1).add ((hDI.add hcount.1).const_mul completionBound)) hpoint
  have hsum := integral_add (hcost.add (hpressure tilt).1)
    ((hDI.add hcount.1).const_mul completionBound)
  have hsumRet := integral_add hcost (hpressure tilt).1
  have hsumCount := integral_add hDI hcount.1
  simp only [Pi.add_apply] at hsum hsumRet hsumCount
  rw [hsumRet, integral_const_mul, hsumCount] at hsum
  change (∫ sample, value ((fun i ↦ (sample.1 i).1), (fun j ↦ (sample.2 j).1)) ∂P) ≤
    ∫ sample, retainedCost sample + pressure sample +
      completionBound * (discrepancy sample + count sample) ∂P at hint
  rw [hsum] at hint
  have htransfer := hvalue.2.2
  change (∫ sample, value ((fun i ↦ (sample.1 i).1), (fun j ↦ (sample.2 j).1)) ∂P) =
    ∫ sample, value sample ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod
      (Measure.pi (fun _ : Fin n ↦ ν)) at htransfer
  rw [htransfer] at hint
  have hnormalized := (div_le_div_of_nonneg_right hint (Nat.cast_nonneg n)).trans_eq
    (show _ = (∫ sample, retainedCost sample ∂P) / (n : ℝ) +
      (∫ sample, pressure sample ∂P) / (n : ℝ) + completionBound *
        ((∫ sample, discrepancy sample ∂P) / (n : ℝ) +
          (∫ sample, count sample ∂P) / (n : ℝ)) by ring)
  apply hnormalized.trans
  apply add_le_add
  · apply add_le_add le_rfl
    calc
      _ = (1 / (n : ℝ)) * (∫ sample, pressure sample ∂P) := by ring
      _ ≤ _ := (hpressure tilt).2
  · exact mul_le_mul_of_nonneg_left
      (add_le_add (div_le_div_of_nonneg_right hDbound (Nat.cast_nonneg n))
        (div_le_div_of_nonneg_right hcount.2 (Nat.cast_nonneg n))) hcompletion

end OTSelector.Reconstruction.PopulationTypedCostData
