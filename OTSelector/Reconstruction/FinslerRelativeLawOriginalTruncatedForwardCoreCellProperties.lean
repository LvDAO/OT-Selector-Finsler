import OTSelector.Reconstruction.FinslerRelativeLawOriginalForwardCoreCellAssembly
import OTSelector.Reconstruction.FinslerRelativeLawOriginalTruncatedFineCellPartition
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineCanonicalObservation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineTypeProperties
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCompactCanonicalFullAssignment
import OTSelector.Reconstruction.FinslerConcreteUpperFineEnergyBudget

/-! One original good/bad core packet gives forward retained cores in every fixed physical cell. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The SAME original fine packet assembles into physical cell cores. Every
edge has the literal retained flag, both original cell memberships, and the
old atlas forward clock gap. Total energy and total source defect keep their
single original good/bad budgets, without selecting a measurable core family. -/
theorem original_truncated_forward_cell_core_packet
    {X Z C T : Type*} [MetricSpace X] [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype C] [Fintype T] [DecidableEq T]
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
    {forwardGap : ℝ} (hgap : 0 < forwardGap)
    (hforward : ∀ t x y, D.sourceGood t x → D.targetGood t y → forwardGap ≤ u y - u x)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (G : Set Z) (hG : MeasurableSet G)
    (hcover : ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c)
    (K : T → C → Set (DyadicUnitCube q)) (hK : ∀ t c, MeasurableSet (K t c))
    (hsplit : let η := restrictOriginalRetainedResidual χ ξ a G
      let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
      let coord := fun t (p : X × X) ↦ D.sourceCoordinate t p.1
      ∀ t, D.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell K t +
        ∑ c, D.types.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell K c t =
          (D.types.rnSubplanTypes η hη).component (false, t))
    (n KG KB k : ℕ) :
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let coord := fun t (p : X × X) ↦ D.sourceCoordinate t p.1
    let good := D.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell K
    let bad := D.types.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell K
    let R := D.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    (∀ᵐ sample ∂P, ∃ coreGood coreBad : OTSelector.PartialMatching n n,
      (∀ e ∈ coreGood.edges, ∃ t,
        (sample.1 e.1).2.bind cellRefinedGoodType = some t ∧
        (sample.2 e.2).2.bind cellRefinedGoodType = some t ∧
        ∃ c, cellRefinedGoodCell a cell (sample.1 e.1) = some c ∧
          cellRefinedGoodCell a cell (sample.2 e.2) = some c) ∧
      (∀ e ∈ coreBad.edges, ∃ p : C × T,
        (sample.1 e.1).2.bind cellRefinedBadType = some p ∧
        (sample.2 e.2).2.bind cellRefinedBadType = some p) ∧
      coreGood.cost (fun i j ↦ cost (sample.1 i).1 (sample.2 j).1) ≤
        fineGoodHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KG sample ∧
      coreBad.cost (fun i j ↦ cost (sample.1 i).1 (sample.2 j).1) ≤
        fineBadHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KB sample ∧
      fineGoodSourceCount sample - (coreGood.card : ℝ) ≤
        fineGoodDiscrepancy D.sourceCoordinate D.targetCoordinate k sample ∧
      fineBadSourceCount sample - (coreBad.card : ℝ) ≤
        fineBadDiscrepancy D.sourceCoordinate D.targetCoordinate sample) →
    ∀ᵐ sample ∂P, ∃ family : C → OTSelector.PartialMatching n n,
      (∀ c e, e ∈ (family c).edges →
        subplanRetentionFlag ((sample.1 e.1).2.map cellRefinedSubplanType) = false ∧
        subplanRetentionFlag ((sample.2 e.2).2.map cellRefinedSubplanType) = false ∧
        a (sample.1 e.1).1 ∈ cell c ∧ a (sample.2 e.2).1 ∈ cell c ∧
        u (sample.1 e.1).1 < u (sample.2 e.2).1) ∧
      (∑ c, (family c).cost (fun i j ↦ cost (sample.1 i).1 (sample.2 j).1)) ≤
        fineGoodHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KG sample +
        fineBadHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KB sample ∧
      (∑ c, (partitionCount (fun i ↦ fineOriginalRetainedCellTag a cell (sample.1 i))
        (some c) - ((family c).card : ℝ))) ≤
        fineGoodDiscrepancy D.sourceCoordinate D.targetCoordinate k sample +
        fineBadDiscrepancy D.sourceCoordinate D.targetCoordinate sample := by
  let η := restrictOriginalRetainedResidual χ ξ a G
  let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
  let coord := fun t (p : X × X) ↦ D.sourceCoordinate t p.1
  let good := D.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell K
  let bad := D.types.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell K
  have hcoord t : Measurable (coord t) := (D.measurable_sourceCoordinate t).comp measurable_fst
  have hproper := D.rnCellRefinedTypes_iid_some η hη good bad hsplit hπ (I := Fin n) (J := Fin n)
  have hlabel : ∀ᵐ p ∂χ + ξ, a p.1 = a p.2 :=
    (original_calibrated_coupling_labels μ ν (χ + ξ) (χ + ξ) hπ le_rfl
      a u horder hμA hνA hcal).mono fun _ h ↦ h.1
  have hpartition := D.original_truncated_fine_cell_partition χ ξ hπ a ha hG
    cell hcell hcover hlabel good bad hsplit n
  have hbad := D.types.rnCellRefinedTypes_bad_cell_properties (μ := μ) (ν := ν)
    η hη good bad hsplit a a ha ha cell hcell hdisj
    (original_rn_compact_bad_joint_cells D.types η hη a ha hlabel coord hcoord cell hcell K hK) n
  have hfw := D.rnCellRefinedTypes_iid_old_forward η hη good bad hsplit u u forwardGap hforward
    (I := Fin n) (J := Fin n)
  dsimp only
  intro hcores
  filter_upwards [hcores, hproper, hpartition, hbad, hfw] with sample hc hp hpart hbCells hfw
  obtain ⟨g, b, hg, hb, hgc, hbc, hgd, hbd⟩ := hc
  obtain ⟨family, he, hcost, hdefect⟩ := exists_original_good_bad_cell_family_with_ancestry
    a a cell sample.1 sample.2 g b hg hb (fun i c t hi ↦ (hbCells.1 i c t hi).2)
    (fun j c t hj ↦ (hbCells.2 j c t hj).2) hp.1 hpart.1
  refine ⟨family, ?_, ?_, ?_⟩
  · intro c e hem
    obtain ⟨hs, ht, he⟩ := he c e hem
    have hs' := (fineOriginalRetainedCellTag_eq_some_iff_flag a cell hdisj _ c (hp.1 e.1)).mp hs
    have ht' := (fineOriginalRetainedCellTag_eq_some_iff_flag a cell hdisj _ c (hp.2 e.2)).mp ht
    refine ⟨hs'.1, ht'.1, hs'.2, ht'.2, ?_⟩
    rcases he with heg | heb
    · obtain ⟨t, hgs, hgt, _⟩ := hg e heg
      have hsTag := (cellRefinedGoodType_bind_some_iff _ _).mp hgs
      have htTag := (cellRefinedGoodType_bind_some_iff _ _).mp hgt
      have hgapEdge := hfw e.1 e.2 _ _ hsTag htTag rfl
      linarith
    · obtain ⟨p, hbs, hbt⟩ := hb e heb
      have hsTag := (cellRefinedBadType_bind_some_iff _ _).mp hbs
      have htTag := (cellRefinedBadType_bind_some_iff _ _).mp hbt
      have hgapEdge := hfw e.1 e.2 _ _ hsTag htTag rfl
      linarith
  · rw [hcost]
    exact add_le_add hgc hbc
  · rw [hdefect]
    exact add_le_add hgd hbd

end OTSelector.Reconstruction.PopulationTypedCostData
