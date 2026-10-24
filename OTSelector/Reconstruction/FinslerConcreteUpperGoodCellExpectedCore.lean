import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.FinslerConcreteUpperHierarchyCellExpectation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalGoodCellProperties

/-! The compact good components of the actual original population have one
old-type expected energy budget on the same finely marked original iid sample.
All iid, quadratic, boundedness, and color inputs are discharged internally. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X Y Z C T : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
  (η : Measure (X × Y)) (hη : η ≤ π)
  (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
  (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  [MeasurableSpace (Option (CellRefinedType C T))]
  [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- Actual original good marked clouds receive the global same-cell core
without a sample-law, quadratic, or histogram assumption. -/
theorem exists_original_good_cell_core_expected_energy
    {n k : ℕ} (hq : 4 < q) (hn : 0 < n) (hk : 0 < k)
    (hπ : Vlasov.IsCoupling π μ ν) (left : X → Z) (right : Y → Z)
    (hleft : Measurable left) (hright : Measurable right)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (compact : T → C → Set (DyadicUnitCube q))
    (hcompact : ∀ t c, MeasurableSet (compact t c))
    (hcarriers : ∀ t, ∀ᵐ p ∂good t, ∃ c,
      left p.1 ∈ cell c ∧ right p.2 ∈ cell c ∧
        D.sourceCoordinate t p.1 ∈ compact t c ∧ D.targetCoordinate t p.2 ∈ compact t c)
    (hsep : ∀ t c c', ∀ x ∈ compact t c, ∀ y ∈ compact t c',
      dyadicCubeCell k x = dyadicCubeCell k y → c = c') :
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
    let S := presentTypeTags T
    let sourceCell := fun sample i ↦ cellRefinedGoodCell left cell (sample.1 i)
    let targetCell := fun sample j ↦ cellRefinedGoodCell right cell (sample.2 j)
    let cost := fun sample i j ↦ cost (sample.1 i).1 (sample.2 j).1
    ∃ K : ℕ, k ≤ K ∧
      (Integrable (fun sample ↦ attributedTypesEnergy S (fun i ↦ xs i sample)
        (fun j ↦ ys j sample) (cost sample) (taggedHierarchyAssignment K xs ys sample)) P ∧
      ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
        (∫ sample, attributedTypesEnergy S (fun i ↦ xs i sample) (fun j ↦ ys j sample)
          (cost sample) (taggedHierarchyAssignment K xs ys sample) ∂P) ≤
        D.quadraticConstant * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) *
          (∑ t, good t Set.univ).toReal ^ (1 - 2 / (q : ℝ)) +
        D.globalBound * Real.sqrt (2 * Fintype.card T) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) *
          Real.sqrt (∑ t, good t Set.univ).toReal) ∧
      (Integrable (fun sample ↦ ∑ t ∈ S,
        taggedDyadicDiscrepancy t k (fun i ↦ xs i sample) (fun j ↦ ys j sample)) P ∧
      (∫ sample, ∑ t ∈ S, taggedDyadicDiscrepancy t k
        (fun i ↦ xs i sample) (fun j ↦ ys j sample) ∂P) ≤
        ∑ t ∈ S, Real.sqrt (2 * (n : ℝ) * L.real {x | x.1 = t} * ((2 : ℝ) ^ k + 1) ^ q)) ∧
      ∀ᵐ sample ∂P, ∃ core : OTSelector.PartialMatching n n,
        (∀ e ∈ core.edges,
          (xs e.1 sample).1 ∈ S ∧ (xs e.1 sample).1 = (ys e.2 sample).1 ∧
          ∃ c, sourceCell sample e.1 = some c ∧ targetCell sample e.2 = some c) ∧
        core.cost (cost sample) ≤ attributedTypesEnergy S (fun i ↦ xs i sample)
          (fun j ↦ ys j sample) (cost sample) (taggedHierarchyAssignment K xs ys sample) ∧
        (∑ t ∈ S, partitionCount (fun i ↦ (xs i sample).1) t) - (core.card : ℝ) ≤
          ∑ t ∈ S, taggedDyadicDiscrepancy t k
            (fun i ↦ xs i sample) (fun j ↦ ys j sample) := by
  classical
  letI : MeasurableSpace (Option (C × T)) := ⊤
  letI : MeasurableSingletonClass (Option (C × T)) := ⟨fun _ ↦ trivial⟩
  obtain ⟨hP, hL, hx, hy, hxi, hyi, hxl, hyl, hxy⟩ :=
    D.rnCellRefinedTypes_good_iid_facts η hη good bad hsplit hπ n
  letI := hP
  letI := hL
  dsimp only
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
  let S := presentTypeTags T
  have hcost := D.rnCellRefinedTypes_cost_bounds η hη good bad hsplit hπ n
  have hquad : ∀ tag ∈ S, ∀ᵐ sample ∂P, ∀ i j,
      (xs i sample).1 = tag → (ys j sample).1 = tag →
        cost (sample.1 i).1 (sample.2 j).1 ≤ D.quadraticConstant *
          ‖dyadicCubePoint (xs i sample).2 - dyadicCubePoint (ys j sample).2‖ ^ 2 := by
    intro tag htag
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp htag
    exact D.rnCellRefinedTypes_good_quadratic η hη good bad hsplit n t
  have hcolors := D.rnCellRefinedTypes_good_cell_colors η hη good bad hsplit hπ
    left right hleft hright cell hcell hdisj compact hcompact hcarriers k hsep n
  have hraw := exists_same_cell_core_with_one_expected_energy hq hn hk
    P L xs ys hx hy hxi hyi hxl hyl hxy S
    (fun sample i j ↦ cost (sample.1 i).1 (sample.2 j).1)
    (fun i j ↦ D.measurable_cost.comp (show Measurable (fun sample :
      (Fin n → X × Option (CellRefinedType C T)) × (Fin n → Y × Option (CellRefinedType C T)) ↦
        ((sample.1 i).1, (sample.2 j).1)) from by fun_prop)) D.quadratic_nonneg D.bound_nonneg
    (hcost.mono fun _ h i j ↦ (h i j).1) (hcost.mono fun _ h i j ↦ (h i j).2) hquad
    (fun sample i ↦ cellRefinedGoodCell left cell (sample.1 i))
    (fun sample j ↦ cellRefinedGoodCell right cell (sample.2 j)) hcolors

  have hcard : S.card = Fintype.card T := card_presentTypeTags _
  have hmass : (∑ t ∈ S, L.real {x | x.1 = t}) = (∑ t, good t Set.univ).toReal :=
    D.rnCellGoodTypes_selected_coordinate_mass η hη good bad hsplit
  simpa only [hcard, hmass] using hraw

end OTSelector.Reconstruction.PopulationTypedCostData
