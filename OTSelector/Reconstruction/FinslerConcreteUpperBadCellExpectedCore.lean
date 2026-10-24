import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.FinslerConcreteUpperHierarchyCellExpectation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalSelectedCoordinateMass
import OTSelector.Reconstruction.FinslerRelativeLawOriginalGoodCoordinateFacts

/-! Cell-specific discarded original components have a genuine small-energy
same-cell core on the same fine original marked experiment. The bad observation
keeps the cell in its type, while the good leading energy keeps only old types. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationTypedCostData
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X Y C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype C] [Fintype T] {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {q : ℕ} {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
  (η : Measure (X × Y)) (hη : η ≤ π)
  (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
  (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
  [MeasurableSpace (Option (C × T))] [MeasurableSingletonClass (Option (C × T))]
  [MeasurableSpace (Option (CellRefinedType C T))]
  [MeasurableSingletonClass (Option (CellRefinedType C T))]

/-- Every iid, quadratic, global-bound, and same-cell input is derived from the
original component split. The selected type count is exactly the finite bad
cell/old-type count; its mass will be made small after these cells are fixed. -/
theorem exists_original_bad_cell_core_expected_energy
    {n : ℕ} (hq : 4 < q) (hn : 0 < n) (hπ : Vlasov.IsCoupling π μ ν) :
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
    let S := presentTypeTags (C × T)
    let sourceCell := fun sample i ↦ (xs i sample).1.map Prod.fst
    let targetCell := fun sample j ↦ (ys j sample).1.map Prod.fst
    let cost := fun sample i j ↦ cost (sample.1 i).1 (sample.2 j).1
    ∃ K : ℕ, 1 ≤ K ∧
      (Integrable (fun sample ↦ attributedTypesEnergy S (fun i ↦ xs i sample)
        (fun j ↦ ys j sample) (cost sample) (taggedHierarchyAssignment K xs ys sample)) P ∧
      ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
        (∫ sample, attributedTypesEnergy S (fun i ↦ xs i sample) (fun j ↦ ys j sample)
          (cost sample) (taggedHierarchyAssignment K xs ys sample) ∂P) ≤
        D.quadraticConstant * dyadicMatchingConstant q * (Fintype.card (C × T) : ℝ) ^ (2 / (q : ℝ)) *
          (∑ t : C × T, bad t.1 t.2 Set.univ).toReal ^ (1 - 2 / (q : ℝ)) +
        D.globalBound * Real.sqrt (2 * Fintype.card (C × T)) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) *
          Real.sqrt (∑ t : C × T, bad t.1 t.2 Set.univ).toReal) ∧
      (Integrable (fun sample ↦ ∑ t ∈ S,
        taggedDyadicDiscrepancy t 1 (fun i ↦ xs i sample) (fun j ↦ ys j sample)) P ∧
      (∫ sample, ∑ t ∈ S, taggedDyadicDiscrepancy t 1
        (fun i ↦ xs i sample) (fun j ↦ ys j sample) ∂P) ≤
        ∑ t ∈ S, Real.sqrt (2 * (n : ℝ) * L.real {x | x.1 = t} * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q)) ∧
      ∀ᵐ sample ∂P, ∃ core : OTSelector.PartialMatching n n,
        (∀ e ∈ core.edges,
          (xs e.1 sample).1 ∈ S ∧ (xs e.1 sample).1 = (ys e.2 sample).1 ∧
          ∃ c, sourceCell sample e.1 = some c ∧ targetCell sample e.2 = some c) ∧
        core.cost (cost sample) ≤ attributedTypesEnergy S (fun i ↦ xs i sample)
          (fun j ↦ ys j sample) (cost sample) (taggedHierarchyAssignment K xs ys sample) ∧
        (∑ t ∈ S, partitionCount (fun i ↦ (xs i sample).1) t) - (core.card : ℝ) ≤
          ∑ t ∈ S, taggedDyadicDiscrepancy t 1
            (fun i ↦ xs i sample) (fun j ↦ ys j sample) := by
  classical
  letI : DecidableEq (C × T) := fun a b ↦ Classical.propDecidable (a = b)
  letI : MeasurableSpace (Option T) := ⊤
  letI : MeasurableSingletonClass (Option T) := ⟨fun _ ↦ trivial⟩
  obtain ⟨hP, hL, hx, hy, hxi, hyi, hxl, hyl, hxy⟩ :=
    D.rnCellRefinedTypes_bad_iid_facts η hη good bad hsplit hπ n
  letI := hP
  letI := hL
  dsimp only
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
  let S := presentTypeTags (C × T)
  have hcost := D.rnCellRefinedTypes_cost_bounds η hη good bad hsplit hπ n
  have hquad : ∀ tag ∈ S, ∀ᵐ sample ∂P, ∀ i j,
      (xs i sample).1 = tag → (ys j sample).1 = tag →
        cost (sample.1 i).1 (sample.2 j).1 ≤ D.quadraticConstant *
          ‖dyadicCubePoint (xs i sample).2 - dyadicCubePoint (ys j sample).2‖ ^ 2 := by
    intro tag htag
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp htag
    exact D.rnCellRefinedTypes_bad_quadratic η hη good bad hsplit n p
  have hcolors : ∀ᵐ sample ∂P,
      (∀ i, (xs i sample).1 ∈ S → ∃ c, (xs i sample).1.map Prod.fst = some c) ∧
      (∀ j, (ys j sample).1 ∈ S → ∃ c, (ys j sample).1.map Prod.fst = some c) ∧
      ∀ i j c c', (xs i sample).1.map Prod.fst = some c →
        (ys j sample).1.map Prod.fst = some c' → (xs i sample).1 = (ys j sample).1 →
        dyadicCubeCell 1 (xs i sample).2 = dyadicCubeCell 1 (ys j sample).2 → c = c' := by
    apply Filter.Eventually.of_forall
    intro sample
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hi
      exact ⟨p.1, by rw [← hp]; rfl⟩
    · intro j hj
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hj
      exact ⟨p.1, by rw [← hp]; rfl⟩
    · intro i j c c' hc hc' heq _
      exact Option.some.inj (hc.symm.trans ((congrArg (Option.map Prod.fst) heq).trans hc'))
  have hraw := exists_same_cell_core_with_one_expected_energy hq hn (by decide : 0 < 1)
    P L xs ys hx hy hxi hyi hxl hyl hxy S
    (fun sample i j ↦ cost (sample.1 i).1 (sample.2 j).1)
    (fun i j ↦ D.measurable_cost.comp (show Measurable (fun sample :
      (Fin n → X × Option (CellRefinedType C T)) × (Fin n → Y × Option (CellRefinedType C T)) ↦
        ((sample.1 i).1, (sample.2 j).1)) from by fun_prop)) D.quadratic_nonneg D.bound_nonneg
    (hcost.mono fun _ h i j ↦ (h i j).1) (hcost.mono fun _ h i j ↦ (h i j).2) hquad
    (fun sample i ↦ (xs i sample).1.map Prod.fst)
    (fun sample j ↦ (ys j sample).1.map Prod.fst) hcolors

  have hcard : S.card = Fintype.card (C × T) := card_presentTypeTags (C × T)
  have hmass : (∑ t ∈ S, L.real {x | x.1 = t}) = (∑ t : C × T, bad t.1 t.2 Set.univ).toReal :=
    D.rnCellBadTypes_selected_coordinate_mass η hη good bad hsplit
  simpa only [hcard, hmass] using hraw

end OTSelector.Reconstruction.PopulationTypedCostData
