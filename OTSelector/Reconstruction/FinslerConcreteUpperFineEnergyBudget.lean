import OTSelector.Probability.SubcouplingTypeCoordinates
import OTSelector.Reconstruction.FinslerConcreteUpperGoodCellExpectedCore
import OTSelector.Reconstruction.FinslerConcreteUpperBadCellExpectedCore

/-! The good and discarded compact components share one original fine marked
experiment. Its leading good energy uses only the original atlas type count. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {X Y C T : Type*} {q n : ℕ} [Fintype T] [Fintype C]

def fineGoodHierarchyEnergy
    (sc : T → X → DyadicUnitCube q) (tc : T → Y → DyadicUnitCube q)
    (cost : X → Y → ℝ) (K : ℕ)
    (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → Y × Option (CellRefinedType C T))) : ℝ :=
  let xs := fun i sample ↦ populationFineGoodCoordinate sc (PopulationTypedCostData.cubeOrigin (q := q)) (sample.1 i)
  let ys := fun j sample ↦ populationFineGoodCoordinate tc (PopulationTypedCostData.cubeOrigin (q := q)) (sample.2 j)
  attributedTypesEnergy (presentTypeTags T) (fun i ↦ xs i sample) (fun j ↦ ys j sample)
    (fun i j ↦ cost (sample.1 i).1 (sample.2 j).1) (taggedHierarchyAssignment K xs ys sample)

def fineBadHierarchyEnergy
    (sc : T → X → DyadicUnitCube q) (tc : T → Y → DyadicUnitCube q)
    (cost : X → Y → ℝ) (K : ℕ)
    (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → Y × Option (CellRefinedType C T))) : ℝ :=
  let xs := fun i sample ↦ populationFineBadCoordinate (fun p : C × T ↦ sc p.2)
    (PopulationTypedCostData.cubeOrigin (q := q)) (sample.1 i)
  let ys := fun j sample ↦ populationFineBadCoordinate (fun p : C × T ↦ tc p.2)
    (PopulationTypedCostData.cubeOrigin (q := q)) (sample.2 j)
  attributedTypesEnergy (presentTypeTags (C × T)) (fun i ↦ xs i sample) (fun j ↦ ys j sample)
    (fun i j ↦ cost (sample.1 i).1 (sample.2 j).1) (taggedHierarchyAssignment K xs ys sample)

def fineGoodSourceCount
    (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → Y × Option (CellRefinedType C T))) : ℝ :=
  ∑ tag ∈ presentTypeTags T, partitionCount (fun i ↦ (sample.1 i).2.bind cellRefinedGoodType) tag

def fineBadSourceCount
    (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → Y × Option (CellRefinedType C T))) : ℝ :=
  ∑ tag ∈ presentTypeTags (C × T), partitionCount (fun i ↦ (sample.1 i).2.bind cellRefinedBadType) tag

def fineGoodDiscrepancy
    (sc : T → X → DyadicUnitCube q) (tc : T → Y → DyadicUnitCube q) (k : ℕ)
    (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → Y × Option (CellRefinedType C T))) : ℝ :=
  ∑ tag ∈ presentTypeTags T, taggedDyadicDiscrepancy tag k
    (fun i ↦ populationFineGoodCoordinate sc (PopulationTypedCostData.cubeOrigin (q := q)) (sample.1 i))
    (fun j ↦ populationFineGoodCoordinate tc (PopulationTypedCostData.cubeOrigin (q := q)) (sample.2 j))

def fineBadDiscrepancy
    (sc : T → X → DyadicUnitCube q) (tc : T → Y → DyadicUnitCube q)
    (sample : (Fin n → X × Option (CellRefinedType C T)) ×
      (Fin n → Y × Option (CellRefinedType C T))) : ℝ :=
  ∑ tag ∈ presentTypeTags (C × T), taggedDyadicDiscrepancy tag 1
    (fun i ↦ populationFineBadCoordinate (fun p : C × T ↦ sc p.2)
      (PopulationTypedCostData.cubeOrigin (q := q)) (sample.1 i))
    (fun j ↦ populationFineBadCoordinate (fun p : C × T ↦ tc p.2)
      (PopulationTypedCostData.cubeOrigin (q := q)) (sample.2 j))

namespace PopulationTypedCostData
variable [MeasurableSpace X] [MeasurableSpace Y]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {cost : X → Y → ℝ} (D : PopulationTypedCostData π μ ν T q cost)
  (η : Measure (X × Y)) (hη : η ≤ π)
  (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
  (hsplit : ∀ t, good t + ∑ c, bad c t = (D.types.rnSubplanTypes η hη).component (false, t))
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  [MeasurableSpace (Option (C × T))] [MeasurableSingletonClass (Option (C × T))]
  [MeasurableSpace (Option (CellRefinedType C T))]
  [MeasurableSingletonClass (Option (CellRefinedType C T))]

include D η hη hsplit in
/-- Literal total good and bad masses are bounded by the unchanged original
probability coupling, independently of the number of compact colors. -/
theorem original_good_bad_masses_le_one (hπ : Vlasov.IsCoupling π μ ν) :
    (∑ t, good t Set.univ).toReal ≤ 1 ∧
      (∑ p : C × T, bad p.1 p.2 Set.univ).toReal ≤ 1 := by
  have hπu : π Set.univ = 1 := by
    calc π Set.univ = (π.map Prod.fst) Set.univ :=
          (Measure.map_apply measurable_fst MeasurableSet.univ).symm
      _ = μ Set.univ := congrArg (fun m : Measure X ↦ m Set.univ) hπ.1
      _ = 1 := measure_univ
  have hg := (D.types.rnCellGoodTypes η hη good bad hsplit).dominated Set.univ
  have hb := (D.types.rnCellBadTypes η hη good bad hsplit).dominated Set.univ
  simp only [Measure.finsetSum_apply, PopulationSubcouplingTypes.rnCellGoodTypes_component,
    PopulationSubcouplingTypes.rnCellBadTypes_component, hπu] at hg hb
  constructor
  · simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hg
  · simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top hb

/-- One combined original-sample energy budget keeps the old type complexity in
its leading good term. Only the discarded small-mass term sees the cell index. -/
theorem exists_original_good_bad_expected_core_packet
    {Z : Type*} [MeasurableSpace Z] {k : ℕ}
    (hq : 4 < q) (hn : 0 < n) (hk : 0 < k) (hπ : Vlasov.IsCoupling π μ ν)
    (left : X → Z) (right : Y → Z) (hleft : Measurable left) (hright : Measurable right)
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
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    ∃ KG KB : ℕ, k ≤ KG ∧ 1 ≤ KB ∧
      Integrable (fun sample ↦
        fineGoodHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KG sample +
        fineBadHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KB sample) P ∧
      ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
        (∫ sample, fineGoodHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KG sample +
          fineBadHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KB sample ∂P) ≤
        D.quadraticConstant * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) +
        D.quadraticConstant * dyadicMatchingConstant q * (Fintype.card (C × T) : ℝ) ^ (2 / (q : ℝ)) *
          (∑ p : C × T, bad p.1 p.2 Set.univ).toReal ^ (1 - 2 / (q : ℝ)) +
        D.globalBound * (Real.sqrt (2 * Fintype.card T) + Real.sqrt (2 * Fintype.card (C × T))) *
          (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) ∧
      Integrable (fun sample ↦ fineGoodDiscrepancy D.sourceCoordinate D.targetCoordinate k sample +
        fineBadDiscrepancy D.sourceCoordinate D.targetCoordinate sample) P ∧
      (∫ sample, fineGoodDiscrepancy D.sourceCoordinate D.targetCoordinate k sample +
        fineBadDiscrepancy D.sourceCoordinate D.targetCoordinate sample ∂P) ≤
        (Fintype.card T : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ k + 1) ^ q) +
        (Fintype.card (C × T) : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q) ∧
      ∀ᵐ sample ∂P, ∃ coreGood coreBad : OTSelector.PartialMatching n n,
        (∀ e ∈ coreGood.edges, ∃ t,
          (sample.1 e.1).2.bind cellRefinedGoodType = some t ∧
          (sample.2 e.2).2.bind cellRefinedGoodType = some t ∧
          ∃ c, cellRefinedGoodCell left cell (sample.1 e.1) = some c ∧
            cellRefinedGoodCell right cell (sample.2 e.2) = some c) ∧
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
          fineBadDiscrepancy D.sourceCoordinate D.targetCoordinate sample := by
  classical
  letI : DecidableEq (C × T) := fun a b ↦ Classical.propDecidable (a = b)
  obtain ⟨KG, hKG, hGE, hGD, hGC⟩ :=
    D.exists_original_good_cell_core_expected_energy η hη good bad hsplit hq hn hk hπ
      left right hleft hright cell hcell hdisj compact hcompact hcarriers hsep
  obtain ⟨KB, hKB, hBE, hBD, hBC⟩ :=
    D.exists_original_bad_cell_core_expected_energy η hη good bad hsplit hq hn hπ
  dsimp only
  let R := D.types.rnCellRefinedTypes η hη good bad hsplit
  let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
  have hGI : Integrable (fineGoodHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KG) P := hGE.1
  have hBI : Integrable (fineBadHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KB) P := hBE.1
  refine ⟨KG, KB, hKG, hKB, hGI.add hBI, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [integral_add hGI hBI, mul_add]
    have hraw := add_le_add hGE.2 hBE.2
    have hmass := D.original_good_bad_masses_le_one η hη good bad hsplit hπ
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hexp : 0 ≤ 1 - 2 / (q : ℝ) := by
      have h2 : (2 : ℝ) ≤ q := by exact_mod_cast (by omega : 2 ≤ q)
      linarith [(div_le_one hqpos).mpr h2]
    have hpow : (∑ t, good t Set.univ).toReal ^ (1 - 2 / (q : ℝ)) ≤ 1 :=
      Real.rpow_le_one ENNReal.toReal_nonneg hmass.1 hexp
    have hsg : Real.sqrt (∑ t, good t Set.univ).toReal ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hmass.1
    have hsb : Real.sqrt (∑ p : C × T, bad p.1 p.2 Set.univ).toReal ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hmass.2
    have hlead : D.quadraticConstant * dyadicMatchingConstant q *
        (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) *
          (∑ t, good t Set.univ).toReal ^ (1 - 2 / (q : ℝ)) ≤
        D.quadraticConstant * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (mul_nonneg D.quadratic_nonneg (dyadicMatchingConstant_pos hq).le)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    have hgoodCount : D.globalBound * Real.sqrt (2 * Fintype.card T) *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (∑ t, good t Set.univ).toReal ≤
        D.globalBound * Real.sqrt (2 * Fintype.card T) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsg
        (mul_nonneg (mul_nonneg D.bound_nonneg (Real.sqrt_nonneg _))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    have hbadCount : D.globalBound * Real.sqrt (2 * Fintype.card (C × T)) *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (∑ p : C × T, bad p.1 p.2 Set.univ).toReal ≤
        D.globalBound * Real.sqrt (2 * Fintype.card (C × T)) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsb
        (mul_nonneg (mul_nonneg D.bound_nonneg (Real.sqrt_nonneg _))
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    exact hraw.trans (by nlinarith only [hlead, hgoodCount, hbadCount])

  · exact hGD.1.add hBD.1
  · have hsum := add_le_add hGD.2 hBD.2
    dsimp only [fineGoodDiscrepancy, fineBadDiscrepancy]
    rw [integral_add hGD.1 hBD.1]
    have hgprob := D.rnCellRefinedTypes_good_iid_facts η hη good bad hsplit hπ n
    have hbprob := D.rnCellRefinedTypes_bad_iid_facts η hη good bad hsplit hπ n
    let LG := (D.types.rnCellGoodTypes η hη good bad hsplit).typeCoordinateLaw μ
      D.sourceCoordinate (cubeOrigin (q := q))
    let LB := (D.types.rnCellBadTypes η hη good bad hsplit).typeCoordinateLaw μ
      (fun p : C × T ↦ D.sourceCoordinate p.2) (cubeOrigin (q := q))
    letI : IsProbabilityMeasure LG := hgprob.2.1
    letI : IsProbabilityMeasure LB := hbprob.2.1
    have hgood : (∑ tag ∈ presentTypeTags T,
        Real.sqrt (2 * (n : ℝ) * LG.real {x | x.1 = tag} * ((2 : ℝ) ^ k + 1) ^ q)) ≤
        (Fintype.card T : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ k + 1) ^ q) := by
      calc _ ≤ ∑ _tag ∈ presentTypeTags T,
          Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ k + 1) ^ q) := by
            apply Finset.sum_le_sum
            intro tag _
            apply Real.sqrt_le_sqrt
            have hmass : LG.real {x | x.1 = tag} ≤ 1 := measureReal_le_one
            exact mul_le_mul_of_nonneg_right
              (mul_le_of_le_one_right (by positivity : 0 ≤ 2 * (n : ℝ)) hmass) (by positivity)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_presentTypeTags]
    have hbad : (∑ tag ∈ presentTypeTags (C × T),
        Real.sqrt (2 * (n : ℝ) * LB.real {x | x.1 = tag} * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q)) ≤
        (Fintype.card (C × T) : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q) := by
      calc _ ≤ ∑ _tag ∈ presentTypeTags (C × T),
          Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q) := by
            apply Finset.sum_le_sum
            intro tag _
            apply Real.sqrt_le_sqrt
            have hmass : LB.real {x | x.1 = tag} ≤ 1 := measureReal_le_one
            exact mul_le_mul_of_nonneg_right
              (mul_le_of_le_one_right (by positivity : 0 ≤ 2 * (n : ℝ)) hmass) (by positivity)
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_presentTypeTags]
    exact hsum.trans (add_le_add hgood hbad)
  · filter_upwards [hGC, hBC] with sample hg hb
    obtain ⟨g, hgedges, hgc, hgd⟩ := hg
    obtain ⟨b, hbedges, hbc, hbd⟩ := hb
    refine ⟨g, b, ?_, ?_, hgc, hbc, hgd, hbd⟩
    · intro e he
      obtain ⟨hs, heq, hc⟩ := hgedges e he
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hs
      refine ⟨t, ?_, ?_, hc⟩
      · exact ht.symm
      · exact heq.symm.trans ht.symm
    · intro e he
      obtain ⟨hs, heq, _⟩ := hbedges e he
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hs
      refine ⟨p, ?_, ?_⟩
      · exact hp.symm
      · exact heq.symm.trans hp.symm

end PopulationTypedCostData
end OTSelector.Reconstruction
