import OTSelector.Reconstruction.OriginalPoissonWindowSetCounts
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowLaw
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryOriginalInputIntensity

/-! Fixed original source sets with compact carriers retain their exact original Poisson count law. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

private theorem colored_source_count_eq
    {q : ℕ} {A : Set (LegalMarkedPhysicalPoint q)} (hA : MeasurableSet A)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
    legalInputTwoBlockMeasure q b (A ×ˢ {0}) = (blockSetCount A b.1 : ℝ≥0∞) := by
  classical
  change ((∑ i : Fin b.1.1, Measure.dirac (b.1.2 i, (0 : Fin 2))) +
    (∑ i : Fin b.2.1, Measure.dirac (b.2.2 i, (1 : Fin 2)))) (A ×ˢ {0}) = _
  rw [Measure.add_apply, Measure.finsetSum_apply, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply' _ (hA.prod (measurableSet_singleton _))]
  have ht (i : Fin b.2.1) : (A ×ˢ ({0} : Set (Fin 2))).indicator
      (1 : LegalColoredInputPoint q → ℝ≥0∞) (b.2.2 i, (1 : Fin 2)) = 0 := by simp
  simp only [ht, Finset.sum_const_zero, add_zero]
  rw [blockSetCount, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : b.1.2 i ∈ A <;> simp [hi]

private theorem colored_target_count_eq
    {q : ℕ} {A : Set (LegalMarkedPhysicalPoint q)} (hA : MeasurableSet A)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
    legalInputTwoBlockMeasure q b (A ×ˢ {1}) = (blockSetCount A b.2 : ℝ≥0∞) := by
  classical
  change ((∑ i : Fin b.1.1, Measure.dirac (b.1.2 i, (0 : Fin 2))) +
    (∑ i : Fin b.2.1, Measure.dirac (b.2.2 i, (1 : Fin 2)))) (A ×ˢ {1}) = _
  rw [Measure.add_apply, Measure.finsetSum_apply, Measure.finsetSum_apply]
  simp only [Measure.dirac_apply' _ (hA.prod (measurableSet_singleton _))]
  have ht (i : Fin b.1.1) : (A ×ˢ ({1} : Set (Fin 2))).indicator
      (1 : LegalColoredInputPoint q → ℝ≥0∞) (b.1.2 i, (0 : Fin 2)) = 0 := by simp
  simp only [ht, Finset.sum_const_zero, zero_add]
  rw [blockSetCount, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : b.2.2 i ∈ A <;> simp [hi]

/-- The complete original input count on a fixed measurable source set inside an original compact carrier has an
actual original Poisson law, inherited before any adaptive phase selection. -/
theorem LegalWeightedStationaryPoissonMatching.exists_original_source_countLaw_of_compact_carrier
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A K : Set (LegalMarkedPhysicalPoint q)} (hA : MeasurableSet A) (hK : IsCompact K)
    (hAK : A ⊆ K) :
    ∃ r : ℝ≥0, HasLaw
      (fun s ↦ (s.2 : Measure (LegalColoredInputPoint q)) (A ×ˢ {0}))
      ((poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞))
      (M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  let U : Set (LegalColoredInputPoint q) := K ×ˢ univ
  have hU : IsCompact U := hK.prod isCompact_univ
  obtain ⟨S, hS, hlaw⟩ := map_inputRestriction_eq_originalPoisson_of_laplace
    M.law M.input_laplace hU
  let W := haarRootCube (Fin q) S
  have hWfin : volume W ≠ ∞ := by
    exact ((isCompact_Icc : IsCompact (haarRootCube (Fin q) S)).measure_lt_top).ne
  have hWpos : volume W ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  let r := ((((volume : Measure (Fin q → ℝ)).restrict W).prod α) A).toNNReal
  have hcount := hasLaw_originalPoissonWindow_sourceSetCount_physical q hWfin hWpos α β hA
  have hcast : HasLaw (Nat.cast : ℕ → ℝ≥0∞)
      ((poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞)) (poissonMeasure r) :=
    ⟨measurable_from_nat.aemeasurable, rfl⟩
  have harray : HasLaw (fun b ↦ legalInputTwoBlockMeasure q b (A ×ˢ {0}))
      ((poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞))
      (legalInputPoissonWindowLaw q W α β) := by
    have h := hcast.fun_comp hcount
    exact h.congr (.of_forall (fun b ↦ colored_source_count_eq hA b))
  have hB : MeasurableSet (A ×ˢ ({0} : Set (Fin 2))) := hA.prod (measurableSet_singleton _)
  let eval : Measure (LegalColoredInputPoint q) → ℝ≥0∞ := fun μ ↦ μ (A ×ˢ {0})
  have hEval : Measurable eval := Measure.measurable_coe hB
  have hrestrict : Measurable (fun μ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      (μ : Measure (LegalColoredInputPoint q)).restrict U) := by
    apply Measure.measurable_of_measurable_coe
    intro B hB
    simpa only [Measure.restrict_apply hB, Function.comp_def] using
      (Measure.measurable_coe (hB.inter hU.measurableSet)).comp measurable_localFiniteMeasure_coe
  have he := congrArg (fun P : Measure (Measure (LegalColoredInputPoint q)) ↦ P.map eval) hlaw
  have hleft : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.2 : Measure (LegalColoredInputPoint q)).restrict U) := hrestrict.comp measurable_snd
  have hright : Measurable (fun b : BlockData (LegalMarkedPhysicalPoint q) ×
      BlockData (LegalMarkedPhysicalPoint q) ↦ (legalInputTwoBlockMeasure q b).restrict U) :=
    hrestrict.comp (measurable_legalInputTwoBlockLocal q)
  rw [Measure.map_map hEval hleft, Measure.map_map hEval hright] at he
  have hsame (μ : Measure (LegalColoredInputPoint q)) : eval (μ.restrict U) = μ (A ×ˢ {0}) := by
    change (μ.restrict U) (A ×ˢ {0}) = μ (A ×ˢ {0})
    rw [Measure.restrict_apply hB]
    congr 1
    exact inter_eq_left.mpr (prod_mono hAK (subset_univ _))
  simp only [Function.comp_def, hsame] at he
  refine ⟨r, ⟨?_, he.trans harray.map_eq⟩⟩
  exact ((Measure.measurable_coe hB).comp (measurable_localFiniteMeasure_coe.comp measurable_snd)).aemeasurable

/-- The complete original input count on a fixed compact target set has an
actual original Poisson law, inherited before any adaptive phase selection. -/
theorem LegalWeightedStationaryPoissonMatching.exists_original_target_countLaw_of_compact_carrier
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A K : Set (LegalMarkedPhysicalPoint q)} (hA : MeasurableSet A) (hK : IsCompact K)
    (hAK : A ⊆ K) :
    ∃ r : ℝ≥0, HasLaw
      (fun s ↦ (s.2 : Measure (LegalColoredInputPoint q)) (A ×ˢ {1}))
      ((poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞))
      (M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  let U : Set (LegalColoredInputPoint q) := K ×ˢ univ
  have hU : IsCompact U := hK.prod isCompact_univ
  obtain ⟨S, hS, hlaw⟩ := map_inputRestriction_eq_originalPoisson_of_laplace
    M.law M.input_laplace hU
  let W := haarRootCube (Fin q) S
  have hWfin : volume W ≠ ∞ := by
    exact ((isCompact_Icc : IsCompact (haarRootCube (Fin q) S)).measure_lt_top).ne
  have hWpos : volume W ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  let r := ((((volume : Measure (Fin q → ℝ)).restrict W).prod β) A).toNNReal
  have hcount := hasLaw_originalPoissonWindow_targetSetCount_physical q hWfin hWpos α β hA
  have hcast : HasLaw (Nat.cast : ℕ → ℝ≥0∞)
      ((poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞)) (poissonMeasure r) :=
    ⟨measurable_from_nat.aemeasurable, rfl⟩
  have harray : HasLaw (fun b ↦ legalInputTwoBlockMeasure q b (A ×ˢ {1}))
      ((poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞))
      (legalInputPoissonWindowLaw q W α β) := by
    have h := hcast.fun_comp hcount
    exact h.congr (.of_forall (fun b ↦ colored_target_count_eq hA b))
  have hB : MeasurableSet (A ×ˢ ({1} : Set (Fin 2))) := hA.prod (measurableSet_singleton _)
  let eval : Measure (LegalColoredInputPoint q) → ℝ≥0∞ := fun μ ↦ μ (A ×ˢ {1})
  have hEval : Measurable eval := Measure.measurable_coe hB
  have hrestrict : Measurable (fun μ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      (μ : Measure (LegalColoredInputPoint q)).restrict U) := by
    apply Measure.measurable_of_measurable_coe
    intro B hB
    simpa only [Measure.restrict_apply hB, Function.comp_def] using
      (Measure.measurable_coe (hB.inter hU.measurableSet)).comp measurable_localFiniteMeasure_coe
  have he := congrArg (fun P : Measure (Measure (LegalColoredInputPoint q)) ↦ P.map eval) hlaw
  have hleft : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.2 : Measure (LegalColoredInputPoint q)).restrict U) := hrestrict.comp measurable_snd
  have hright : Measurable (fun b : BlockData (LegalMarkedPhysicalPoint q) ×
      BlockData (LegalMarkedPhysicalPoint q) ↦ (legalInputTwoBlockMeasure q b).restrict U) :=
    hrestrict.comp (measurable_legalInputTwoBlockLocal q)
  rw [Measure.map_map hEval hleft, Measure.map_map hEval hright] at he
  have hsame (μ : Measure (LegalColoredInputPoint q)) : eval (μ.restrict U) = μ (A ×ˢ {1}) := by
    change (μ.restrict U) (A ×ˢ {1}) = μ (A ×ˢ {1})
    rw [Measure.restrict_apply hB]
    congr 1
    exact inter_eq_left.mpr (prod_mono hAK (subset_univ _))
  simp only [Function.comp_def, hsame] at he
  refine ⟨r, ⟨?_, he.trans harray.map_eq⟩⟩
  exact ((Measure.measurable_coe hB).comp (measurable_localFiniteMeasure_coe.comp measurable_snd)).aemeasurable

private theorem lintegral_poisson_natCast (r : ℝ≥0) :
    (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure r) = (r : ℝ≥0∞) := by
  have h := ofReal_integral_eq_lintegral_ofReal (integrable_id_poissonMeasure r)
    (.of_forall (fun n : ℕ ↦ Nat.cast_nonneg n))
  simpa only [integral_id_poissonMeasure, ENNReal.ofReal_natCast,
    ENNReal.ofReal_coe_nnreal] using h.symm

/-- The same genuine original input count has exactly its physical intensity
as Poisson rate; no count or rate law is assumed for selected points. -/
theorem LegalWeightedStationaryPoissonMatching.original_source_countLaw_of_compact_carrier
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A K : Set (LegalMarkedPhysicalPoint q)} (hA : MeasurableSet A) (hK : IsCompact K)
    (hAK : A ⊆ K) :
    HasLaw (fun s ↦ (s.2 : Measure (LegalColoredInputPoint q)) (A ×ˢ {0}))
      ((poissonMeasure (((volume : Measure (Fin q → ℝ)).prod α) A).toNNReal).map
        (Nat.cast : ℕ → ℝ≥0∞)) (M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  obtain ⟨r, hN⟩ := M.exists_original_source_countLaw_of_compact_carrier hA hK hAK
  have hmean := hN.lintegral_comp measurable_id.aemeasurable
  change (∫⁻ s, (s.2 : Measure (LegalColoredInputPoint q)) (A ×ˢ {0})
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
      ∫⁻ x, x ∂(poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞) at hmean
  rw [lintegral_map (f := fun x : ℝ≥0∞ ↦ x) measurable_id measurable_from_nat,
    lintegral_poisson_natCast] at hmean
  have hint : (∫⁻ s, (s.2 : Measure (LegalColoredInputPoint q)) (A ×ˢ {0})
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
      ((volume : Measure (Fin q → ℝ)).prod α) A := by
    rw [← M.inputColorIntensities_eq_volume_prod.1,
      ← lintegral_legalInputColorMeasure_eq_intensity q _ 0 hA]
    apply lintegral_congr
    intro s
    rw [legalInputColorMeasure, Measure.map_apply measurable_fst hA,
      Measure.restrict_apply (hA.preimage measurable_fst)]
    congr 1
  have hr : r = (((volume : Measure (Fin q → ℝ)).prod α) A).toNNReal := by
    have h := congrArg ENNReal.toNNReal (hmean.symm.trans hint)
    simpa only [ENNReal.toNNReal_coe] using h
  simpa only [hr] using hN
/-- The same genuine original input count has exactly its physical intensity
as Poisson rate; no count or rate law is assumed for selected points. -/
theorem LegalWeightedStationaryPoissonMatching.original_target_countLaw_of_compact_carrier
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {A K : Set (LegalMarkedPhysicalPoint q)} (hA : MeasurableSet A) (hK : IsCompact K)
    (hAK : A ⊆ K) :
    HasLaw (fun s ↦ (s.2 : Measure (LegalColoredInputPoint q)) (A ×ˢ {1}))
      ((poissonMeasure (((volume : Measure (Fin q → ℝ)).prod β) A).toNNReal).map
        (Nat.cast : ℕ → ℝ≥0∞)) (M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  obtain ⟨r, hN⟩ := M.exists_original_target_countLaw_of_compact_carrier hA hK hAK
  have hmean := hN.lintegral_comp measurable_id.aemeasurable
  change (∫⁻ s, (s.2 : Measure (LegalColoredInputPoint q)) (A ×ˢ {1})
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
      ∫⁻ x, x ∂(poissonMeasure r).map (Nat.cast : ℕ → ℝ≥0∞) at hmean
  rw [lintegral_map (f := fun x : ℝ≥0∞ ↦ x) measurable_id measurable_from_nat,
    lintegral_poisson_natCast] at hmean
  have hint : (∫⁻ s, (s.2 : Measure (LegalColoredInputPoint q)) (A ×ˢ {1})
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) =
      ((volume : Measure (Fin q → ℝ)).prod β) A := by
    rw [← M.inputColorIntensities_eq_volume_prod.2,
      ← lintegral_legalInputColorMeasure_eq_intensity q _ 1 hA]
    apply lintegral_congr
    intro s
    rw [legalInputColorMeasure, Measure.map_apply measurable_fst hA,
      Measure.restrict_apply (hA.preimage measurable_fst)]
    congr 1
  have hr : r = (((volume : Measure (Fin q → ℝ)).prod β) A).toNNReal := by
    have h := congrArg ENNReal.toNNReal (hmean.symm.trans hint)
    simpa only [ENNReal.toNNReal_coe] using h
  simpa only [hr] using hN

end OTSelector.Reconstruction
