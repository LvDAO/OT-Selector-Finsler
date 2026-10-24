import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation
import OTSelector.Probability.CommonSubplanSampling

/-!
Conditions: A probability pair coupling π, a genuine positive-mass dominated retained pair measure χ≤π and measurable equality on the source/target carriers.

Objects: Two original-to-normalized-retained sampling couplings with exact source/target marginals and off-diagonal masses bounded by the original residual mass (π−χ)(univ).

Proof detail: Since retained mass is at most one, χ is below its probability normalization. Use the actual common retained marginal in the diagonal-plus-residual coupling construction for each color.

References: David A. Levin and Yuval Peres, with contributions by Elizabeth L. Wilmer: Section 4.2, pp. 49–52, Proposition 4.7, Remark 4.8 and equations (4.8)–(4.13); D. H. Fremlin: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
Relation: An actual retained-pair common-part argument. It needs no classwise equality of realized color counts and does not resample the retained residue independently.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalRetainedPairSampling.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalRetainedPairSampling`; the selected original proof blocks follow. -/
section

/-! Actual retained original pair mass supplies both color sampling couplings.
No class mass balance or independent replacement of a retained residue is used. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.style.haveILetI false

/-- An actual subprobability measure is retained inside its own normalization,
including original zero-density sets. -/
theorem le_normalizedFiniteLaw_of_mass_le_one
    {X : Type*} [MeasurableSpace X] (θ : Measure X) [IsFiniteMeasure θ]
    (hpos : 0 < θ.real univ) (hmass : θ.real univ ≤ 1) : θ ≤ normalizedFiniteLaw θ := by
  have hc : (1 : ℝ) ≤ (θ.real univ)⁻¹ := (one_le_inv₀ hpos).mpr hmass
  have hcNN : (1 : ℝ≥0) ≤ (θ.real univ)⁻¹.toNNReal := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_one,Real.coe_toNNReal _ (inv_nonneg.mpr hpos.le)] using hc
  have hcENN : (1 : ℝ≥0∞) ≤ ((θ.real univ)⁻¹.toNNReal : ℝ≥0∞) := by exact_mod_cast hcNN
  intro S
  change θ S ≤ ((θ.real univ)⁻¹.toNNReal : ℝ≥0∞) * θ S
  calc
    θ S = (1 : ℝ≥0∞) * θ S := (one_mul _).symm
    _ ≤ _ := by gcongr

/-- The actual original retained pair submeasure constructs source and target
common-sampling couplings with exact normalized retained marginals. Both
changed probabilities pay only the same original removed pair mass. -/
theorem exists_original_retained_pair_sampling
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableEq X] [MeasurableEq Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (π χ : Measure (X × Y)) [IsFiniteMeasure π]
    (hπ : Vlasov.IsCoupling π μ ν) (hχ : χ ≤ π) (hpos : 0 < χ.real univ) :
    ∃ κS : ProbabilityMeasure (X × X), ∃ κT : ProbabilityMeasure (Y × Y),
      (κS : Measure (X × X)).map Prod.fst = μ ∧
      (κS : Measure (X × X)).map Prod.snd = (normalizedFiniteLaw χ).map Prod.fst ∧
      (κT : Measure (Y × Y)).map Prod.fst = ν ∧
      (κT : Measure (Y × Y)).map Prod.snd = (normalizedFiniteLaw χ).map Prod.snd ∧
      (κS : Measure (X × X)) {p | p.1 ≠ p.2} ≤ (π - χ) univ ∧
      (κT : Measure (Y × Y)) {p | p.1 ≠ p.2} ≤ (π - χ) univ := by
  letI : IsFiniteMeasure χ := isFiniteMeasure_of_le π hχ
  letI : IsProbabilityMeasure (normalizedFiniteLaw χ) := normalizedFiniteLaw_probability χ hpos
  letI : IsProbabilityMeasure ((normalizedFiniteLaw χ).map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure ((normalizedFiniteLaw χ).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hmapS : (normalizedFiniteLaw χ).map Prod.fst = normalizedFiniteLaw (χ.map Prod.fst) := by
    have hm : (χ.map Prod.fst).real univ = χ.real univ := by
      simp only [measureReal_def,Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ]
    simp only [normalizedFiniteLaw,hm,Measure.map_smul]
  have hmapT : (normalizedFiniteLaw χ).map Prod.snd = normalizedFiniteLaw (χ.map Prod.snd) := by
    have hm : (χ.map Prod.snd).real univ = χ.real univ := by
      simp only [measureReal_def,Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ]
    simp only [normalizedFiniteLaw,hm,Measure.map_smul]
  have hθS : χ.map Prod.fst ≤ μ := by
    simpa only [hπ.1] using Measure.map_mono hχ measurable_fst
  have hθT : χ.map Prod.snd ≤ ν := by
    simpa only [hπ.2] using Measure.map_mono hχ measurable_snd
  have hS : χ.map Prod.fst ≤ (normalizedFiniteLaw χ).map Prod.fst := by
    rw [hmapS]
    apply le_normalizedFiniteLaw_of_mass_le_one
    · simpa only [map_measureReal_apply measurable_fst MeasurableSet.univ,preimage_univ] using hpos
    · simpa only [measureReal_def,measure_univ,ENNReal.toReal_one] using
        ENNReal.toReal_mono (measure_ne_top μ univ) (hθS univ)
  have hT : χ.map Prod.snd ≤ (normalizedFiniteLaw χ).map Prod.snd := by
    rw [hmapT]
    apply le_normalizedFiniteLaw_of_mass_le_one
    · simpa only [map_measureReal_apply measurable_snd MeasurableSet.univ,preimage_univ] using hpos
    · simpa only [measureReal_def,measure_univ,ENNReal.toReal_one] using
        ENNReal.toReal_mono (measure_ne_top ν univ) (hθT univ)
  obtain ⟨κS,κT,hκS,hκT,hSf,hSs,hTf,hTs,hSb,hTb⟩ :=
    exists_common_sampling_of_original_subplan π χ μ ((normalizedFiniteLaw χ).map Prod.fst)
      ν ((normalizedFiniteLaw χ).map Prod.snd) hπ hχ hS hT
  exact ⟨⟨κS,hκS⟩,⟨κT,hκT⟩,hSf,hSs,hTf,hTs,hSb,hTb⟩

end OTSelector.Reconstruction

end
end
