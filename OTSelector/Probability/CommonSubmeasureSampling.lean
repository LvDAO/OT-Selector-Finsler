import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FiniteMeasureCommonSampling.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FiniteMeasureCommonSampling`; the selected original proof blocks follow. -/
section

/-!
# Probability.CommonSubmeasureSampling

## Lemma skeleton

* **Conditions:** Two probability measures with an actual shared submeasure; the finite-law freezing wrapper has positive reference mass and eta<1.
* **Objects:** Exact common sampling with a mismatch bound and its normalized finite-law freezing consequence.
* **Proof detail:** Sample the shared part diagonally and couple the residuals independently after their equal-mass normalization. For freezing use the common part supplied by full variation and compare normalized masses.

## Mathematical sources

- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.

Source relation (composition): Explicit common-submeasure coupling. The numerical 3 eta/(1-eta) is a locally derived coarse bound.
-/

/-!
# A common sampling law from the actual shared submeasure

The shared part is sampled on the diagonal. Only the two residual measures are
sampled independently, giving the original marginals exactly.
-/

open Set MeasureTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

variable {X : Type*} [MeasurableSpace X] [MeasurableEq X]

/-- Two probability laws sharing a submeasure have a coupling whose disagreement
probability is bounded by the actual residual mass. -/
theorem exists_common_sampling_of_submeasure (μ ν θ : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hθμ : θ ≤ μ) (hθν : θ ≤ ν) :
    ∃ π : Measure (X × X), IsProbabilityMeasure π ∧
      π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
      π {p | p.1 ≠ p.2} ≤ (μ - θ) univ := by
  let _instCommon : IsFiniteMeasure θ := isFiniteMeasure_of_le μ hθμ
  let μr := μ - θ
  let νr := ν - θ
  have hmass : μr univ = νr univ := by
    simp only [μr, νr, Measure.sub_apply MeasurableSet.univ hθμ,
      Measure.sub_apply MeasurableSet.univ hθν, measure_univ]
  have hcancel (ξ : Measure X) [IsFiniteMeasure ξ] :
      ((ξ univ)⁻¹ * ξ univ) • ξ = ξ := by
    by_cases hξ : ξ univ = 0
    · have hz : ξ = 0 := Measure.measure_univ_eq_zero.mp hξ
      simp [hz]
    · rw [ENNReal.inv_mul_cancel hξ (measure_ne_top _ _), one_smul]
  let diagonalLaw := θ.map (fun x ↦ (x, x))
  let residualLaw := (μr univ)⁻¹ • μr.prod νr
  let π := diagonalLaw + residualLaw
  have hdiag : Measurable (fun x : X ↦ (x, x)) := by fun_prop
  have hfst : π.map Prod.fst = μ := by
    dsimp only [π, diagonalLaw, residualLaw]
    rw [Measure.map_add _ _ measurable_fst,
      Measure.map_map measurable_fst hdiag,
      show Prod.fst ∘ (fun x : X ↦ (x, x)) = id from rfl, Measure.map_id,
      Measure.map_smul, Measure.map_fst_prod, smul_smul, ← hmass, hcancel,
      add_comm]
    exact Measure.sub_add_cancel_of_le hθμ
  have hsnd : π.map Prod.snd = ν := by
    dsimp only [π, diagonalLaw, residualLaw]
    rw [Measure.map_add _ _ measurable_snd,
      Measure.map_map measurable_snd hdiag,
      show Prod.snd ∘ (fun x : X ↦ (x, x)) = id from rfl, Measure.map_id,
      Measure.map_smul, Measure.map_snd_prod, smul_smul, hmass, hcancel,
      add_comm]
    exact Measure.sub_add_cancel_of_le hθν
  have hprob : IsProbabilityMeasure π := by
    constructor
    have h := congrArg (fun ξ : Measure X ↦ ξ univ) hfst
    simpa only [Measure.map_apply measurable_fst MeasurableSet.univ,
      preimage_univ, measure_univ] using h
  refine ⟨π, hprob, hfst, hsnd, ?_⟩
  have hmeas : MeasurableSet {p : X × X | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hzero : diagonalLaw {p | p.1 ≠ p.2} = 0 := by
    dsimp only [diagonalLaw]
    rw [Measure.map_apply (show Measurable (fun x : X ↦ (x, x)) by fun_prop) hmeas]
    simp
  calc
    π {p | p.1 ≠ p.2} = residualLaw {p | p.1 ≠ p.2} := by
      change (diagonalLaw + residualLaw) _ = _
      rw [Measure.add_apply, hzero, zero_add]
    _ ≤ residualLaw univ := measure_mono (subset_univ _)
    _ = (μ - θ) univ := by
      change ((μr univ)⁻¹ • μr.prod νr) univ = μr univ
      rw [Measure.smul_apply, smul_eq_mul, ← univ_prod_univ, Measure.prod_prod, ← hmass]
      by_cases hz : μr univ = 0
      · simp [hz]
      · rw [← mul_assoc, ENNReal.inv_mul_cancel hz (measure_ne_top _ _), one_mul]

/-- The raw freezing estimates produce an actual normalized sampling coupling;
the probability of changing a sample is explicitly controlled. -/
theorem FiniteLawFreezingBound.exists_normalized_common_sampling
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {η : ℝ}
    (D : FiniteLawFreezingBound μ ν η)
    (hη : 0 ≤ η) (hη1 : η < 1) (hν : 0 < ν.real univ) :
    ∃ π : Measure (X × X), IsProbabilityMeasure π ∧
      π.map Prod.fst = normalizedFiniteLaw μ ∧
      π.map Prod.snd = normalizedFiniteLaw ν ∧
      π {p | p.1 ≠ p.2} ≤ ENNReal.ofReal (3 * η / (1 - η)) := by
  have hv := D.normalized_variation hη hη1 hν
  let _instActual := normalizedFiniteLaw_probability μ hv.1
  let _instFrozen := normalizedFiniteLaw_probability ν hν
  obtain ⟨θ, hθμ, hθν, _, hsmall⟩ := D.normalized_common_part hη hη1 hν
  obtain ⟨π, hπ, hf, hs, hb⟩ :=
    exists_common_sampling_of_submeasure (normalizedFiniteLaw μ) (normalizedFiniteLaw ν)
      θ hθμ hθν
  exact ⟨π, hπ, hf, hs, hb.trans hsmall⟩

end OTSelector.Reconstruction

end
