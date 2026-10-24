import OTSelector.Probability.CommonSubplanSampling
import OTSelector.Probability.FiniteProductIndicatorMoment

/-!
Conditions: Two genuine one-point sampling probability couplings with specified marginals and finite iid index sets; mismatch upper bounds are explicit.

Objects: Exact original iid-array marginals under a two-color product coupling and an expected number of replaced coordinates bounded by the one-point residual masses.

Proof detail: Integrate the finite sum of mismatch indicators and use finite-product marginal identities separately for the two colors.

References: David A. Levin and Yuval Peres, with contributions by Elizabeth L. Wilmer: Section 4.2, pp. 49–52, Proposition 4.7, Remark 4.8 and equations (4.8)–(4.13); Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: An actual iid sampling-coupling construction. It makes no equality claim for the realized per-color counts in any retained core.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CommonSubplanIIDSampling.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CommonSubplanIIDSampling`; the selected original proof blocks follow. -/
section

/-!
# Exact iid laws and replacement counts under common sampling

The product of the two sampling couplings preserves independent iid arrays for
both models. Its expected number of changed coordinates is charged to the fixed
original residual, without imposing equality of realized color counts.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace OTSelector.Reconstruction

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableEq X] [MeasurableEq Y]

/-- Number of unequal coordinates in a finite common-sampling array. -/
noncomputable def commonSamplingChangeCount {I A : Type*} [Fintype I]
    (p : I → A × A) : ℝ :=
  ∑ i, {q : A × A | q.1 ≠ q.2}.indicator (fun _ ↦ (1 : ℝ)) (p i)

/-- Exact expected number of replaced coordinates in one color. -/
theorem integral_commonSamplingChangeCount {I A : Type*} [Fintype I]
    [MeasurableSpace A] [MeasurableEq A]
    (γ : Measure (A × A)) [IsProbabilityMeasure γ] :
    Integrable (commonSamplingChangeCount (I := I)) (Measure.pi (fun _ : I ↦ γ)) ∧
    (∫ p, commonSamplingChangeCount p ∂Measure.pi (fun _ : I ↦ γ)) =
      Fintype.card I * γ.real {q | q.1 ≠ q.2} := by
  have hA : MeasurableSet {q : A × A | q.1 ≠ q.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hi (i : I) := OTSelector.Probability.integrable_finiteProductIndicator
    (fun _ : I ↦ γ) (fun _ ↦ {q : A × A | q.1 ≠ q.2}) (fun _ ↦ hA) i
  constructor
  · exact integrable_finsetSum _ (fun i _ ↦ hi i)
  · rw [show commonSamplingChangeCount (I := I) =
        fun p ↦ ∑ i, OTSelector.Probability.finiteProductIndicator
          (fun _ : I ↦ {q : A × A | q.1 ≠ q.2}) i p from rfl,
      integral_finsetSum _ (fun i _ ↦ hi i)]
    simp only [OTSelector.Probability.integral_finiteProductIndicator
      (fun _ : I ↦ γ) (fun _ ↦ {q : A × A | q.1 ≠ q.2}) (fun _ ↦ hA),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [MeasurableEq X] [MeasurableEq Y] in
/-- Both independent iid color arrays retain the exact original and frozen laws. -/
theorem iid_twoColor_common_sampling_marginals {I : Type*} [Fintype I]
    (γ₀ : Measure (X × X)) [IsProbabilityMeasure γ₀]
    (γ₁ : Measure (Y × Y)) [IsProbabilityMeasure γ₁]
    (μ₀ μ₁ : Measure X) (ν₀ ν₁ : Measure Y)
    (hμ₀ : γ₀.map Prod.fst = μ₀) (hμ₁ : γ₀.map Prod.snd = μ₁)
    (hν₀ : γ₁.map Prod.fst = ν₀) (hν₁ : γ₁.map Prod.snd = ν₁) :
    let Ω := (Measure.pi (fun _ : I ↦ γ₀)).prod (Measure.pi (fun _ : I ↦ γ₁))
    Ω.map (fun p ↦ (fun i ↦ (p.1 i).1, fun i ↦ (p.2 i).1)) =
        (Measure.pi (fun _ : I ↦ μ₀)).prod (Measure.pi (fun _ : I ↦ ν₀)) ∧
    Ω.map (fun p ↦ (fun i ↦ (p.1 i).2, fun i ↦ (p.2 i).2)) =
        (Measure.pi (fun _ : I ↦ μ₁)).prod (Measure.pi (fun _ : I ↦ ν₁)) := by
  have h₀ := iid_common_sampling_marginals (I := I) γ₀ μ₀ μ₁ hμ₀ hμ₁
  have h₁ := iid_common_sampling_marginals (I := I) γ₁ ν₀ ν₁ hν₀ hν₁
  constructor
  · rw [show (fun p : (I → X × X) × (I → Y × Y) ↦
        (fun i ↦ (p.1 i).1, fun i ↦ (p.2 i).1)) =
        Prod.map (fun p i ↦ (p i).1) (fun p i ↦ (p i).1) from rfl,
      ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), h₀.1, h₁.1]
  · rw [show (fun p : (I → X × X) × (I → Y × Y) ↦
        (fun i ↦ (p.1 i).2, fun i ↦ (p.2 i).2)) =
        Prod.map (fun p i ↦ (p i).2) (fun p i ↦ (p i).2) from rfl,
      ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), h₀.2, h₁.2]

/-- The total expected change count is at most twice the sample size times the
mass of the fixed discarded original subplan. -/
theorem integral_twoColor_commonSamplingChangeCount_le {I : Type*} [Fintype I]
    (γ₀ : Measure (X × X)) [IsProbabilityMeasure γ₀]
    (γ₁ : Measure (Y × Y)) [IsProbabilityMeasure γ₁]
    {δ : ℝ≥0∞} (hδ : δ ≠ ∞)
    (h₀ : γ₀ {q | q.1 ≠ q.2} ≤ δ) (h₁ : γ₁ {q | q.1 ≠ q.2} ≤ δ) :
    let Ω := (Measure.pi (fun _ : I ↦ γ₀)).prod (Measure.pi (fun _ : I ↦ γ₁))
    Integrable (fun p ↦ commonSamplingChangeCount p.1 + commonSamplingChangeCount p.2) Ω ∧
    (∫ p, commonSamplingChangeCount p.1 + commonSamplingChangeCount p.2 ∂Ω) ≤
      2 * Fintype.card I * δ.toReal := by
  obtain ⟨hi₀, he₀⟩ := integral_commonSamplingChangeCount (I := I) γ₀
  obtain ⟨hi₁, he₁⟩ := integral_commonSamplingChangeCount (I := I) γ₁
  have hp₀ := hi₀.comp_fst (Measure.pi (fun _ : I ↦ γ₁))
  have hp₁ := hi₁.comp_snd (Measure.pi (fun _ : I ↦ γ₀))
  refine ⟨hp₀.add hp₁, ?_⟩
  rw [integral_add hp₀ hp₁, integral_fun_fst, integral_fun_snd,
    probReal_univ, probReal_univ, one_smul, one_smul, he₀, he₁]
  have hb₀ := mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hδ h₀)
    (show (0 : ℝ) ≤ Fintype.card I by positivity)
  have hb₁ := mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hδ h₁)
    (show (0 : ℝ) ≤ Fintype.card I by positivity)
  change (Fintype.card I : ℝ) * _ + (Fintype.card I : ℝ) * _ ≤ _
  simp only [measureReal_def]
  linarith

end OTSelector.Reconstruction

end
