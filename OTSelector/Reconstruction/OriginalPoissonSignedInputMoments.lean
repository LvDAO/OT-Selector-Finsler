import OTSelector.Probability.PoissonSignedIntegralMoments
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowSecondMoment

/-!
# Exact signed stochastic integral of the original finite Poisson input

The finite random measure is the existing literal input enumeration, with all
multiplicities retained. Its intensity is the original rate times the original
point law. The exact signed variance and deterministic support estimate follow
from the shared prefix result, without assigning a Poisson law to adaptive ports.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [MeasurableSpace X]

private theorem measurable_originalPoissonSignedPrefixEncode :
    Measurable (fun z : ℕ × (ℕ → X) ↦
      (⟨z.1, fun i : Fin z.1 ↦ z.2 i⟩ : BlockData X)) := by
  apply measurable_from_prod_countable_right
  intro n
  exact (measurable_sigma_mk n).comp
    (measurable_pi_lambda _ fun i : Fin n ↦ measurable_pi_apply (i : ℕ))

/-- Any measurable signed-test functional keeps the literal count-and-points law. -/
theorem integral_functional_originalPoisson_blockTest
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {Φ : ℝ → ℝ} (hΦ : Measurable Φ) :
    (∫ b, Φ (legalInputBlockTest f b)
      ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) =
      ∫ z, Φ (poissonPrefixSum f z)
        ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) := by
  have htest : Measurable (fun b : BlockData X ↦ Φ (legalInputBlockTest f b)) :=
    hΦ.comp (measurable_legalInputBlockTest hf)
  rw [blockDataLaw_eq_map_cloud,
    integral_map measurable_originalPoissonSignedPrefixEncode.aemeasurable
      htest.aestronglyMeasurable]
  rfl

/-- The actual signed finite point integral has a finite second moment. -/
theorem memLp_two_originalPoisson_blockTest
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hbound : ∀ x, |f x| ≤ B) :
    MemLp (legalInputBlockTest f) 2
      (blockDataLaw ν (fun n ↦ poissonMeasure r {n})) := by
  rw [blockDataLaw_eq_map_cloud]
  exact (memLp_map_measure_iff
    (measurable_legalInputBlockTest hf).aestronglyMeasurable
    measurable_originalPoissonSignedPrefixEncode.aemeasurable).mpr
      (memLp_two_poissonPrefixSum ν r hf hbound)

/-- Campbell's identity for a signed bounded test of the actual original enumeration. -/
theorem integral_originalPoisson_blockTest
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hbound : ∀ x, |f x| ≤ B) :
    (∫ b, legalInputBlockTest f b ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) =
      (r : ℝ) * ∫ x, f x ∂ν := by
  rw [show (∫ b, legalInputBlockTest f b
      ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) =
      ∫ b, id (legalInputBlockTest f b)
        ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n}) from rfl,
    integral_functional_originalPoisson_blockTest ν r hf measurable_id]
  exact integral_poissonPrefixSum ν r hf hbound

/-- Exact compensated variance for the existing original finite-array law. -/
theorem integral_sq_centered_originalPoisson_blockTest
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) :
    (∫ b, (legalInputBlockTest f b - (r : ℝ) * ∫ x, f x ∂ν) ^ 2
      ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) =
      (r : ℝ) * ∫ x, (f x) ^ 2 ∂ν := by
  rw [integral_functional_originalPoisson_blockTest ν r hf
    (by fun_prop : Measurable (fun u : ℝ ↦ (u - (r : ℝ) * ∫ x, f x ∂ν) ^ 2))]
  exact integral_sq_centered_poissonPrefixSum ν r hf hB hbound

/-- Exact zero-mean full-input variance, including signed cancellation. -/
theorem integral_sq_originalPoisson_blockTest_of_integral_eq_zero
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) (hmean : ∫ x, f x ∂ν = 0) :
    (∫ b, (legalInputBlockTest f b) ^ 2
      ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) =
      (r : ℝ) * ∫ x, (f x) ^ 2 ∂ν := by
  simpa only [hmean, mul_zero, sub_zero] using
    integral_sq_centered_originalPoisson_blockTest ν r hf hB hbound

/-- A deterministic boundary-layer support controls the full-input variance. -/
theorem integral_sq_centered_originalPoisson_blockTest_le_support
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) {S : Set X} (hS : MeasurableSet S)
    (hsupport : ∀ x, x ∉ S → f x = 0) :
    (∫ b, (legalInputBlockTest f b - (r : ℝ) * ∫ x, f x ∂ν) ^ 2
      ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) ≤
      (r : ℝ) * B ^ 2 * ν.real S := by
  rw [integral_functional_originalPoisson_blockTest ν r hf
    (by fun_prop : Measurable (fun u : ℝ ↦ (u - (r : ℝ) * ∫ x, f x ∂ν) ^ 2))]
  exact integral_sq_centered_poissonPrefixSum_le_support ν r hf hB hbound hS hsupport

/-- The exact stochastic-integral statement on the original finite random measure. -/
theorem integral_sq_centered_originalPoisson_blockMeasure
    [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) :
    (∫ b, ((∫ x, f x ∂legalInputBlockMeasure b) -
      ∫ x, f x ∂((r : ℝ≥0∞) • ν)) ^ 2
      ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) =
      ∫ x, (f x) ^ 2 ∂((r : ℝ≥0∞) • ν) := by
  simp_rw [integral_legalInputBlockMeasure, integral_smul_measure,
    ENNReal.coe_toReal, smul_eq_mul]
  exact integral_sq_centered_originalPoisson_blockTest ν r hf hB hbound

end OTSelector.Reconstruction
