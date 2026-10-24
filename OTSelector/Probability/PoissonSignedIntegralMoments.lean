import OTSelector.Probability.PoissonPrefixMoments
import OTSelector.Probability.IIDWeightedSecondMoment
import OTSelector.Probability.InfiniteProductLaw
import OTSelector.Probability.PoissonCountDiscrepancy

/-!
# Signed moments of the original finite Poisson input

The random input is the original independent Poisson count and iid point sequence.
Conditioning on the count reduces its signed second moment to the shared finite iid
second-moment formula. No Poisson assumption is made about adaptively selected points.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [MeasurableSpace X]

/-- The already known Poisson second-moment series also supplies its integrability. -/
theorem integrable_sq_id_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ ↦ (n : ℝ) ^ 2) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  refine (poissonSecondMoment_hasSum r).summable.congr fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), poissonMeasure_real_singleton]
  ring

/-- A bounded signed test of the complete original used prefix is square integrable. -/
theorem memLp_two_poissonPrefixSum
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    MemLp (poissonPrefixSum f) 2
      ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_poissonPrefixSum hf).aestronglyMeasurable).mpr
  refine (((integrable_sq_id_poissonMeasure r).comp_fst
    (Measure.infinitePi (fun _ : ℕ ↦ ν))).mul_const (B ^ 2)).mono'
      ((measurable_poissonPrefixSum hf).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    (poissonPrefixSum f z) ^ 2 = |poissonPrefixSum f z| ^ 2 := (sq_abs _).symm
    _ ≤ ((z.1 : ℝ) * B) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_poissonPrefixSum_le hB z) 2
    _ = (z.1 : ℝ) ^ 2 * B ^ 2 := mul_pow _ _ _

/-- The exact raw second moment retains the diagonal contribution of each original point. -/
theorem integral_sq_poissonPrefixSum
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) :
    (∫ z, (poissonPrefixSum f z) ^ 2
      ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν)))) =
      (r : ℝ) * (∫ x, (f x) ^ 2 ∂ν) +
        ((r : ℝ) * ∫ x, f x ∂ν) ^ 2 := by
  have hfixed (n : ℕ) :
      (∫ y : ℕ → X, (∑ i : Fin n, f (y i)) ^ 2
        ∂Measure.infinitePi (fun _ : ℕ ↦ ν)) =
      (∫ x, f x ∂ν) ^ 2 * (n : ℝ) ^ 2 +
        ((∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2) * (n : ℝ) := by
    have hproj : Measurable (fun y : ℕ → X ↦ fun i : Fin n ↦ y i) := by
      fun_prop
    have htest : Measurable (fun y : Fin n → X ↦ (∑ i, f (y i)) ^ 2) := by
      fun_prop
    calc
      _ = ∫ y : Fin n → X, (∑ i, f (y i)) ^ 2
          ∂(Measure.infinitePi (fun _ : ℕ ↦ ν)).map
            (fun y : ℕ → X ↦ fun i : Fin n ↦ y i) :=
        (integral_map hproj.aemeasurable htest.aestronglyMeasurable).symm
      _ = ∫ y : Fin n → X, (∑ i, f (y i)) ^ 2 ∂Measure.pi (fun _ ↦ ν) := by
        rw [infinitePi_map_fin]
      _ = _ := by
        simpa only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_one, one_pow] using
          integral_iid_weighted_sum_sq ν hf hB hbound (fun _ : Fin n ↦ (1 : ℝ))
  rw [integral_prod _ (memLp_two_poissonPrefixSum ν r hf hbound).integrable_sq]
  change (∫ n, ∫ y : ℕ → X, (∑ i : Fin n, f (y i)) ^ 2
    ∂Measure.infinitePi (fun _ : ℕ ↦ ν) ∂poissonMeasure r) = _
  simp_rw [hfixed]
  rw [integral_add
    ((integrable_sq_id_poissonMeasure r).const_mul _)
    ((integrable_id_poissonMeasure r).const_mul _), integral_const_mul,
    integral_const_mul, integral_sq_id_poissonMeasure, integral_id_poissonMeasure]
  ring

/-- Exact variance of a signed spatial test of the original Poisson input. -/
theorem variance_poissonPrefixSum
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) :
    variance (poissonPrefixSum f)
      ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) =
      (r : ℝ) * ∫ x, (f x) ^ 2 ∂ν := by
  rw [variance_eq_sub (memLp_two_poissonPrefixSum ν r hf hbound)]
  change (∫ z, (poissonPrefixSum f z) ^ 2
      ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν)))) -
      (∫ z, poissonPrefixSum f z
        ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν)))) ^ 2 = _
  rw [integral_sq_poissonPrefixSum ν r hf hB hbound,
    integral_poissonPrefixSum ν r hf hbound]
  ring

/-- The centered stochastic integral has the intensity-weighted squared-test moment. -/
theorem integral_sq_centered_poissonPrefixSum
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) :
    (∫ z, (poissonPrefixSum f z - (r : ℝ) * ∫ x, f x ∂ν) ^ 2
      ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν)))) =
      (r : ℝ) * ∫ x, (f x) ^ 2 ∂ν := by
  rw [← integral_poissonPrefixSum ν r hf hbound,
    ← variance_eq_integral (measurable_poissonPrefixSum hf).aemeasurable]
  exact variance_poissonPrefixSum ν r hf hB hbound

/-- A zero-mean spatial weight requires no compensation term. -/
theorem integral_sq_poissonPrefixSum_of_integral_eq_zero
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) (hmean : ∫ x, f x ∂ν = 0) :
    (∫ z, (poissonPrefixSum f z) ^ 2
      ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν)))) =
      (r : ℝ) * ∫ x, (f x) ^ 2 ∂ν := by
  simp only [integral_sq_poissonPrefixSum ν r hf hB hbound, hmean, mul_zero,
    zero_pow (by norm_num : 2 ≠ 0), add_zero]

/-- A deterministic spatial support gives the boundary-layer variance bound directly. -/
theorem integral_sq_centered_poissonPrefixSum_le_support
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) {S : Set X} (hS : MeasurableSet S)
    (hsupport : ∀ x, x ∉ S → f x = 0) :
    (∫ z, (poissonPrefixSum f z - (r : ℝ) * ∫ x, f x ∂ν) ^ 2
      ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν)))) ≤
      (r : ℝ) * B ^ 2 * ν.real S := by
  rw [integral_sq_centered_poissonPrefixSum ν r hf hB hbound]
  have hsq : Integrable (fun x ↦ (f x) ^ 2) ν :=
    (MemLp.of_bound hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall hbound) : MemLp f 2 ν).integrable_sq
  have hle : ∀ x, (f x) ^ 2 ≤ S.indicator (fun _ ↦ B ^ 2) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      exact (sq_abs (f x)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (hbound x) 2
    · simp [hsupport x hx, hx]
  calc
    _ ≤ (r : ℝ) * ∫ x, S.indicator (fun _ ↦ B ^ 2) x ∂ν :=
      mul_le_mul_of_nonneg_left (integral_mono hsq
        ((integrable_const (B ^ 2)).indicator hS) hle) r.coe_nonneg
    _ = _ := by rw [integral_indicator_const _ hS]; simp only [smul_eq_mul]; ring

/-- The law transfer keeps an arbitrary original experiment on its own probability space. -/
theorem memLp_two_poissonPrefixSum_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {Z : Ω → ℕ × (ℕ → X)}
    (hZ : HasLaw Z ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) P)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hbound : ∀ x, |f x| ≤ B) :
    MemLp (fun ω ↦ poissonPrefixSum f (Z ω)) 2 P := by
  have h := memLp_two_poissonPrefixSum ν r hf hbound
  rw [← hZ.map_eq] at h
  exact h.comp_of_map hZ.aemeasurable

/-- Exact compensated variance after transfer of the full original count-and-points law. -/
theorem integral_sq_centered_poissonPrefixSum_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {Z : Ω → ℕ × (ℕ → X)}
    (hZ : HasLaw Z ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) P)
    {f : X → ℝ} (hf : Measurable f) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, |f x| ≤ B) :
    (∫ ω, (poissonPrefixSum f (Z ω) - (r : ℝ) * ∫ x, f x ∂ν) ^ 2 ∂P) =
      (r : ℝ) * ∫ x, (f x) ^ 2 ∂ν := by
  have htest : Measurable (fun z : ℕ × (ℕ → X) ↦
      (poissonPrefixSum f z - (r : ℝ) * ∫ x, f x ∂ν) ^ 2) := by
    exact ((measurable_poissonPrefixSum hf).sub measurable_const).pow_const 2
  calc
    _ = ∫ z, (poissonPrefixSum f z - (r : ℝ) * ∫ x, f x ∂ν) ^ 2
        ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) :=
      hZ.integral_comp htest.aestronglyMeasurable
    _ = _ := integral_sq_centered_poissonPrefixSum ν r hf hB hbound

end OTSelector.Probability
