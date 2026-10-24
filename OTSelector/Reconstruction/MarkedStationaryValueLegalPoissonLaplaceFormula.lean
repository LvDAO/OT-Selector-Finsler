import OTSelector.Reconstruction.MarkedStationaryValueLegalInputLaplace
import OTSelector.Probability.PoissonPrefixMoments
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowMoment
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Analytic Laplace functional of the literal original Poisson prefix

The formula is proved from the actual original Poisson count and its actual
independent iid observations. It applies directly to the finite original block
arrays, without postulating their Laplace functional or any transformed law.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The actual Poisson probability generating function, derived from its
original weighted exponential series. -/
theorem integral_pow_poissonMeasure_eq_exp (r : ℝ≥0) (a : ℝ) :
    (∫ n : ℕ, a ^ n ∂poissonMeasure r) = Real.exp ((r : ℝ) * (a - 1)) := by
  rw [integral_poissonMeasure r]
  simp only [smul_eq_mul]
  calc
    _ = ∑' n : ℕ, Real.exp (-(r : ℝ)) * (((r : ℝ) * a) ^ n / (n.factorial : ℝ)) := by
      congr 1
      funext n
      rw [mul_pow]
      ring
    _ = Real.exp (-(r : ℝ)) * ∑' n : ℕ, (((r : ℝ) * a) ^ n / (n.factorial : ℝ)) := tsum_mul_left
    _ = Real.exp (-(r : ℝ)) * Real.exp ((r : ℝ) * a) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * a)).tsum_eq, ← Real.exp_eq_exp_ℝ]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

variable {X : Type*} [MeasurableSpace X]

/-- The literal Poisson prefix Laplace readout is integrable because the
original test is nonnegative at every used observation. -/
theorem integrable_exp_neg_poissonPrefixSum (ν : Measure X) [IsProbabilityMeasure ν]
    (r : ℝ≥0) {f : X → ℝ} (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x) :
    Integrable (fun z ↦ Real.exp (-poissonPrefixSum f z))
      ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_poissonPrefixSum hf).neg.exp.aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun i _ ↦ hfn (z.2 i)))

/-- The complete analytic Laplace formula of the unchanged original used
prefix follows from its actual finite iid products and original count law. -/
theorem integral_exp_neg_poissonPrefixSum_eq (ν : Measure X) [IsProbabilityMeasure ν]
    (r : ℝ≥0) {f : X → ℝ} (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x) :
    (∫ z, Real.exp (-poissonPrefixSum f z)
      ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν)))) =
      Real.exp ((r : ℝ) * ((∫ x, Real.exp (-f x) ∂ν) - 1)) := by
  have hfixed (n : ℕ) :
      (∫ seq : ℕ → X, Real.exp (-(∑ i : Fin n, f (seq i)))
        ∂Measure.infinitePi (fun _ : ℕ ↦ ν)) = (∫ x, Real.exp (-f x) ∂ν) ^ n := by
    have hmap := infinitePi_map_fin ν n
    have hseq : Measurable (fun seq : ℕ → X ↦ fun i : Fin n ↦ seq i) :=
      measurable_pi_lambda _ (fun i ↦ measurable_pi_apply (i : ℕ))
    have hfm : Measurable (fun v : Fin n → X ↦ Real.exp (-(∑ i : Fin n, f (v i)))) :=
      (Finset.measurable_sum _ (fun i _ ↦ hf.comp (measurable_pi_apply i))).neg.exp
    calc
      _ = ∫ v : Fin n → X, Real.exp (-(∑ i : Fin n, f (v i)))
          ∂(Measure.infinitePi (fun _ : ℕ ↦ ν)).map (fun seq : ℕ → X ↦ fun i : Fin n ↦ seq i) := by
        simpa only [Function.comp_def] using
          (integral_map hseq.aemeasurable hfm.aestronglyMeasurable).symm
      _ = ∫ v : Fin n → X, Real.exp (-(∑ i : Fin n, f (v i)))
          ∂Measure.pi (fun _ : Fin n ↦ ν) := by rw [hmap]
      _ = ∫ v : Fin n → X, ∏ i : Fin n, Real.exp (-f (v i))
          ∂Measure.pi (fun _ : Fin n ↦ ν) := by
        apply integral_congr_ae
        filter_upwards with v
        rw [← Finset.sum_neg_distrib, Real.exp_sum]
      _ = _ := by
        simpa only [Fintype.card_fin] using
          (integral_fintype_prod_eq_pow (ι := Fin n) (μ := ν) (fun x ↦ Real.exp (-f x)))
  rw [integral_prod _ (integrable_exp_neg_poissonPrefixSum ν r hf hfn)]
  change (∫ n, (∫ seq : ℕ → X, Real.exp (-(∑ i : Fin n, f (seq i)))
    ∂Measure.infinitePi (fun _ : ℕ ↦ ν)) ∂poissonMeasure r) = _
  simp_rw [hfixed]
  exact integral_pow_poissonMeasure_eq_exp r _

private theorem measurable_finiteOriginalPrefixEncode :
    Measurable (fun z : ℕ × (ℕ → X) ↦ (⟨z.1, fun i : Fin z.1 ↦ z.2 i⟩ : BlockData X)) := by
  apply measurable_from_prod_countable_right
  intro n
  exact (measurable_sigma_mk n).comp (measurable_pi_lambda _
    (fun i : Fin n ↦ measurable_pi_apply (i : ℕ)))

/-- The original Poisson finite array law is a probability law, including
zero intensity. This follows from its actual count-and-iid encoding. -/
theorem isProbabilityMeasure_originalPoissonBlockDataLaw
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0) :
    IsProbabilityMeasure (blockDataLaw ν (fun n ↦ poissonMeasure r {n})) := by
  rw [blockDataLaw_eq_map_cloud]
  exact Measure.isProbabilityMeasure_map measurable_finiteOriginalPrefixEncode.aemeasurable

/-- The literal original finite BlockData law has its analytic Poisson
Laplace formula, with no replacement of either points or count. -/
theorem integral_exp_neg_legalInputBlockTest_eq (ν : Measure X) [IsProbabilityMeasure ν]
    (r : ℝ≥0) {f : X → ℝ} (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x) :
    (∫ b : BlockData X, Real.exp (-legalInputBlockTest f b)
      ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) =
      Real.exp ((r : ℝ) * ((∫ x, Real.exp (-f x) ∂ν) - 1)) := by
  have hm : Measurable (fun b : BlockData X ↦ Real.exp (-legalInputBlockTest f b)) := by
    simpa only [Pi.neg_apply] using (measurable_legalInputBlockTest hf).neg.exp
  rw [blockDataLaw_eq_map_cloud,
    integral_map measurable_finiteOriginalPrefixEncode.aemeasurable hm.aestronglyMeasurable]
  exact integral_exp_neg_poissonPrefixSum_eq ν r hf hfn

/-- The analytic Laplace functional of the two original finite color blocks,
including different original count intensities. -/
theorem integral_legalInputBlockLaplace_eq_exp
    (ν ρ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (rS rT : ℝ≥0) {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (∫ b, legalInputBlockLaplace f g b ∂
      (blockDataLaw ν (fun n ↦ poissonMeasure rS {n})).prod
        (blockDataLaw ρ (fun n ↦ poissonMeasure rT {n}))) =
      Real.exp ((rS : ℝ) * ((∫ x, Real.exp (-f x) ∂ν) - 1) +
        (rT : ℝ) * ((∫ y, Real.exp (-g y) ∂ρ) - 1)) := by
  have : IsProbabilityMeasure (blockDataLaw ν (fun n ↦ poissonMeasure rS {n})) :=
    isProbabilityMeasure_originalPoissonBlockDataLaw ν rS
  have : IsProbabilityMeasure (blockDataLaw ρ (fun n ↦ poissonMeasure rT {n})) :=
    isProbabilityMeasure_originalPoissonBlockDataLaw ρ rT
  have heq : legalInputBlockLaplace f g = fun b : BlockData X × BlockData X ↦
      Real.exp (-legalInputBlockTest f b.1) * Real.exp (-legalInputBlockTest g b.2) := by
    funext b
    unfold legalInputBlockLaplace
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  change (∫ b : BlockData X × BlockData X,
    Real.exp (-legalInputBlockTest f b.1) * Real.exp (-legalInputBlockTest g b.2) ∂
      (blockDataLaw ν (fun n ↦ poissonMeasure rS {n})).prod
        (blockDataLaw ρ (fun n ↦ poissonMeasure rT {n}))) = _
  rw [integral_prod_mul (fun b : BlockData X ↦ Real.exp (-legalInputBlockTest f b))
    (fun b : BlockData X ↦ Real.exp (-legalInputBlockTest g b)),
    integral_exp_neg_legalInputBlockTest_eq ν rS hf hfn,
    integral_exp_neg_legalInputBlockTest_eq ρ rT hg hgn, ← Real.exp_add]

/-- The original physical-window Poisson arrays have the analytic Laplace
functional of their literal Haar-times-original-clock intensities. -/
theorem integral_legalInputPoissonWindowLaw_laplace_eq_exp
    (q : ℕ) {U : Set (Fin q → ℝ)} (hUfin : volume U ≠ ∞) (hUpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {f g : LegalMarkedPhysicalPoint q → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (∫ b, legalInputBlockLaplace f g b ∂legalInputPoissonWindowLaw q U α β) =
      Real.exp ((∫ x, (Real.exp (-f x) - 1)
        ∂((volume : Measure (Fin q → ℝ)).restrict U).prod α) +
          ∫ y, (Real.exp (-g y) - 1)
            ∂((volume : Measure (Fin q → ℝ)).restrict U).prod β) := by
  have : IsFiniteMeasure ((volume : Measure (Fin q → ℝ)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hUfin.lt_top⟩
  have hmass : 0 < ((volume : Measure (Fin q → ℝ)).restrict U).real univ := by
    rw [Measure.real, Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos hUpos hUfin
  let ν := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  have : IsProbabilityMeasure ν := normalizedFiniteLaw_probability _ hmass
  have hscale (γ : Measure ℝ) [IsProbabilityMeasure γ]
      (h : LegalMarkedPhysicalPoint q → ℝ) (hh : Measurable h) (hhn : ∀ x, 0 ≤ h x) :
      (((volume U).toNNReal : ℝ≥0) : ℝ) * ((∫ x, Real.exp (-h x) ∂ν.prod γ) - 1) =
        ∫ x, (Real.exp (-h x) - 1)
          ∂((volume : Measure (Fin q → ℝ)).restrict U).prod γ := by
    have hI : Integrable (fun x ↦ Real.exp (-h x)) (ν.prod γ) := by
      apply (integrable_const (1 : ℝ)).mono' hh.neg.exp.aestronglyMeasurable
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      exact neg_nonpos.mpr (hhn x)
    rw [← physicalIntensity_smul_normalized_window q hUfin hUpos γ, integral_smul_measure,
      integral_sub hI (integrable_const (1 : ℝ)), integral_const]
    simp only [probReal_univ, smul_eq_mul, mul_one]
    rfl
  change (∫ b, legalInputBlockLaplace f g b ∂
    (blockDataLaw (ν.prod α) (fun n ↦ poissonMeasure (volume U).toNNReal {n})).prod
      (blockDataLaw (ν.prod β) (fun n ↦ poissonMeasure (volume U).toNNReal {n}))) = _
  rw [integral_legalInputBlockLaplace_eq_exp (ν.prod α) (ν.prod β)
    (volume U).toNNReal (volume U).toNNReal hf hg hfn hgn,
    hscale α f hf hfn, hscale β g hg hgn]

end OTSelector.Reconstruction
