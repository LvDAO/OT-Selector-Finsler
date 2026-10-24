import Mathlib.Probability.Moments.Variance
import OTSelector.Probability.DirichletQuadraticMoments
import OTSelector.Probability.DirichletReference
import OTSelector.Probability.IIDWeightedSecondMoment
import OTSelector.Probability.SecondMomentMassTails

/-!
Conditions: The unchanged product of iid target positions and independent genuine Dirichlet weights, and any bounded measurable signed test.

Objects: The actual weighted readout, exact centered variance factor 2/(n+2), its Chebyshev deviation bound and the signed scalar weak law.

Proof detail: Expand the weighted second moment using actual iid pair moments and exact Dirichlet diagonal moments. Subtract the square of the mean and apply Chebyshev to the resulting vanishing variance.

References: Thomas P. Minka: Section 1, equations (1)–(3), p. 1; equations (19)–(20), p. 2; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: A weighted LLN proved on the original weighted experiment. An unweighted sample law is not substituted, and arbitrary signed bounded tests are supported.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.OriginalWeightedTargetLLN.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.OriginalWeightedTargetLLN`; the selected original proof blocks follow. -/
section

/-!
# Signed weak laws for the original Dirichlet-weighted target experiment

The product law is the unchanged original iid-targets times Dirichlet law. Exact iid pair
moments and the original Dirichlet diagonal moment give the signed centered variance and a
vanishing deviation probability. No unweighted sample or different experiment is substituted.
-/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section
namespace OTSelector.Probability

set_option backward.isDefEq.respectTransparency false

variable {S : Type*} [MeasurableSpace S]

/-- A signed target test under the original target tuple and original Dirichlet weights. -/
def originalDirichletWeightedTargetTest (n : ℕ) (f : S → ℝ)
    (z : (Fin (n + 1) → S) × (Fin (n + 1) → ℝ)) : ℝ :=
  ∑ i, z.2 i * f (z.1 i)

/-- The actual signed weighted test is measurable in the original experiment. -/
theorem measurable_originalDirichletWeightedTargetTest (n : ℕ)
    {f : S → ℝ} (hf : Measurable f) :
    Measurable (originalDirichletWeightedTargetTest n f) := by
  unfold originalDirichletWeightedTargetTest
  exact Finset.measurable_sum _ fun i _ ↦
    ((measurable_pi_apply i).comp measurable_snd).mul
      (hf.comp ((measurable_pi_apply i).comp measurable_fst))

omit [MeasurableSpace S] in
/-- Simplex weights retain the original global absolute test bound. -/
theorem norm_originalDirichletWeightedTargetTest_le (n : ℕ)
    {f : S → ℝ} {B : ℝ} (hbound : ∀ x, |f x| ≤ B)
    {p : Fin (n + 1) → ℝ} (hp : p ∈ stdSimplex ℝ (Fin (n + 1)))
    (y : Fin (n + 1) → S) : ‖originalDirichletWeightedTargetTest n f (y, p)‖ ≤ B := by
  calc
    ‖originalDirichletWeightedTargetTest n f (y, p)‖ ≤ ∑ i, ‖p i * f (y i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, p i * B := Finset.sum_le_sum fun i _ ↦ by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hp.1 i)]
      exact mul_le_mul_of_nonneg_left (hbound (y i)) (hp.1 i)
    _ = B := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- Every power of the actual bounded signed test is integrable under targets times weights. -/
theorem integrable_originalDirichletWeightedTargetTest_pow (n : ℕ)
    (ν : Measure S) [IsProbabilityMeasure ν] {f : S → ℝ} (hf : Measurable f)
    {B : ℝ} (_hB : 0 ≤ B) (hbound : ∀ x, |f x| ≤ B) (k : ℕ) :
    Integrable (fun z ↦ originalDirichletWeightedTargetTest n f z ^ k)
      ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) := by
  have hsimplex : ∀ᵐ z ∂(Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n),
      z.2 ∈ stdSimplex ℝ (Fin (n + 1)) := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    simpa only [Measure.map_snd_prod, measure_univ, one_smul] using
      ae_mem_stdSimplex_dirichletOne n
  have hm : Measurable (fun z ↦ originalDirichletWeightedTargetTest n f z ^ k) :=
    (measurable_originalDirichletWeightedTargetTest n hf).pow_const k
  refine Integrable.of_bound hm.aestronglyMeasurable (B ^ k) ?_
  filter_upwards [hsimplex] with z hz
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_originalDirichletWeightedTargetTest_le n hbound hz z.1) k

/-- Exact signed second moment under the actual original product order targets times Dirichlet. -/
theorem integral_originalDirichletWeightedTargetTest_sq (n : ℕ)
    (ν : Measure S) [IsProbabilityMeasure ν] {f : S → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, |f x| ≤ B) :
    (∫ z, originalDirichletWeightedTargetTest n f z ^ 2
      ∂(Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) =
      (∫ x, f x ∂ν) ^ 2 +
        ((∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2) * (2 / ((n : ℝ) + 2)) := by
  rw [integral_prod_symm _
    (integrable_originalDirichletWeightedTargetTest_pow n ν hf hB hbound 2)]
  have hinner : (fun p : Fin (n + 1) → ℝ ↦
      ∫ y, originalDirichletWeightedTargetTest n f (y, p) ^ 2
        ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν)) =ᵐ[dirichletOne n]
      (fun p ↦ (∫ x, f x ∂ν) ^ 2 +
        ((∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2) * ∑ i, p i ^ 2) := by
    filter_upwards [ae_mem_stdSimplex_dirichletOne n] with p hp
    change (∫ y, (∑ i, p i * f (y i)) ^ 2 ∂Measure.pi (fun _ ↦ ν)) = _
    rw [integral_iid_weighted_sum_sq ν hf hB hbound p, hp.2]
    ring
  rw [integral_congr_ae hinner,
    integral_add (integrable_const _) ((integrable_finsetSum _
      (fun i _ ↦ integrable_dirichletOne_coordinate_pow n i 2)).const_mul _),
    integral_const_mul, integral_dirichletOne_sum_sq]
  simp only [integral_const, probReal_univ, one_smul]

/-- The actual signed weighted deviation is square-integrable, with its exact centered second
moment. The original iid target tuple is the first factor and Dirichlet weights the second. -/
theorem originalDirichletWeightedTargetTest_centered_sq (n : ℕ)
    (ν : Measure S) [IsProbabilityMeasure ν] {f : S → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, |f x| ≤ B) :
    Integrable (fun z ↦ (originalDirichletWeightedTargetTest n f z - ∫ x, f x ∂ν) ^ 2)
      ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) ∧
    (∫ z, (originalDirichletWeightedTargetTest n f z - ∫ x, f x ∂ν) ^ 2
      ∂(Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) =
      (2 / ((n : ℝ) + 2)) *
        ((∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2) := by
  let m : ℝ := ∫ x, f x ∂ν
  let centered : S → ℝ := fun x ↦ f x - m
  have hfc : Measurable centered := hf.sub_const m
  have hC : 0 ≤ B + |m| := add_nonneg hB (abs_nonneg _)
  have hcbound (x : S) : |centered x| ≤ B + |m| := by
    calc
      |centered x| ≤ |f x| + |m| := by
        simpa only [centered, sub_zero, zero_sub, abs_neg] using abs_sub_le (f x) 0 m
      _ ≤ B + |m| := add_le_add (hbound x) le_rfl
  have hfi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hbound x)
  have hcenterMean : (∫ x, centered x ∂ν) = 0 := by
    rw [show centered = fun x ↦ f x - m from rfl,
      integral_sub hfi (integrable_const m), integral_const, probReal_univ, one_smul]
    exact sub_self _
  have hMemLp : MemLp f 2 ν := MemLp.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hbound x)
  have hcenterSq : (∫ x, (centered x) ^ 2 ∂ν) = (∫ x, (f x) ^ 2 ∂ν) - m ^ 2 :=
    (variance_eq_integral hf.aemeasurable).symm.trans (variance_eq_sub hMemLp)
  have hsimplex : ∀ᵐ z ∂(Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n),
      z.2 ∈ stdSimplex ℝ (Fin (n + 1)) := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    simpa only [Measure.map_snd_prod, measure_univ, one_smul] using
      ae_mem_stdSimplex_dirichletOne n
  have hcenterAE :
      (fun z ↦ (originalDirichletWeightedTargetTest n f z - m) ^ 2) =ᵐ[
        (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)]
      (fun z ↦ originalDirichletWeightedTargetTest n centered z ^ 2) := by
    filter_upwards [hsimplex] with z hz
    congr 1
    dsimp only [originalDirichletWeightedTargetTest, centered]
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hz.2, one_mul]
  refine ⟨(integrable_originalDirichletWeightedTargetTest_pow n ν hfc hC hcbound 2).congr
    hcenterAE.symm, ?_⟩
  rw [integral_congr_ae hcenterAE,
    integral_originalDirichletWeightedTargetTest_sq n ν hfc hC hcbound,
    hcenterMean, hcenterSq]
  simp only [zero_pow (by norm_num : 2 ≠ 0), zero_add, sub_zero]
  exact mul_comm _ _

/-- Quantitative deviation probability for the original signed Dirichlet-weighted target test. -/
theorem measureReal_originalDirichletWeightedTargetTest_deviation_le (n : ℕ)
    (ν : Measure S) [IsProbabilityMeasure ν] {f : S → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, |f x| ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)).real
      {z | ε ≤ |originalDirichletWeightedTargetTest n f z - ∫ x, f x ∂ν|} ≤
      ((2 / ((n : ℝ) + 2)) *
        ((∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2)) / ε ^ 2 := by
  obtain ⟨hint, hsecond⟩ := originalDirichletWeightedTargetTest_centered_sq n ν hf hB hbound
  have hintAbs : Integrable
      (fun z ↦ |originalDirichletWeightedTargetTest n f z - ∫ x, f x ∂ν| ^ 2)
      ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) := by
    simpa only [sq_abs] using hint
  apply probability_mass_tail_le_of_second_moment hintAbs _ hε
  simpa only [sq_abs] using hsecond.le

/-- Every bounded measurable signed target test converges in probability under the original
independent iid-targets times Dirichlet experiment, with no relation between different rows. -/
theorem tendsto_measureReal_originalDirichletWeightedTargetTest_deviation
    (ν : Measure S) [IsProbabilityMeasure ν] {f : S → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, |f x| ≤ B) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦
      ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)).real
        {z | ε ≤ |originalDirichletWeightedTargetTest n f z - ∫ x, f x ∂ν|})
      atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hrate : Tendsto (fun n : ℕ ↦ ((2 / ((n : ℝ) + 2)) *
      ((∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2)) / ε ^ 2) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, Function.comp_def, mul_zero, zero_mul] using
      (((tendsto_const_nhds (x := (2 : ℝ))).mul
        (tendsto_inv_atTop_zero.comp hden)).mul_const
          ((∫ x, (f x) ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2)).div_const (ε ^ 2)
  exact squeeze_zero (fun _ ↦ measureReal_nonneg)
    (fun n ↦ measureReal_originalDirichletWeightedTargetTest_deviation_le n ν hf hB hbound hε)
    hrate

end OTSelector.Probability

end
end
