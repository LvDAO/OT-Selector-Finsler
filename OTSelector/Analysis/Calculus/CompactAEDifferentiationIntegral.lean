import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Analysis.Calculus.CompactAEDifferentiationIntegral

Conditions: A finite measure, an a.e. compact-valued measurable center phase, bounded measurable perturbation and the actual differentiability/compact continuity hypotheses.

Objects: A.e. strong measurability of the composition and derivative of the parameterized integral.

Proof detail: Use compact separability/continuity for measurable composition, bound the perturbation tube uniformly on a compact set, and apply dominated differentiation.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/html/sec_diffunderint.html): Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters).
- [Rick Durrett, Probability](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=38): Section 1.6.2, Theorems 1.6.5–1.6.7 (Fatou, monotone convergence, dominated convergence), p. 30.

Source relation: Dominated Leibniz/Bochner extension with compact a.e. phases. The uniform majorant is constructed from the given hypotheses.
-/

/-!
# First variation with a measurable compact central phase

A C1 function on an open finite-dimensional phase domain can be differentiated under
an integral along bounded measurable additive perturbations. The central phase is
only assumed almost everywhere to lie in a compact subset of the domain. Compactness
constructs the common parameter neighborhood and integrable derivative bound.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal

noncomputable section

namespace OTSelector.Geometry

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {α : Type*} [MeasurableSpace α] {μ : Measure α}

omit [NormedSpace ℝ H] [FiniteDimensional ℝ H] in
private theorem aestronglyMeasurable_comp_of_continuousOn_ae
    {f : H → ℝ} {U : Set H} (hU : IsOpen U) (hf : ContinuousOn f U)
    {z : α → H} (hz : AEStronglyMeasurable z μ) (hzU : ∀ᵐ t ∂μ, z t ∈ U) :
    AEStronglyMeasurable (fun t ↦ f (z t)) μ := by
  classical
  borelize H
  have hm : Measurable (U.piecewise f 0) :=
    hf.measurable_piecewise continuous_zero.continuousOn hU.measurableSet
  apply ((hm.comp_aemeasurable hz.aemeasurable).aestronglyMeasurable).congr
  filter_upwards [hzU] with t ht
  exact piecewise_eq_of_mem U f 0 ht

/-- A bounded measurable phase perturbation admits the actual first variation under
any finite measure. Compact central phase containment supplies the common admissible
parameter neighborhood, measurability, integrability and derivative domination. -/
theorem hasDerivAt_integral_add_smul_of_compact_ae [IsFiniteMeasure μ]
    {L : H → ℝ} {U K : Set H} (hU : IsOpen U) (hL : ContDiffOn ℝ 1 L U)
    (hK : IsCompact K) (hKU : K ⊆ U) {z w : α → H} {C : ℝ≥0}
    (hz : AEStronglyMeasurable z μ) (hzK : ∀ᵐ t ∂μ, z t ∈ K)
    (hw : AEStronglyMeasurable w μ) (hwC : ∀ᵐ t ∂μ, ‖w t‖ ≤ (C : ℝ)) :
    Integrable (fun t ↦ fderiv ℝ L (z t) (w t)) μ ∧
      HasDerivAt (fun s : ℝ ↦ ∫ t, L (z t + s • w t) ∂μ)
        (∫ t, fderiv ℝ L (z t) (w t) ∂μ) 0 := by
  obtain ⟨δ₁, hδ₁, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨δ₂, hδ₂, hδK⟩ := hK.exists_isCompact_cthickening
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  let S := cthickening δ K
  have hSU : S ⊆ U := (cthickening_mono (min_le_left δ₁ δ₂) K).trans hδU
  have hS : IsCompact S := hδK.of_isClosed_subset isClosed_cthickening
    (cthickening_mono (min_le_right δ₁ δ₂) K)
  have hD : ContinuousOn (fderiv ℝ L) U := hL.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn (hD.mono hSU)
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn (hL.continuousOn.mono hKU)
  let r := δ / ((C : ℝ) + 1)
  have hC₁ : 0 < (C : ℝ) + 1 := by positivity
  have hr : 0 < r := div_pos hδ hC₁
  have hrC : r * (C : ℝ) ≤ δ := by
    calc
      r * (C : ℝ) ≤ r * ((C : ℝ) + 1) := mul_le_mul_of_nonneg_left (by linarith) hr.le
      _ = δ := div_mul_cancel₀ δ hC₁.ne'
  have hphase : ∀ᵐ t ∂μ, ∀ s ∈ ball (0 : ℝ) r, z t + s • w t ∈ S := by
    filter_upwards [hzK, hwC] with t ht hwt s hs
    apply mem_cthickening_of_dist_le _ (z t) δ K ht
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hs' : |s| < r := by
      simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hs
    exact (mul_le_mul hs'.le hwt (norm_nonneg _) hr.le).trans hrC
  have hmeas : ∀ᶠ s in 𝓝 (0 : ℝ),
      AEStronglyMeasurable (fun t ↦ L (z t + s • w t)) μ := by
    filter_upwards [ball_mem_nhds (0 : ℝ) hr] with s hs
    apply aestronglyMeasurable_comp_of_continuousOn_ae hU hL.continuousOn
      (hz.add (hw.const_smul s))
    exact hphase.mono (fun t ht ↦ hSU (ht s hs))
  have hint : Integrable (fun t ↦ L (z t + (0 : ℝ) • w t)) μ := by
    simp only [zero_smul, add_zero]
    apply Integrable.of_bound
      (aestronglyMeasurable_comp_of_continuousOn_ae hU hL.continuousOn hz
        (hzK.mono (fun _ ht ↦ hKU ht))) A
    exact hzK.mono (fun t ht ↦ hA (z t) ht)
  have hpair : ContinuousOn (fun p : H × H ↦ fderiv ℝ L p.1 p.2) (U ×ˢ univ) :=
    (hD.comp continuous_fst.continuousOn (fun _ hp ↦ hp.1)).clm_apply
      continuous_snd.continuousOn
  have hdmeas : AEStronglyMeasurable (fun t ↦ fderiv ℝ L (z t) (w t)) μ :=
    aestronglyMeasurable_comp_of_continuousOn_ae (hU.prod isOpen_univ) hpair
      (hz.prodMk hw) (hzK.mono (fun _ ht ↦ ⟨hKU ht, mem_univ _⟩))
  have hbound : ∀ᵐ t ∂μ, ∀ s ∈ ball (0 : ℝ) r,
      ‖fderiv ℝ L (z t + s • w t) (w t)‖ ≤ max B 0 * (C : ℝ) := by
    filter_upwards [hphase, hwC] with t ht hwt s hs
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul ((hB _ (ht s hs)).trans (le_max_left _ _)) hwt
        (norm_nonneg _) (le_max_right _ _))
  have hdiff : ∀ᵐ t ∂μ, ∀ s ∈ ball (0 : ℝ) r,
      HasDerivAt (fun u : ℝ ↦ L (z t + u • w t))
        (fderiv ℝ L (z t + s • w t) (w t)) s := by
    filter_upwards [hphase] with t ht s hs
    have hdL := (hL.contDiffAt (hU.mem_nhds (hSU (ht s hs)))).differentiableAt_one
    have hd := hdL.hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_const s (z t)).add ((hasDerivAt_id s).smul_const (w t)))
    simpa only [Function.comp_def, Pi.add_apply, id_eq, one_smul, zero_add] using! hd
  have hdmeas₀ : AEStronglyMeasurable
      (fun t ↦ fderiv ℝ L (z t + (0 : ℝ) • w t) (w t)) μ := by
    simpa only [zero_smul, add_zero] using hdmeas
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds (0 : ℝ) hr) hmeas hint hdmeas₀ hbound (integrable_const _) hdiff
  simpa only [zero_smul, add_zero] using h

end OTSelector.Geometry
