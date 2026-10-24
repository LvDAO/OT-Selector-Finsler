import OTSelector.Reconstruction.FinslerOriginalConditionalMoments
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Compliance moments uniform over conditional paired laws

The two actual marginal moments bound the compliance difference under every
coupling of those marginals. The bound uses only the fixed root's marginal moments
and the sharp elementary power-sum constant, so it does not depend on the pairing.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator ENNReal

namespace OTSelector.Reconstruction

/-- The power of a norm difference is bounded by the two separate powers. -/
theorem norm_sub_rpow_le_marginal_sum {E : Type*} [NormedAddCommGroup E]
    (x y : E) {r : ℝ} (hr : 0 ≤ r) :
    ‖x - y‖ ^ r ≤ (2 : ℝ) ^ max (r - 1) 0 * (‖x‖ ^ r + ‖y‖ ^ r) := by
  apply (Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le x y) hr).trans
  by_cases hr1 : r ≤ 1
  · rw [max_eq_right (sub_nonpos.mpr hr1), Real.rpow_zero, one_mul]
    exact Real.rpow_add_le_add_rpow (norm_nonneg _) (norm_nonneg _) hr hr1
  · rw [max_eq_left (sub_nonneg.mpr (le_of_not_ge hr1))]
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ‖x‖₊ ‖y‖₊ (le_of_not_ge hr1)

/-- Any pairing has the same marginal moment bound for its compliance difference;
no independence or monotone-support assumption on the pairing is needed. -/
theorem paired_norm_sub_rpow_integrable_bound
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [NormedAddCommGroup E]
    {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}
    (hπ : Vlasov.IsCoupling π μ ν) {f : X → E} {g : Y → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g ν)
    {r : ℝ} (hr : 0 ≤ r)
    (hfm : Integrable (fun x ↦ ‖f x‖ ^ r) μ)
    (hgm : Integrable (fun y ↦ ‖g y‖ ^ r) ν) :
    Integrable (fun p ↦ ‖g p.2 - f p.1‖ ^ r) π ∧
      (∫ p, ‖g p.2 - f p.1‖ ^ r ∂π) ≤ (2 : ℝ) ^ max (r - 1) 0 *
        ((∫ x, ‖f x‖ ^ r ∂μ) + ∫ y, ‖g y‖ ^ r ∂ν) := by
  have hfm' : Integrable (fun x ↦ ‖f x‖ ^ r) (π.map Prod.fst) := hπ.1.symm ▸ hfm
  have hgm' : Integrable (fun y ↦ ‖g y‖ ^ r) (π.map Prod.snd) := hπ.2.symm ▸ hgm
  have hf' : AEStronglyMeasurable f (π.map Prod.fst) := hπ.1.symm ▸ hf
  have hg' : AEStronglyMeasurable g (π.map Prod.snd) := hπ.2.symm ▸ hg
  have hfst := hfm'.comp_measurable measurable_fst
  have hsnd := hgm'.comp_measurable measurable_snd
  simp only [Function.comp_def] at hfst hsnd
  have hb : Integrable (fun p : X × Y ↦ (2 : ℝ) ^ max (r - 1) 0 *
      (‖f p.1‖ ^ r + ‖g p.2‖ ^ r)) π := (hfst.add hsnd).const_mul _
  have hm : AEStronglyMeasurable (fun p : X × Y ↦ ‖g p.2 - f p.1‖ ^ r) π :=
    (Real.continuous_rpow_const hr).comp_aestronglyMeasurable
      ((hg'.comp_measurable measurable_snd).sub (hf'.comp_measurable measurable_fst)).norm
  have hbnd (p : X × Y) : ‖g p.2 - f p.1‖ ^ r ≤
      (2 : ℝ) ^ max (r - 1) 0 * (‖f p.1‖ ^ r + ‖g p.2‖ ^ r) := by
    simpa only [add_comm] using norm_sub_rpow_le_marginal_sum (g p.2) (f p.1) hr
  have hi : Integrable (fun p : X × Y ↦ ‖g p.2 - f p.1‖ ^ r) π :=
    hb.mono' hm (Filter.Eventually.of_forall fun p ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        using hbnd p)
  refine ⟨hi, ?_⟩
  calc
    (∫ p, ‖g p.2 - f p.1‖ ^ r ∂π) ≤
        ∫ p, (2 : ℝ) ^ max (r - 1) 0 * (‖f p.1‖ ^ r + ‖g p.2‖ ^ r) ∂π :=
      integral_mono_ae hi hb (Filter.Eventually.of_forall hbnd)
    _ = (2 : ℝ) ^ max (r - 1) 0 *
        ((∫ x, ‖f x‖ ^ r ∂μ) + ∫ y, ‖g y‖ ^ r ∂ν) := by
      rw [integral_const_mul, integral_add hfst hsnd]
      rw [← integral_map measurable_fst.aemeasurable hfm'.aestronglyMeasurable,
        ← integral_map measurable_snd.aemeasurable hgm'.aestronglyMeasurable, hπ.1, hπ.2]

end OTSelector.Reconstruction
