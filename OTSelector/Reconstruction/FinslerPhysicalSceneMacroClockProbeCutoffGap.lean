import OTSelector.Reconstruction.FinslerPhysicalSceneMacroClockCompactKernel

/-!
# Comparing the full macro-clock probe with its target cutoff

Finite physical plans integrate the bounded continuous probe.  Removing the
target cutoff pays the two actual planwise cutoff errors.
-/

open Set MeasureTheory
open scoped Topology ENNReal CompactlySupported

namespace OTSelector.Reconstruction

variable {ι : Type*} [Fintype ι]
local notation "V" => (ι → ℝ)
local notation "Point" => (V × ℝ)
local notation "Edge" => (Point × Point)

/-- The unchanged macro parameter and both clocks define a bounded continuous
probe, hence an integrable test for each finite physical plan. -/
theorem integrable_macro_clock_probe
    (π : Measure Edge) [IsFiniteMeasure π] (w : V)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ)) :
    Integrable (fun e : Edge ↦ η e.1.1 * g (w, (e.1.2, e.2.2))) π := by
  have hcontinuous : Continuous
      (fun e : Edge ↦ η e.1.1 * g (w, (e.1.2, e.2.2))) :=
    (η.continuous.comp continuous_fst.fst).mul
      (g.continuous.comp
        (continuous_const.prodMk (continuous_fst.snd.prodMk continuous_snd.snd)))
  refine Integrable.of_bound hcontinuous.aestronglyMeasurable
    (‖η.toBoundedContinuousFunction‖ * ‖g.toBoundedContinuousFunction‖)
    (ae_of_all _ fun e ↦ ?_)
  rw [norm_mul]
  exact mul_le_mul (η.toBoundedContinuousFunction.norm_coe_le_norm e.1.1)
    (g.toBoundedContinuousFunction.norm_coe_le_norm (w, (e.1.2, e.2.2)))
    (norm_nonneg _) (norm_nonneg _)

/-- A continuous target cutoff in `[0,1]` preserves integrability of the full
macro-clock probe under a finite physical plan. -/
theorem integrable_macro_clock_probe_cutoff
    (π : Measure Edge) [IsFiniteMeasure π] (w : V)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ))
    (χ : C_c(Point, ℝ)) (hχ : ∀ y, χ y ∈ Icc 0 1) :
    Integrable
      (fun e : Edge ↦ (η e.1.1 * g (w, (e.1.2, e.2.2))) * χ e.2) π := by
  refine (integrable_macro_clock_probe π w η g).mul_bdd (c := 1)
    (χ.continuous.comp continuous_snd).aestronglyMeasurable
    (ae_of_all _ fun e ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hχ e.2).1]
  exact (hχ e.2).2

/-- The full actual finite-plan macro-clock gap is bounded by its cutoff gap
and the cutoff loss in each of the same two plans. -/
theorem ofReal_abs_macro_clock_probe_gap_le_cutoff_gap_add_errors
    (πp πm : Measure Edge) [IsFiniteMeasure πp] [IsFiniteMeasure πm]
    (w : V) (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ))
    (χ : C_c(Point, ℝ)) (hχ : ∀ y, χ y ∈ Icc 0 1) :
    ENNReal.ofReal
      |(∫ e, η e.1.1 * g (w, (e.1.2, e.2.2)) ∂πp) -
        ∫ e, η e.1.1 * g (w, (e.1.2, e.2.2)) ∂πm| ≤
      ENNReal.ofReal
        |(∫ e, (η e.1.1 * g (w, (e.1.2, e.2.2))) * χ e.2 ∂πp) -
          ∫ e, (η e.1.1 * g (w, (e.1.2, e.2.2))) * χ e.2 ∂πm| +
        (∫⁻ e, ENNReal.ofReal
          |η e.1.1 * g (w, (e.1.2, e.2.2)) -
            (η e.1.1 * g (w, (e.1.2, e.2.2))) * χ e.2| ∂πp) +
        (∫⁻ e, ENNReal.ofReal
          |η e.1.1 * g (w, (e.1.2, e.2.2)) -
            (η e.1.1 * g (w, (e.1.2, e.2.2))) * χ e.2| ∂πm) := by
  let f : Edge → ℝ := fun e ↦ η e.1.1 * g (w, (e.1.2, e.2.2))
  let fc : Edge → ℝ := fun e ↦ f e * χ e.2
  have hfp : Integrable f πp := integrable_macro_clock_probe πp w η g
  have hfm : Integrable f πm := integrable_macro_clock_probe πm w η g
  have hfcp : Integrable fc πp := integrable_macro_clock_probe_cutoff πp w η g χ hχ
  have hfcm : Integrable fc πm := integrable_macro_clock_probe_cutoff πm w η g χ hχ
  have hp : edist (∫ e, f e ∂πp) (∫ e, fc e ∂πp) ≤
      ∫⁻ e, ENNReal.ofReal |f e - fc e| ∂πp := by
    simpa only [edist_dist, Real.dist_eq] using edist_integral_le_lintegral_edist hfp hfcp
  have hm : edist (∫ e, fc e ∂πm) (∫ e, f e ∂πm) ≤
      ∫⁻ e, ENNReal.ofReal |f e - fc e| ∂πm := by
    rw [edist_comm]
    simpa only [edist_dist, Real.dist_eq] using edist_integral_le_lintegral_edist hfm hfcm
  change ENNReal.ofReal |(∫ e, f e ∂πp) - ∫ e, f e ∂πm| ≤
    ENNReal.ofReal |(∫ e, fc e ∂πp) - ∫ e, fc e ∂πm| +
      (∫⁻ e, ENNReal.ofReal |f e - fc e| ∂πp) +
      (∫⁻ e, ENNReal.ofReal |f e - fc e| ∂πm)
  calc
    _ = edist (∫ e, f e ∂πp) (∫ e, f e ∂πm) := by
      rw [edist_dist, Real.dist_eq]
    _ ≤ edist (∫ e, f e ∂πp) (∫ e, fc e ∂πp) +
        edist (∫ e, fc e ∂πp) (∫ e, fc e ∂πm) +
        edist (∫ e, fc e ∂πm) (∫ e, f e ∂πm) := edist_triangle4 _ _ _ _
    _ ≤ (∫⁻ e, ENNReal.ofReal |f e - fc e| ∂πp) +
        edist (∫ e, fc e ∂πp) (∫ e, fc e ∂πm) +
        (∫⁻ e, ENNReal.ofReal |f e - fc e| ∂πm) :=
      add_le_add (add_le_add hp le_rfl) hm
    _ = _ := by
      rw [edist_dist, Real.dist_eq]
      ac_rfl

end OTSelector.Reconstruction
