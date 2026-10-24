import Mathlib.MeasureTheory.Order.Group.Lattice
import OTSelector.Reconstruction.FinslerPhysicalSceneMacroClockProbeCutoffGap
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedLaw

/-!
# Expected cutoff comparison in one actual experiment

Measurable fields of finite physical plans integrate the literal joint probe
measurably.  One common experiment then pays its two actual cutoff errors.
-/

open Set MeasureTheory
open scoped Topology ENNReal CompactlySupported

namespace OTSelector.Reconstruction

private theorem measurable_lintegral_finite_field
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (π : Ω → Measure S) [∀ ω, IsFiniteMeasure (π ω)] (hπ : Measurable π)
    (f : Ω × S → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun ω ↦ ∫⁻ e, f (ω, e) ∂π ω) := by
  have hm := measurable_parameterized_finite_measure_map π hπ
    (fun p : Ω × S ↦ p) measurable_id
  convert (Measure.measurable_lintegral hf).comp hm using 1
  funext ω
  exact (lintegral_map hf measurable_prodMk_left).symm

private theorem measurable_integral_finite_field
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (π : Ω → Measure S) [∀ ω, IsFiniteMeasure (π ω)] (hπ : Measurable π)
    (f : Ω × S → ℝ) (hf : Measurable f)
    (hfi : ∀ ω, Integrable (fun e ↦ f (ω, e)) (π ω)) :
    Measurable (fun ω ↦ ∫ e, f (ω, e) ∂π ω) := by
  have hp := measurable_lintegral_finite_field π hπ
    (fun p ↦ ENNReal.ofReal (f p)) hf.ennreal_ofReal
  have hn := measurable_lintegral_finite_field π hπ
    (fun p ↦ ENNReal.ofReal (-f p)) hf.neg.ennreal_ofReal
  have heq (ω : Ω) : (∫ e, f (ω, e) ∂π ω) =
      (∫⁻ e, ENNReal.ofReal (f (ω, e)) ∂π ω).toReal -
        (∫⁻ e, ENNReal.ofReal (-f (ω, e)) ∂π ω).toReal :=
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hfi ω)
  simp_rw [heq]
  exact hp.ennreal_toReal.sub hn.ennreal_toReal

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
local notation "V" => (ι → ℝ)
local notation "Point" => (V × ℝ)
local notation "Edge" => (Point × Point)

private theorem measurable_joint_macro_clock_probe
    (tag : Ω → V) (htag : Measurable tag)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ)) :
    Measurable (fun p : Ω × Edge ↦
      η p.2.1.1 * g (tag p.1, (p.2.1.2, p.2.2.2))) :=
  (η.continuous.measurable.comp measurable_snd.fst.fst).mul
    (g.continuous.measurable.comp ((htag.comp measurable_fst).prodMk
      (measurable_snd.fst.snd.prodMk measurable_snd.snd.snd)))

/-- Literal full probe integrals are measurable in the actual finite-plan field
and macro parameter, with no topology on the experiment. -/
theorem measurable_macro_clock_probe_integral
    (π : Ω → Measure Edge) [∀ ω, IsFiniteMeasure (π ω)] (hπ : Measurable π)
    (tag : Ω → V) (htag : Measurable tag)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ)) :
    Measurable (fun ω ↦ ∫ e, η e.1.1 * g (tag ω, (e.1.2, e.2.2)) ∂π ω) := by
  exact measurable_integral_finite_field π hπ _
    (measurable_joint_macro_clock_probe tag htag η g)
    (fun ω ↦ integrable_macro_clock_probe (π ω) (tag ω) η g)

/-- Literal cutoff probe integrals are measurable in the same actual finite-plan
field and macro parameter. -/
theorem measurable_macro_clock_probe_cutoff_integral
    (π : Ω → Measure Edge) [∀ ω, IsFiniteMeasure (π ω)] (hπ : Measurable π)
    (tag : Ω → V) (htag : Measurable tag)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ))
    (χ : C_c(Point, ℝ)) (hχ : ∀ y, χ y ∈ Icc 0 1) :
    Measurable (fun ω ↦
      ∫ e, (η e.1.1 * g (tag ω, (e.1.2, e.2.2))) * χ e.2 ∂π ω) := by
  exact measurable_integral_finite_field π hπ _
    ((measurable_joint_macro_clock_probe tag htag η g).mul
      (χ.continuous.measurable.comp measurable_snd.snd))
    (fun ω ↦ integrable_macro_clock_probe_cutoff (π ω) (tag ω) η g χ hχ)

/-- The full signed-plan gap is a measurable nonnegative readout of the same
actual experiment. -/
theorem measurable_ofReal_abs_macro_clock_probe_gap
    (πp πm : Ω → Measure Edge)
    [∀ ω, IsFiniteMeasure (πp ω)] [∀ ω, IsFiniteMeasure (πm ω)]
    (hπp : Measurable πp) (hπm : Measurable πm)
    (tag : Ω → V) (htag : Measurable tag)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ)) :
    Measurable (fun ω ↦ ENNReal.ofReal
      |(∫ e, η e.1.1 * g (tag ω, (e.1.2, e.2.2)) ∂πp ω) -
        ∫ e, η e.1.1 * g (tag ω, (e.1.2, e.2.2)) ∂πm ω|) :=
  ((measurable_macro_clock_probe_integral πp hπp tag htag η g).sub
    (measurable_macro_clock_probe_integral πm hπm tag htag η g)).abs.ennreal_ofReal

/-- The target-cutoff signed-plan gap is measurable in the original experiment. -/
theorem measurable_ofReal_abs_macro_clock_probe_cutoff_gap
    (πp πm : Ω → Measure Edge)
    [∀ ω, IsFiniteMeasure (πp ω)] [∀ ω, IsFiniteMeasure (πm ω)]
    (hπp : Measurable πp) (hπm : Measurable πm)
    (tag : Ω → V) (htag : Measurable tag)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ))
    (χ : C_c(Point, ℝ)) (hχ : ∀ y, χ y ∈ Icc 0 1) :
    Measurable (fun ω ↦ ENNReal.ofReal
      |(∫ e, (η e.1.1 * g (tag ω, (e.1.2, e.2.2))) * χ e.2 ∂πp ω) -
        ∫ e, (η e.1.1 * g (tag ω, (e.1.2, e.2.2))) * χ e.2 ∂πm ω|) :=
  ((measurable_macro_clock_probe_cutoff_integral πp hπp tag htag η g χ hχ).sub
    (measurable_macro_clock_probe_cutoff_integral πm hπm tag htag η g χ hχ)).abs.ennreal_ofReal

/-- The actual planwise cutoff loss is measurable from the original finite-plan
field and literal joint nonnegative error kernel. -/
theorem measurable_lintegral_macro_clock_probe_cutoff_error
    (π : Ω → Measure Edge) [∀ ω, IsFiniteMeasure (π ω)] (hπ : Measurable π)
    (tag : Ω → V) (htag : Measurable tag)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ)) (χ : C_c(Point, ℝ)) :
    Measurable (fun ω ↦ ∫⁻ e, ENNReal.ofReal
      |η e.1.1 * g (tag ω, (e.1.2, e.2.2)) -
        (η e.1.1 * g (tag ω, (e.1.2, e.2.2))) * χ e.2| ∂π ω) := by
  have hf := measurable_joint_macro_clock_probe tag htag η g
  exact measurable_lintegral_finite_field π hπ _
    (hf.sub (hf.mul (χ.continuous.measurable.comp measurable_snd.snd))).abs.ennreal_ofReal

/-- One common actual experiment compares the full macro-clock gap to its
target-cutoff gap and the two actual planwise cutoff losses. -/
theorem lintegral_ofReal_abs_macro_clock_probe_gap_le_cutoff_gap_add_errors
    (m : Measure Ω) (πp πm : Ω → Measure Edge)
    [∀ ω, IsFiniteMeasure (πp ω)] [∀ ω, IsFiniteMeasure (πm ω)]
    (hπp : Measurable πp) (hπm : Measurable πm)
    (tag : Ω → V) (htag : Measurable tag)
    (η : C_c(V, ℝ)) (g : C_c(V × (ℝ × ℝ), ℝ))
    (χ : C_c(Point, ℝ)) (hχ : ∀ y, χ y ∈ Icc 0 1) :
    (∫⁻ ω, ENNReal.ofReal
      |(∫ e, η e.1.1 * g (tag ω, (e.1.2, e.2.2)) ∂πp ω) -
        ∫ e, η e.1.1 * g (tag ω, (e.1.2, e.2.2)) ∂πm ω| ∂m) ≤
      (∫⁻ ω, ENNReal.ofReal
        |(∫ e, (η e.1.1 * g (tag ω, (e.1.2, e.2.2))) * χ e.2 ∂πp ω) -
          ∫ e, (η e.1.1 * g (tag ω, (e.1.2, e.2.2))) * χ e.2 ∂πm ω| ∂m) +
        (∫⁻ ω, ∫⁻ e, ENNReal.ofReal
          |η e.1.1 * g (tag ω, (e.1.2, e.2.2)) -
            (η e.1.1 * g (tag ω, (e.1.2, e.2.2))) * χ e.2| ∂πp ω ∂m) +
        (∫⁻ ω, ∫⁻ e, ENNReal.ofReal
          |η e.1.1 * g (tag ω, (e.1.2, e.2.2)) -
            (η e.1.1 * g (tag ω, (e.1.2, e.2.2))) * χ e.2| ∂πm ω ∂m) := by
  have hp := measurable_lintegral_macro_clock_probe_cutoff_error πp hπp tag htag η g χ
  have hm := measurable_lintegral_macro_clock_probe_cutoff_error πm hπm tag htag η g χ
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal
        |(∫ e, (η e.1.1 * g (tag ω, (e.1.2, e.2.2))) * χ e.2 ∂πp ω) -
          ∫ e, (η e.1.1 * g (tag ω, (e.1.2, e.2.2))) * χ e.2 ∂πm ω| +
        (∫⁻ e, ENNReal.ofReal
          |η e.1.1 * g (tag ω, (e.1.2, e.2.2)) -
            (η e.1.1 * g (tag ω, (e.1.2, e.2.2))) * χ e.2| ∂πp ω) +
        (∫⁻ e, ENNReal.ofReal
          |η e.1.1 * g (tag ω, (e.1.2, e.2.2)) -
            (η e.1.1 * g (tag ω, (e.1.2, e.2.2))) * χ e.2| ∂πm ω) ∂m :=
      lintegral_mono fun ω ↦
        ofReal_abs_macro_clock_probe_gap_le_cutoff_gap_add_errors
          (πp ω) (πm ω) (tag ω) η g χ hχ
    _ = _ := by
      rw [lintegral_add_right _ hm, lintegral_add_right _ hp]

end OTSelector.Reconstruction
