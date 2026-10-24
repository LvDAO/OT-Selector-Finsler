import OTSelector.Reconstruction.FinslerPhysicalSceneMacroProbeConvolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# Exact signed convolution on the same original Haar experiment

A compact source cutoff and a bounded signed probe give genuine absolute
integrability. Fubini and the actual Haar involution retain the original plan.
-/
open Set Function MeasureTheory OTSelector.Probability
open scoped ENNReal Topology CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
variable {ι Z : Type*} [Fintype ι] [MeasurableSpace Z]
local notation "V" => (ι → ℝ)

/-- Absolute integrability of the genuine bounded signed Haar probe follows
from the original finite plan and compact spatial cutoff alone. -/
theorem integrable_haar_root_weighted_probe
    (Γ : Measure Z) [IsFiniteMeasure Γ] (loc : Z → V) (hloc : Measurable loc)
    (η : C_c(V, ℝ)) (hη : ∀ v, 0 ≤ η v)
    (G : V × Z → ℝ) (hG : Measurable G)
    (C : ℝ) (hC : ∀ z p, |G (z, p)| ≤ C) :
    Integrable (fun w : V × Z ↦ η (loc w.2 - w.1) * G w) (volume.prod Γ) := by
  let f : V × Z → ℝ := fun w ↦ η (loc w.2 - w.1) * G w
  have hm : Measurable f :=
    (η.continuous.measurable.comp ((hloc.comp measurable_snd).sub measurable_fst)).mul hG
  have hηfinite : (∫⁻ v, ENNReal.ofReal (η v) ∂volume) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable η.continuous.aestronglyMeasurable
      (ae_of_all _ hη)).mpr (η.continuous.integrable_of_hasCompactSupport η.hasCompactSupport)
  have hf : Integrable f (volume.prod Γ) := by
    refine ⟨hm.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    rw [lintegral_prod _ hm.enorm.aemeasurable]
    calc
      _ ≤ ∫⁻ z, ∫⁻ p, ENNReal.ofReal (η (loc p - z)) * ENNReal.ofReal C ∂Γ ∂volume := by
        apply lintegral_mono
        intro z
        apply lintegral_mono
        intro p
        have hb : |η (loc p - z) * G (z, p)| ≤ η (loc p - z) * C := by
          rw [abs_mul, abs_of_nonneg (hη _)]
          exact mul_le_mul_of_nonneg_left (hC z p) (hη _)
        simpa only [f, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul (hη _)] using
          ENNReal.ofReal_le_ofReal hb
      _ = (∫⁻ v, ENNReal.ofReal (η v) ∂volume) * (ENNReal.ofReal C * Γ univ) := by
        simpa only [lintegral_const] using lintegral_haar_root_weighted_probe volume Γ loc hloc
          (fun v ↦ ENNReal.ofReal (η v)) η.continuous.measurable.ennreal_ofReal
          (fun _ ↦ ENNReal.ofReal C) measurable_const
      _ < ∞ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hηfinite)
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top Γ univ))
  exact hf

/-- Signed real Haar rooting is the exact convolution of the unchanged plan.
Its Fubini integrability follows from compact source mass and bounded probe. -/
theorem integral_haar_root_weighted_probe_convolution
    (Γ : Measure Z) [IsFiniteMeasure Γ] (loc : Z → V) (hloc : Measurable loc)
    (η : C_c(V, ℝ)) (hη : ∀ v, 0 ≤ η v)
    (G : V × Z → ℝ) (hG : Measurable G)
    (C : ℝ) (hC : ∀ z p, |G (z, p)| ≤ C) :
    (∫ z, ∫ p, η (loc p - z) * G (z, p) ∂Γ ∂volume) =
      ∫ p, ∫ v, η v * G (loc p - v, p) ∂volume ∂Γ := by
  let f : V × Z → ℝ := fun w ↦ η (loc w.2 - w.1) * G w
  have hf : Integrable f (volume.prod Γ) :=
    integrable_haar_root_weighted_probe Γ loc hloc η hη G hG C hC
  change (∫ z, ∫ p, f (z, p) ∂Γ ∂volume) = _
  rw [integral_integral_swap hf]
  apply integral_congr_ae
  filter_upwards [] with p
  have he : MeasurableEmbedding (fun z : V ↦ loc p - z) :=
    (Homeomorph.subLeft (loc p)).toMeasurableEquiv.measurableEmbedding
  simpa only [f, sub_sub_cancel] using (volume.measurePreserving_sub_left (loc p)).integral_comp he
    (fun v ↦ η v * G (loc p - v, p))

end OTSelector.Reconstruction
