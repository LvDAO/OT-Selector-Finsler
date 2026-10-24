import OTSelector.Reconstruction.VariableHaarCubeCollar

/-! # Normalize the actual collar-plus-tail energy by its own Haar volume -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1800000

/-- An actual finite shell-plus-bulk nonnegative energy bound gives a finite
energy and its normalized real bound, without invoking Fatou in reverse. -/
theorem finite_and_normalized_shell_bulk_energy_le
    (ι : Type*) [Fintype ι] {R delta : ℝ} (hR : 0 < R)
    {energy full tail : ℝ≥0∞} (hfull : full ≠ ∞) (htail : tail ≠ ∞)
    (henergy : energy ≤
      full * volume (haarRootCube ι R \ haarRootCube ι (R - delta)) +
        tail * volume (haarRootCube ι R)) :
    energy ≠ ∞ ∧ energy.toReal / volume.real (haarRootCube ι R) ≤
      full.toReal * (volume.real (haarRootCube ι R \ haarRootCube ι (R - delta)) /
        volume.real (haarRootCube ι R)) + tail.toReal := by
  have hvol : volume (haarRootCube ι R) ≠ ∞ := isCompact_Icc.measure_ne_top
  have hcollar : volume (haarRootCube ι R \ haarRootCube ι (R - delta)) ≠ ∞ :=
    measure_ne_top_of_subset sdiff_subset hvol
  have hprod₀ := ENNReal.mul_ne_top hfull hcollar
  have hprod₁ := ENNReal.mul_ne_top htail hvol
  have hrhs := ENNReal.add_ne_top.mpr ⟨hprod₀, hprod₁⟩
  have hfinite : energy ≠ ∞ := ne_top_of_le_ne_top hrhs henergy
  have hreal := ENNReal.toReal_mono hrhs henergy
  rw [ENNReal.toReal_add hprod₀ hprod₁, ENNReal.toReal_mul, ENNReal.toReal_mul] at hreal
  have hpos : 0 < volume.real (haarRootCube ι R) := by
    rw [volume_real_haarRootCube ι hR.le]
    positivity
  refine ⟨hfinite, ?_⟩
  calc
    _ ≤ (full.toReal * volume.real (haarRootCube ι R \ haarRootCube ι (R - delta)) +
        tail.toReal * volume.real (haarRootCube ι R)) / volume.real (haarRootCube ι R) :=
      div_le_div_of_nonneg_right hreal hpos.le
    _ = _ := by field_simp

end OTSelector.Reconstruction
