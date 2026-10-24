import OTSelector.Reconstruction.OriginalBirthPhysicalVelocity
import OTSelector.Reconstruction.OriginalMaskedOneEdgeTraffic
import OTSelector.Reconstruction.FinslerOriginalPathMeasurability

/-!
# Literal masked one-edge birth traffic in canonical momentum

This is the actual full-clock readout used in the source-confined L2 theorem.
The clock mask may depend on the original edge and on its clock. Only its fixed
short-window support and bound by one enter the pointwise estimate.
-/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The full literal physical one-edge readout has coefficient C√s/t in its
same canonical birth momentum. No mark ordering, cone, or independence is needed
for this short-window bound. -/
theorem original_maskedBirthTraffic_le_canonicalMomentum
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {t s A C M₀ : ℝ} (ht : 0 < t) (hs : 0 < s)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hM : 0 ≤ M₀)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    {J : Set ℝ} (hJ : MeasurableSet J) (hvolume : volume J ≤ ENNReal.ofReal (A * s))
    {h : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞}
    (hh : ∀ z, h z ≤ ENNReal.ofReal M₀)
    {mask : ℝ → ℝ≥0∞} (hmask : ∀ c ∈ J, mask c ≤ 1) (hsupport : mask.support ⊆ J)
    (hvelocity : ∀ c ∈ J,
      ‖originalSeedKernel S w (c - S.level) *ᵥ originalSeedPairMomentum S w m‖ ≤
        (C / (t * Real.sqrt s)) *
          ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
            originalSeedPairMomentum S w m‖) :
    (∫⁻ c : ℝ, h (x + originalSeedPathOffset S w c m) *
      (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask c)) ≤
      ENNReal.ofReal (M₀ * A * C * Real.sqrt s / t) *
        ENNReal.ofReal ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
          originalSeedPairMomentum S w m‖ := by
  let y := ‖((positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)⁻¹ *ᵥ
    originalSeedPairMomentum S w m‖
  let f := fun c : ℝ ↦ h (x + originalSeedPathOffset S w c m) *
    (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖ * mask c)
  have hy : 0 ≤ y := norm_nonneg _
  have hfsupport : f.support ⊆ J :=
    (Function.support_mul_subset_right _ _).trans
      ((Function.support_mul_subset_right _ _).trans hsupport)
  have hpoint : ∀ c ∈ J, f c ≤ ENNReal.ofReal (M₀ * ((C / (t * Real.sqrt s)) * y)) := by
    intro c hc
    have hocc := ENNReal.ofReal_le_ofReal
      ((norm_originalSeedClockOccupation_le_velocity S w m c).trans (hvelocity c hc))
    calc
      _ ≤ ENNReal.ofReal M₀ * (ENNReal.ofReal ((C / (t * Real.sqrt s)) * y) * 1) := by
        exact mul_le_mul (hh _) (mul_le_mul hocc (hmask c hc) zero_le zero_le)
          zero_le zero_le
      _ = _ := by rw [mul_one, ENNReal.ofReal_mul hM]
  have hcancel : s / Real.sqrt s = Real.sqrt s :=
    (div_eq_iff (Real.sqrt_pos.mpr hs).ne').mpr (Real.mul_self_sqrt hs.le).symm
  have hid : (M₀ * ((C / (t * Real.sqrt s)) * y)) * (A * s) =
      (M₀ * A * C * Real.sqrt s / t) * y := by
    calc
      _ = (M₀ * A * C / t) * y * (s / Real.sqrt s) := by ring
      _ = _ := by rw [hcancel]; ring
  change (∫⁻ c, f c) ≤ ENNReal.ofReal (M₀ * A * C * Real.sqrt s / t) * ENNReal.ofReal y
  calc
    _ = ∫⁻ c in J, f c := (setLIntegral_eq_of_support_subset hfsupport).symm
    _ ≤ ∫⁻ _c in J, ENNReal.ofReal (M₀ * ((C / (t * Real.sqrt s)) * y)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hJ] with c hc
      exact hpoint c hc
    _ = ENNReal.ofReal (M₀ * ((C / (t * Real.sqrt s)) * y)) * volume J := by simp
    _ ≤ ENNReal.ofReal (M₀ * ((C / (t * Real.sqrt s)) * y)) * ENNReal.ofReal (A * s) :=
      mul_le_mul_of_nonneg_left hvolume zero_le
    _ = ENNReal.ofReal ((M₀ * ((C / (t * Real.sqrt s)) * y)) * (A * s)) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal ((M₀ * A * C * Real.sqrt s / t) * y) := congrArg ENNReal.ofReal hid
    _ = _ := ENNReal.ofReal_mul (by positivity)

end OTSelector.Reconstruction
