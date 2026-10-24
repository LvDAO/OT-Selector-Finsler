import OTSelector.Reconstruction.OriginalLegalScreeningPressureDilationInput

/-! The exact complementary parameters realizing any positive reserve-to-main intensity. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The unit-input reserve fraction corresponding to physical reserve intensity lambda. -/
def originalReserveWorkingFraction (ρ : ℝ) : ℝ := ρ / (1+ρ)

/-- The common physical dilation from the original working cube to the unit-input cube. -/
def originalReserveWorkingScale (q : ℕ) (ρ : ℝ) : ℝ :=
  legalIntensityDilation q (1-originalReserveWorkingFraction ρ)

/-- Every positive physical reserve intensity gives a genuine complementary fraction. -/
theorem originalReserveWorkingFraction_bounds {ρ : ℝ} (hρ : 0 < ρ) :
    0 < originalReserveWorkingFraction ρ ∧ originalReserveWorkingFraction ρ < 1 := by
  have hp : 0 < 1+ρ := by linarith
  exact ⟨div_pos hρ hp, (div_lt_one hp).mpr (by linarith)⟩

/-- The original reserve-to-main intensity is recovered exactly. -/
theorem originalReserveWorkingFraction_ratio {ρ : ℝ} (hρ : 0 < ρ) :
    originalReserveWorkingFraction ρ / (1-originalReserveWorkingFraction ρ) = ρ := by
  have hp : (1+ρ) ≠ 0 := by linarith
  unfold originalReserveWorkingFraction
  field_simp
  ring

/-- Both original Poisson rates are the actual working-volume rates:
lambda V for reserve and (1+lambda)V for the complete original arrays. -/
theorem originalReserveWorking_intensity_count_rates {q : ℕ} (hq : 0 < q)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 ≤ R) :
    let θ := originalReserveWorkingFraction ρ
    let d := originalReserveWorkingScale q ρ
    Real.toNNReal θ *
      (volume (originalCenteredPhysicalCubeRegion b (2*(d*R)))).toNNReal =
      Real.toNNReal ρ * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal ∧
    (volume (originalCenteredPhysicalCubeRegion b (2*(d*R)))).toNNReal =
      Real.toNNReal (1+ρ) * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal := by
  let θ := originalReserveWorkingFraction ρ
  let d := originalReserveWorkingScale q ρ
  have hθ := originalReserveWorkingFraction_bounds hρ
  have hd : 0 < d := legalIntensityDilation_pos q (sub_pos.mpr hθ.2)
  have hdiv : d*R/d = R := mul_div_cancel_left₀ R hd.ne'
  have hv := originalOrientedReserveIntensity_count_rate hq b
    (sub_pos.mpr hθ.2) (mul_nonneg hd.le hR)
  change (volume (originalCenteredPhysicalCubeRegion b (2*(d*R/d)))).toNNReal = _ at hv
  rw [hdiv] at hv
  have hvR := congrArg (fun a : ℝ≥0 ↦ (a : ℝ)) hv
  simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sub_pos.mpr hθ.2).le,
    ENNReal.coe_toNNReal_eq_toReal] at hvR
  have hcomp : 1-θ = (1+ρ)⁻¹ := by
    dsimp only [θ, originalReserveWorkingFraction]
    field_simp
    ring
  have hvfull : (volume (originalCenteredPhysicalCubeRegion b (2*(d*R)))).toNNReal =
      Real.toNNReal (1+ρ) * (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, Real.coe_toNNReal _ (by linarith : 0 ≤ 1+ρ),
      ENNReal.coe_toNNReal_eq_toReal]
    rw [hcomp] at hvR
    have hp : (1+ρ) ≠ 0 := by linarith
    field_simp [hp] at hvR
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hvR.symm
  refine ⟨?_, hvfull⟩
  rw [hvfull, ← mul_assoc, ← Real.toNNReal_mul hθ.1.le]
  have he : θ * (1+ρ) = ρ := by
    dsimp only [θ, originalReserveWorkingFraction]
    exact div_mul_cancel₀ ρ (by linarith)
  rw [he]

end OTSelector.Reconstruction
