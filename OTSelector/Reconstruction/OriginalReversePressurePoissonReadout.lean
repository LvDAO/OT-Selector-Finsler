import OTSelector.Reconstruction.OriginalLegalScreeningPressureDilationFinite
import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineShape

/-! Exact physical cost-scale versus genuine Poisson count-scale pressure. -/
open Set Function MeasureTheory
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Count intensity changes the original pressure normalization and tilt,
while the physical cost scale and every original cloud label remain fixed. -/
theorem originalRawScaleTilted_countIntensity {q : ℕ} (hq : 0 < q)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    {ρ side : ℝ} (hρ : 0 < ρ) (hside : 0 < side) (τ : ℝ)
    (cloud : TwoMarkedCloudSpace q ℝ ℝ) :
    legalMarkedTilted q id id (side^q) kin g τ cloud =
      ρ^(-(2/(q : ℝ))) * legalMarkedTilted q id id (ρ*side^q) kin g
        (τ*ρ^(2/(q : ℝ))) cloud := by
  have hpow := rpow_affine_intensity q hq hρ.le hside.le
  have hsidepow : (side^q)^(2/(q : ℝ)) = side^2 := by
    simpa only [one_mul,Real.one_rpow] using
      rpow_affine_intensity q hq (r := (1 : ℝ)) zero_le_one hside.le
  have hcancel : ρ^(-(2/(q : ℝ)))*ρ^(2/(q : ℝ)) = 1 := by
    rw [← Real.rpow_add hρ]
    simp
  unfold legalMarkedTilted legalMarkedFixedValue
  rw [← PartialMatching.legalMaximumValue_const_mul _ _ (Real.rpow_nonneg hρ.le _)]
  congr 1
  funext i j
  simp only [mKineticCost,mProbe,hpow,hsidepow]
  linear_combination -(side^2 * kin (mSourceMark cloud i) (mTargetMark cloud j)
    (mDisplacement (mSourcePoint cloud i) (mTargetPoint cloud j)) +
    τ*g (mSourceMark cloud i) (mTargetMark cloud j))*hcancel

/-- The genuine full Poisson expectation reads the original scale pressure
at its actual side and exact dilated tilt. No finite-value comparison or
candidate pressure bound is assumed. -/
theorem originalRawScaleTilted_normalized_mean_eq_pressure {q : ℕ} (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    {ρ side : ℝ} (hρ : 0 < ρ) (hside : 0 < side) (τ : ℝ) :
    (∫ cloud, legalMarkedTilted q id id (side^q) kin g τ cloud
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (ρ*side^q)))/(side^q) =
      ρ^(1-2/(q : ℝ)) * legalMarkedScalePressure q id id α β kin g
        (side*ρ^(1/(q : ℝ))) (τ*ρ^(2/(q : ℝ))) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsidepow : 0 < side^q := pow_pos hside q
  have hscale : (side*ρ^(1/(q : ℝ)))^q = ρ*side^q := by
    have hh : (ρ^(1/(q : ℝ)))^q = ρ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hρ.le]
      rw [show (1/(q : ℝ))*(q : ℝ) = 1 by field_simp,Real.rpow_one]
    rw [mul_pow,hh,mul_comm]
  have hspos : 0 < side*ρ^(1/(q : ℝ)) := mul_pos hside (Real.rpow_pos_of_pos hρ _)
  have hmean : (∫ cloud, legalMarkedTilted q id id (side^q) kin g τ cloud
      ∂twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (ρ*side^q))) =
      ρ^(-(2/(q : ℝ))) * legalMarkedPressure q id id α β
        (Real.toNNReal (ρ*side^q)) kin g (τ*ρ^(2/(q : ℝ))) := by
    simp_rw [originalRawScaleTilted_countIntensity hq kin g hρ hside τ]
    rw [integral_const_mul]
    simp only [legalMarkedPressure,Real.coe_toNNReal _ (mul_pos hρ hsidepow).le]
  rw [hmean,legalMarkedScalePressure,ite_eq_left hspos,hscale]
  have hfactor : ρ^(1-2/(q : ℝ)) = ρ*ρ^(-(2/(q : ℝ))) := by
    calc
      _ = ρ^((1 : ℝ)+(-(2/(q : ℝ)))) := by rfl
      _ = ρ^(1 : ℝ)*ρ^(-(2/(q : ℝ))) := Real.rpow_add hρ _ _
      _ = _ := by rw [Real.rpow_one]
  rw [hfactor]
  field_simp [hρ.ne',hsidepow.ne']

end OTSelector.Reconstruction
