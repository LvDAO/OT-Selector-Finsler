import OTSelector.Reconstruction.MarkedStationaryValueLegalPressureLimit
import Mathlib.Tactic

/-! Scalar limits for a genuine two-piece pressure comparison. -/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

noncomputable section
namespace OTSelector.Reconstruction

/-- A single tilt's actual scale-pressure limit has the same intensity-normalized limit. -/
theorem tendsto_originalOrientedShape_pressure_div_nnreal
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t p : ℝ)
    (hp : Tendsto (fun R ↦ legalMarkedScalePressure q id id α β kin g R t)
      atTop (𝓝 p)) :
    Tendsto (fun r : ℝ≥0 ↦ legalMarkedPressure q id id α β r kin g t / (r : ℝ))
      atTop (𝓝 p) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hcoe : Tendsto (fun r : ℝ≥0 ↦ (r : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hroot : Tendsto (fun r : ℝ≥0 ↦ (r : ℝ) ^ (1 / (q : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / (q : ℝ))).comp hcoe
  refine (hp.comp hroot).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with r hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  change legalMarkedScalePressure q id id α β kin g ((r : ℝ) ^ (1 / (q : ℝ))) t =
    legalMarkedPressure q id id α β r kin g t / (r : ℝ)
  simp only [legalMarkedScalePressure, Real.rpow_pos_of_pos hrR _, ↓reduceIte]
  have hpow : ((r : ℝ) ^ (1 / (q : ℝ))) ^ q = (r : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hrR.le]
    have hexp : (1 / (q : ℝ)) * (q : ℝ) = 1 := by field_simp
    rw [hexp, Real.rpow_one]
  rw [hpow, Real.toNNReal_coe]

/-- Pass a finite comparison with a shrinking shape and a separate hole budget to limits. -/
theorem originalOrientedShape_scaled_normalized_limit_le
    (f g hole error : ℝ≥0 → ℝ) {a b H : ℝ} {θ : ℝ≥0} (hθ : 0 < θ)
    (hf : Tendsto (fun r : ℝ≥0 ↦ f r / (r : ℝ)) atTop (𝓝 a))
    (hg : Tendsto (fun r : ℝ≥0 ↦ g r / (r : ℝ)) atTop (𝓝 b))
    (hhole : Tendsto (fun r : ℝ≥0 ↦ hole r / (r : ℝ)) atTop (𝓝 H))
    (herr : Tendsto (fun r : ℝ≥0 ↦ error r / (r : ℝ)) atTop (𝓝 0))
    (hbound : ∀ᶠ r : ℝ≥0 in atTop, f r ≤ g (r * θ) + hole r + error r) :
    a ≤ (θ : ℝ) * b + H := by
  have hθR : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
  have hshift : Tendsto (fun r : ℝ≥0 ↦ r * θ) atTop atTop :=
    tendsto_id.atTop_mul_const hθ
  have hgshift := hg.comp hshift
  have hscaled : Tendsto (fun r : ℝ≥0 ↦ g (r * θ) / (r : ℝ))
      atTop (𝓝 ((θ : ℝ) * b)) := by
    refine (hgshift.const_mul (θ : ℝ)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with r hr
    have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    change (θ : ℝ) * (g (r * θ) / ((r * θ : ℝ≥0) : ℝ)) = g (r * θ) / (r : ℝ)
    rw [NNReal.coe_mul]
    field_simp [hrR, hθR]
  have hineq : ∀ᶠ r : ℝ≥0 in atTop,
      f r / (r : ℝ) ≤ g (r * θ) / (r : ℝ) + hole r / (r : ℝ) + error r / (r : ℝ) := by
    filter_upwards [hbound, eventually_gt_atTop (0 : ℝ≥0)] with r hb hr
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    simpa only [add_div] using div_le_div_of_nonneg_right hb hrR.le
  have hle := le_of_tendsto_of_tendsto hf ((hscaled.add hhole).add herr) hineq
  simpa only [add_zero] using hle

end OTSelector.Reconstruction
