import OTSelector.Reconstruction.FinslerRelativeLawUniformVolumeWeight

/-! Replacing actual microscopic filling volume by the original cell volume
retains the missing-volume error for a pressure coefficient of either sign. -/
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction

/-- A true microscopic mean upper bound gives an eventual original-cell
pressure upper bound. The repair is paid after the sample limit, while the
nonvanishing missing mass is paid with the absolute pressure coefficient. -/
theorem eventually_mean_le_original_volume_pressure
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {s : Set X} (hs : MeasurableSet s) (hsfin : μ s ≠ ⊤)
    (U : ℕ → Set X) (hU : ∀ N, MeasurableSet (U N))
    (hUfin : ∀ N, μ (U N) ≠ ⊤)
    {mean micro repair : ℕ → ℝ} {pressure missing repairLimit : ℝ}
    (hmean : ∀ᶠ N in atTop, mean N ≤ micro N + repair N)
    (hmicro : Tendsto (fun N ↦ micro N - μ.real (U N) * pressure) atTop (𝓝 0))
    (hmissing : ∀ N, μ.real (s \ U N) ≤ missing)
    (hadded : Tendsto (fun N ↦ μ (U N \ s)) atTop (𝓝 0))
    (hrepair : Tendsto repair atTop (𝓝 repairLimit)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
      mean N ≤ μ.real s * pressure + missing * |pressure| + repairLimit + ε := by
  intro ε hε
  have haddedReal : Tendsto (fun N ↦ μ.real (U N \ s)) atTop (𝓝 0) := by
    simpa only [measureReal_def, ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hadded
  have herr : Tendsto (fun N ↦ |micro N - μ.real (U N) * pressure| +
      μ.real (U N \ s) * |pressure| + (repair N - repairLimit)) atTop (𝓝 0) := by
    simpa only [abs_zero, zero_mul, zero_add, sub_self, add_zero] using
      ((hmicro.abs.add (haddedReal.mul_const |pressure|)).add
        (hrepair.sub (tendsto_const_nhds (x := repairLimit))))
  filter_upwards [hmean, herr.eventually (Iio_mem_nhds hε)] with N hN herror
  have hgap := measureReal_weighted_error_le_added_missing μ hs (hU N) hsfin (hUfin N)
    (micro N) pressure
  have hmis : (μ.real (U N \ s) + μ.real (s \ U N)) * |pressure| ≤
      μ.real (U N \ s) * |pressure| + missing * |pressure| := by
    rw [add_mul]
    exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (hmissing N) (abs_nonneg _))
  have hmicro := (le_abs_self (micro N - μ.real s * pressure)).trans (hgap.trans
    (add_le_add (le_refl _) hmis))
  linarith

end OTSelector.Reconstruction
