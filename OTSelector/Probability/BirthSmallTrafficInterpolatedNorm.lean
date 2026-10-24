import OTSelector.Probability.BirthDyadicTrafficLevelNorm
import OTSelector.Analysis.RealPowerInterpolation

/-! Both actual small-phase estimates concern the same literal random birth
contribution. Their norm interpolation gives positive decay in both dyadic scales. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- The actual two same-traffic per-band energy estimates produce the precise
interpolated birth-level norm. No independent copy or separate mask is introduced. -/
theorem birthBand_small_traffic_interpolated_level_norm
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ bands, MemLp (T i) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {E t s C k : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s) (hC : 0 ≤ C)
    (hE1 : 1 ≤ E) (hk : 0 < k)
    (hNs : (bands.card : ℝ) * s = 8 * t)
    (hE : (∑ i ∈ bands, e i) ≤ E) (hV : (∑ i ∈ bands, v i) ≤ E)
    (hfirst : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      C * s ^ (3 / 2 : ℝ) *
        (t ^ ((k - 3) / 2) * Real.sqrt (e i) + t ^ (k / 2) * Real.sqrt (v i)))
    (hsecond : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      C * s ^ 2 * (t ^ (-(k + 4)) * e i + t ^ (-(k + 3)) * v i)) :
    MemLp (fun x ↦ ∑ i ∈ bands, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤
        ENNReal.ofReal (((2 * (8 : ℝ) ^ (3 / 4 : ℝ) + 2 * Real.sqrt 8) *
          Real.sqrt C * Real.sqrt E) *
          (t ^ (k / 8) * (s / t) ^ (k / (4 * (3 * k + 4))))) := by
  have h₁ := birthBand_small_first_traffic_level_norm P bands T hT e v he hv
    ht ht1 hs hC hE1 hNs hE hV hfirst
  have h₂ := birthBand_small_second_traffic_level_norm P bands T hT e v he hv
    ht ht1 hs hC hNs hE hV hsecond
  let A₁ : ℝ := 2 * (8 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt C * Real.sqrt E
  let A₂ : ℝ := 2 * Real.sqrt 8 * Real.sqrt C * Real.sqrt E
  let A : ℝ := A₁ + A₂
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
  have hA : 0 ≤ A := add_nonneg hA₁ hA₂
  have hfin := h₁.1.eLpNorm_ne_top
  have hx₁ : (eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P).toReal ≤ A₁ * t ^ (k / 4) :=
    (ENNReal.le_ofReal_iff_toReal_le hfin (mul_nonneg hA₁ (Real.rpow_nonneg ht.le _))).mp h₁.2
  have hx₂ : (eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P).toReal ≤
      A₂ * (t ^ (-(k + 2) / 2) * (s / t) ^ (1 / 2 : ℝ)) := by
    have hr := (ENNReal.le_ofReal_iff_toReal_le hfin
      (show 0 ≤ 2 * Real.sqrt 8 * Real.sqrt C * Real.sqrt E * t ^ (-(k + 2) / 2) *
        Real.sqrt (s / t) by positivity)).mp h₂.2
    simpa only [A₂, Real.sqrt_eq_rpow, mul_assoc] using hr
  have hx₁' : (eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P).toReal ≤ A * t ^ (k / 4) :=
    hx₁.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA₂) (Real.rpow_nonneg ht.le _))
  have hx₂' : (eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P).toReal ≤
      A * (t ^ (-(k + 2) / 2) * (s / t) ^ (1 / 2 : ℝ)) :=
    hx₂.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA₁) (by positivity))
  have hinterp := interleaved_smallTraffic_interpolation hA ht (div_pos hs ht) hk hx₁' hx₂'
  have htarget : 0 ≤ A * (t ^ (k / 8) * (s / t) ^ (k / (4 * (3 * k + 4)))) := by positivity
  refine ⟨h₁.1, ?_⟩
  have hresult := (ENNReal.le_ofReal_iff_toReal_le hfin htarget).mpr hinterp
  have hcoeff : A = (2 * (8 : ℝ) ^ (3 / 4 : ℝ) + 2 * Real.sqrt 8) * Real.sqrt C * Real.sqrt E := by
    dsimp [A, A₁, A₂]
    ring
  simpa only [hcoeff] using hresult

end OTSelector.Probability
