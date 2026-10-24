import OTSelector.Probability.BirthDyadicTrafficLevelNorm
import OTSelector.Probability.RankZeroBirthBandNorm

/-! The same literal rank-zero original birth contribution retains its stronger
momentum-only first estimate and obtains positive decay in both physical scales. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- Actual momentum-only first and second estimates for the same rank-zero
birth traffic yield a summable positive double-dyadic norm bound. -/
theorem birthBand_rankZero_traffic_interpolated_level_norm
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ bands, MemLp (T i) 2 P)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i)
    {E t s C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s) (hC : 0 ≤ C)
    (hE1 : 1 ≤ E) (hNs : (bands.card : ℝ) * s = 8 * t)
    (hV : (∑ i ∈ bands, v i) ≤ E)
    (hfirst : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      (C * s ^ (3 / 2 : ℝ)) * Real.sqrt (v i))
    (hsecond : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      C * s ^ 2 * (t ^ (-3 : ℝ) * v i)) :
    MemLp (fun x ↦ ∑ i ∈ bands, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤
        ENNReal.ofReal ((((8 : ℝ) ^ (3 / 4 : ℝ) + 2 * Real.sqrt 8) *
          Real.sqrt C * Real.sqrt E) *
          (t ^ (3 / 8 : ℝ) * (s / t) ^ (3 / 28 : ℝ))) := by
  have h₁ := rankZero_birthBand_traffic_memLp_two_of_first_moment P bands T hT v hv
    ht hs hC hNs hV hfirst
  have h₂ := birthBand_small_second_traffic_level_norm P bands T hT (fun _ ↦ 0) v
    (fun _ ↦ le_rfl) hv (k := 0) ht ht1 hs hC hNs (by simpa using (show 0 ≤ E by linarith)) hV
    (by simpa only [zero_add, mul_zero] using hsecond)
  norm_num only [zero_add, neg_div, Nat.cast_ofNat] at h₂
  let A₁ : ℝ := (8 : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt C * Real.sqrt E
  let A₂ : ℝ := 2 * Real.sqrt 8 * Real.sqrt C * Real.sqrt E
  let A : ℝ := A₁ + A₂
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
  have hA : 0 ≤ A := add_nonneg hA₁ hA₂
  have hroot : E ^ (1 / 4 : ℝ) ≤ Real.sqrt E := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)
  have hfirst' : eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤
      ENNReal.ofReal (A₁ * t ^ (3 / 4 : ℝ)) := by
    apply h₁.2.trans
    apply ENNReal.ofReal_le_ofReal
    dsimp [A₁]
    gcongr
  have hfin := h₁.1.eLpNorm_ne_top
  have hx₁ : (eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P).toReal ≤ A₁ * t ^ (3 / 4 : ℝ) :=
    (ENNReal.le_ofReal_iff_toReal_le hfin (mul_nonneg hA₁ (Real.rpow_nonneg ht.le _))).mp hfirst'
  have hx₂ : (eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P).toReal ≤
      A₂ * (t ^ (-1 : ℝ) * (s / t) ^ (1 / 2 : ℝ)) := by
    have hr := (ENNReal.le_ofReal_iff_toReal_le hfin
      (show 0 ≤ 2 * Real.sqrt 8 * Real.sqrt C * Real.sqrt E * t ^ (-1 : ℝ) *
        Real.sqrt (s / t) by positivity)).mp h₂.2
    simpa only [A₂, Real.sqrt_eq_rpow, mul_assoc] using hr
  have hx₁' : (eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P).toReal ≤ A * t ^ (3 / 4 : ℝ) :=
    hx₁.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hA₂) (Real.rpow_nonneg ht.le _))
  have hx₂' : (eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P).toReal ≤
      A * (t ^ (-1 : ℝ) * (s / t) ^ (1 / 2 : ℝ)) :=
    hx₂.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA₁) (by positivity))
  have hinterp := rankZero_smallTraffic_interpolation hA ht (div_pos hs ht) hx₁' hx₂'
  have htarget : 0 ≤ A * (t ^ (3 / 8 : ℝ) * (s / t) ^ (3 / 28 : ℝ)) := by positivity
  refine ⟨h₁.1, ?_⟩
  have hresult := (ENNReal.le_ofReal_iff_toReal_le hfin htarget).mpr hinterp
  have hcoeff : A = ((8 : ℝ) ^ (3 / 4 : ℝ) + 2 * Real.sqrt 8) * Real.sqrt C * Real.sqrt E := by
    dsimp [A, A₁, A₂]
    ring
  simpa only [hcoeff] using hresult

end OTSelector.Probability
