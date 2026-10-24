import OTSelector.MeasureTheory.Integral.BandSquareRootMoment

/-! The actual birth-band mass and physical window length give the sharp
small-phase first-moment coefficients, including the stronger rank-zero term. -/
open Set Function MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction

/-- The square root of the unchanged original rank-density band mass retains
its true elapsed-width and physical focal-time powers. -/
theorem sqrt_birthBandMass {t s K : ℝ} {k : ℕ}
    (ht : 0 < t) (_hs : 0 ≤ s) (hK : 0 ≤ K) :
    Real.sqrt (K * t ^ k * s) = Real.sqrt K * t ^ ((k : ℝ) / 2) * Real.sqrt s := by
  have htk : Real.sqrt (t ^ k) = t ^ ((k : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    ring
  rw [Real.sqrt_mul (mul_nonneg hK (pow_nonneg ht.le _)), Real.sqrt_mul hK, htk]

/-- The original energy coefficient of the small first estimate. -/
theorem smallBirth_firstMoment_energy_scale {t s K : ℝ} {k : ℕ}
    (ht : 0 < t) (hs : 0 < s) (hK : 0 ≤ K) :
    s * t ^ (-3 / 2 : ℝ) * Real.sqrt (K * t ^ k * s) =
      Real.sqrt K * s ^ (3 / 2 : ℝ) * t ^ (((k : ℝ) - 3) / 2) := by
  rw [sqrt_birthBandMass ht hs.le hK]
  have hs' : s * Real.sqrt s = s ^ (3 / 2 : ℝ) := by
    calc
      _ = s ^ (1 : ℝ) * s ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = s ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hs _ _).symm
      _ = _ := by norm_num
  have ht' : t ^ (-3 / 2 : ℝ) * t ^ ((k : ℝ) / 2) = t ^ (((k : ℝ) - 3) / 2) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  calc
    _ = Real.sqrt K * (s * Real.sqrt s) *
        (t ^ (-3 / 2 : ℝ) * t ^ ((k : ℝ) / 2)) := by ring
    _ = _ := by rw [hs', ht']

/-- The full unchanged momentum coefficient retains the additional positive
`3/2` elapsed-time power even when the residue rank is zero. -/
theorem smallBirth_firstMoment_momentum_scale {t s K : ℝ} {k : ℕ}
    (ht : 0 < t) (hs : 0 < s) (hK : 0 ≤ K) :
    s * Real.sqrt (K * t ^ k * s) =
      Real.sqrt K * s ^ (3 / 2 : ℝ) * t ^ ((k : ℝ) / 2) := by
  rw [sqrt_birthBandMass ht hs.le hK]
  have hs' : s * Real.sqrt s = s ^ (3 / 2 : ℝ) := by
    calc
      _ = s ^ (1 : ℝ) * s ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = s ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hs _ _).symm
      _ = _ := by norm_num
  calc
    _ = Real.sqrt K * (s * Real.sqrt s) * t ^ ((k : ℝ) / 2) := by ring
    _ = _ := by rw [hs']

/-- Actual same-band Cauchy-Schwarz plus its original mass and true clock
length gives the sharp small-phase first-moment energy powers. -/
theorem smallBirth_firstMoment_le_of_band_window_bounds
    {t s A C K : ℝ} {k : ℕ} (ht : 0 < t) (hs : 0 < s)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hK : 0 ≤ K) {J m E V H : ℝ≥0∞}
    (hJ : J ≤ ENNReal.ofReal (A * s)) (hm : m ≤ ENNReal.ofReal (K * t ^ k * s))
    (hH : H ≤ J * ENNReal.ofReal C *
      (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * E ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ) +
        V ^ (1 / 2 : ℝ) * m ^ (1 / 2 : ℝ))) :
    H ≤ ENNReal.ofReal (A * C * Real.sqrt K) *
      (ENNReal.ofReal (s ^ (3 / 2 : ℝ) * t ^ (((k : ℝ) - 3) / 2)) * E ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (s ^ (3 / 2 : ℝ) * t ^ ((k : ℝ) / 2)) * V ^ (1 / 2 : ℝ)) := by
  have hmassroot : m ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt (K * t ^ k * s)) := by
    rw [OTSelector.Probability.ofReal_sqrt_eq_rpow]
    exact ENNReal.rpow_le_rpow hm (by norm_num)
  have he := smallBirth_firstMoment_energy_scale (k := k) ht hs hK
  have hv := smallBirth_firstMoment_momentum_scale (k := k) ht hs hK
  have he' : (A * s) * C * t ^ (-3 / 2 : ℝ) * Real.sqrt (K * t ^ k * s) =
      (A * C * Real.sqrt K) * (s ^ (3 / 2 : ℝ) * t ^ (((k : ℝ) - 3) / 2)) := by
    calc
      _ = (A * C) * (s * t ^ (-3 / 2 : ℝ) * Real.sqrt (K * t ^ k * s)) := by ring
      _ = _ := by rw [he]; ring
  have hv' : (A * s) * C * Real.sqrt (K * t ^ k * s) =
      (A * C * Real.sqrt K) * (s ^ (3 / 2 : ℝ) * t ^ ((k : ℝ) / 2)) := by
    calc
      _ = (A * C) * (s * Real.sqrt (K * t ^ k * s)) := by ring
      _ = _ := by rw [hv]; ring
  apply hH.trans
  calc
    _ ≤ ENNReal.ofReal (A * s) * ENNReal.ofReal C *
        (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * E ^ (1 / 2 : ℝ) *
            ENNReal.ofReal (Real.sqrt (K * t ^ k * s)) +
          V ^ (1 / 2 : ℝ) * ENNReal.ofReal (Real.sqrt (K * t ^ k * s))) := by
      gcongr
    _ = _ := by
      simp only [mul_add]
      have h₁ : ENNReal.ofReal (A * s) * ENNReal.ofReal C *
          (ENNReal.ofReal (t ^ (-3 / 2 : ℝ)) * E ^ (1 / 2 : ℝ) *
            ENNReal.ofReal (Real.sqrt (K * t ^ k * s))) =
          ENNReal.ofReal ((A * s) * C * t ^ (-3 / 2 : ℝ) * Real.sqrt (K * t ^ k * s)) *
            E ^ (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_mul (show 0 ≤ (A * s) * C * t ^ (-3 / 2 : ℝ) by positivity),
          ENNReal.ofReal_mul (show 0 ≤ (A * s) * C by positivity),
          ENNReal.ofReal_mul (show 0 ≤ A * s by positivity)]
        ring
      have h₂ : ENNReal.ofReal (A * s) * ENNReal.ofReal C *
          (V ^ (1 / 2 : ℝ) * ENNReal.ofReal (Real.sqrt (K * t ^ k * s))) =
          ENNReal.ofReal ((A * s) * C * Real.sqrt (K * t ^ k * s)) * V ^ (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_mul (show 0 ≤ (A * s) * C by positivity),
          ENNReal.ofReal_mul (show 0 ≤ A * s by positivity)]
        ring
      rw [h₁, h₂, he', hv', ENNReal.ofReal_mul
        (show 0 ≤ A * C * Real.sqrt K by positivity), ENNReal.ofReal_mul
        (show 0 ≤ A * C * Real.sqrt K by positivity)]
      ring

end OTSelector.Reconstruction
