import OTSelector.MeasureTheory.DensityPowerChangeOfMeasure

/-!
# Integrable original density-scaled pressures without a lower density bound

The Haar representation has nonnegative exponent 1-2/q.  Its linear pressure
growth controls the original population integral even where density approaches
zero; no uniform bound on the singular population integrand is asserted.
-/
open MeasureTheory Filter
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- The original tilt contribution pays exactly one density power, also at zero. -/
theorem density_rpow_probe_weight {theta a t : ℝ} (htheta : 0 ≤ theta) :
    theta ^ (1 - a) * |t * theta ^ a| = |t| * theta := by
  have hexp : (1 - a) + a = 1 := by ring
  have hne : (1 - a) + a ≠ 0 := by rw [hexp]; norm_num
  have hp := Real.rpow_add' htheta hne
  calc
    _ = |t| * (theta ^ (1 - a) * theta ^ a) := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg htheta _)]
      ring
    _ = _ := by rw [← hp, hexp, Real.rpow_one]

/-- Linear growth of the original pressure gives the correct Haar density
bound, with no negative density power left in the majorant. -/
theorem abs_density_haar_pressure_le
    {theta a t Cb G : ℝ} (htheta : 0 ≤ theta) (I : ℝ → ℝ)
    (hI : ∀ v, |I v| ≤ Cb + |v| * G) :
    |theta ^ (1 - a) * I (t * theta ^ a)| ≤
      Cb * theta ^ (1 - a) + |t| * G * theta := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg htheta _)]
  calc
    _ ≤ theta ^ (1 - a) * (Cb + |t * theta ^ a| * G) :=
      mul_le_mul_of_nonneg_left (hI _) (Real.rpow_nonneg htheta _)
    _ = Cb * theta ^ (1 - a) + G * (theta ^ (1 - a) * |t * theta ^ a|) := by ring
    _ = _ := by rw [density_rpow_probe_weight htheta]; ring

/-- A finite upper density bound controls the Haar pressure; zero density and
arbitrarily small positive density are allowed. -/
theorem abs_density_haar_pressure_le_of_upper
    {theta U q t Cb G : ℝ} (htheta : 0 ≤ theta) (hupper : theta ≤ U)
    (hq : 2 < q) (hCb : 0 ≤ Cb) (hG : 0 ≤ G) (I : ℝ → ℝ)
    (hI : ∀ v, |I v| ≤ Cb + |v| * G) :
    |theta ^ (1 - 2 / q) * I (t * theta ^ (2 / q))| ≤
      Cb * U ^ (1 - 2 / q) + |t| * G * U := by
  have hq0 : 0 < q := by linarith
  have hp : 0 ≤ 1 - 2 / q := by
    have h := (div_lt_one hq0).mpr hq
    linarith
  exact (abs_density_haar_pressure_le htheta I hI).trans
    (add_le_add
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow htheta hupper hp) hCb)
      (mul_le_mul_of_nonneg_left hupper (mul_nonneg (abs_nonneg _) hG)))

/-- Absolute original population and Haar density-weighted pressure integrals
coincide under the same change of measure. -/
theorem integral_abs_withDensity_pressure_scale
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (theta : X → ℝ≥0∞) (hm : AEMeasurable theta μ)
    (hfinite : ∀ᵐ x ∂μ, theta x < ∞) {q : ℝ} (hq : 2 < q)
    (I : X → ℝ → ℝ) (t : ℝ) :
    (∫ x, |(theta x).toReal ^ (-2 / q) *
      I x (t * (theta x).toReal ^ (2 / q))| ∂μ.withDensity theta) =
      ∫ x, |(theta x).toReal ^ (1 - 2 / q) *
        I x (t * (theta x).toReal ^ (2 / q))| ∂μ := by
  calc
    _ = ∫ x, (theta x).toReal ^ (-2 / q) *
        |I x (t * (theta x).toReal ^ (2 / q))| ∂μ.withDensity theta := by
      apply integral_congr_ae
      exact .of_forall fun x ↦ by
        dsimp only
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
    _ = ∫ x, (theta x).toReal ^ (1 - 2 / q) *
        |I x (t * (theta x).toReal ^ (2 / q))| ∂μ :=
      integral_withDensity_pressure_scale μ theta hm hfinite hq (fun x v ↦ |I x v|) t
    _ = _ := by
      apply integral_congr_ae
      exact .of_forall fun x ↦ by
        dsimp only
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _)]

/-- Finite original Haar mass, an upper density bound and true linear local
pressure growth produce integrability of both corrected representations.
There is no lower density restriction or population-integrand uniform bound. -/
theorem integrable_density_pressure_of_upper_bound
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (theta : X → ℝ≥0∞) (hm : AEMeasurable theta μ)
    (hfinite : ∀ᵐ x ∂μ, theta x < ∞) {q : ℝ} (hq : 2 < q)
    (I : X → ℝ → ℝ) (t : ℝ) {U Cb G : ℝ}
    (hCb : 0 ≤ Cb) (hG : 0 ≤ G)
    (hupper : ∀ᵐ x ∂μ, (theta x).toReal ≤ U)
    (hread : AEStronglyMeasurable
      (fun x ↦ I x (t * (theta x).toReal ^ (2 / q))) μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ v, |I x v| ≤ Cb + |v| * G) :
    Integrable (fun x ↦ (theta x).toReal ^ (-2 / q) *
        I x (t * (theta x).toReal ^ (2 / q))) (μ.withDensity theta) ∧
      Integrable (fun x ↦ (theta x).toReal ^ (1 - 2 / q) *
        I x (t * (theta x).toReal ^ (2 / q))) μ ∧
      (∫ x, |(theta x).toReal ^ (-2 / q) *
        I x (t * (theta x).toReal ^ (2 / q))| ∂μ.withDensity theta) ≤
        (Cb * U ^ (1 - 2 / q) + |t| * G * U) * μ.real Set.univ := by
  have hq0 : 0 < q := by linarith
  have hp : 0 ≤ 1 - 2 / q := by
    have h := (div_lt_one hq0).mpr hq
    linarith
  let B := Cb * U ^ (1 - 2 / q) + |t| * G * U
  have hpow : AEStronglyMeasurable (fun x ↦ (theta x).toReal ^ (1 - 2 / q)) μ :=
    (Real.continuous_rpow_const hp).comp_aestronglyMeasurable hm.ennreal_toReal.aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, |(theta x).toReal ^ (1 - 2 / q) *
      I x (t * (theta x).toReal ^ (2 / q))| ≤ B := by
    filter_upwards [hupper, hgrowth] with x hx hI
    exact abs_density_haar_pressure_le_of_upper ENNReal.toReal_nonneg hx hq hCb hG (I x) hI
  have hH : Integrable (fun x ↦ (theta x).toReal ^ (1 - 2 / q) *
      I x (t * (theta x).toReal ^ (2 / q))) μ := by
    apply Integrable.of_bound (hpow.mul hread) B
    simpa only [Real.norm_eq_abs, Pi.mul_apply] using hbound
  refine ⟨(integrable_withDensity_pressure_scale_iff μ theta hm hfinite hq I t).mpr hH, hH, ?_⟩
  rw [integral_abs_withDensity_pressure_scale μ theta hm hfinite hq I t]
  calc
    _ ≤ ∫ _x, B ∂μ := integral_mono_ae hH.abs (integrable_const B) hbound
    _ = _ := by rw [integral_const]; simp only [smul_eq_mul, mul_comm, B]

end OTSelector.Probability
