import OTSelector.Probability.BirthDyadicTrafficLevelNorm

/-! A uniform nonnegative mean-square error is paid once per actual finite
birth band, while the two original energy budgets keep their square-root
number-of-bands gain. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- The literal finite traffic sum keeps the shared energy budget and pays
the square root of the uniform mean-square remainder for each band. -/
theorem finiteBand_traffic_memLp_two_of_quadratic_energy_budget_remainder
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ s, MemLp (T i) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {cE cV E V R : ℝ} (hcE : 0 ≤ cE) (hcV : 0 ≤ cV) (hR : 0 ≤ R)
    (hE : (∑ i ∈ s, e i) ≤ E) (hV : (∑ i ∈ s, v i) ≤ V)
    (hmean : ∀ i ∈ s, (∫ x, T i x ^ 2 ∂P) ≤ cE * e i + cV * v i + R) :
    MemLp (fun x ↦ ∑ i ∈ s, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ s, T i x) 2 P ≤
        ENNReal.ofReal (Real.sqrt (s.card : ℝ) *
          (Real.sqrt cE * Real.sqrt E + Real.sqrt cV * Real.sqrt V) +
            (s.card : ℝ) * Real.sqrt R) := by
  have hsumroot : (∑ i ∈ s, (Real.sqrt cE * Real.sqrt (e i) +
      Real.sqrt cV * Real.sqrt (v i))) ≤ Real.sqrt (s.card : ℝ) *
      (Real.sqrt cE * Real.sqrt E + Real.sqrt cV * Real.sqrt V) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      _ ≤ Real.sqrt cE * (Real.sqrt (s.card : ℝ) * Real.sqrt E) +
          Real.sqrt cV * (Real.sqrt (s.card : ℝ) * Real.sqrt V) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (sum_sqrt_energy_le_card_sqrt_mul s e he hE) (Real.sqrt_nonneg _))
          (mul_le_mul_of_nonneg_left (sum_sqrt_energy_le_card_sqrt_mul s v hv hV)
            (Real.sqrt_nonneg _))
      _ = _ := by ring
  refine ⟨memLp_finsetSum s hT, ?_⟩
  calc
    _ = eLpNorm (∑ i ∈ s, T i) 2 P := by congr 1; funext x; simp
    _ ≤ ∑ i ∈ s, eLpNorm (T i) 2 P :=
      eLpNorm_sum_le (fun i hi ↦ (hT i hi).aestronglyMeasurable) (by norm_num)
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (Real.sqrt cE * Real.sqrt (e i) +
        Real.sqrt cV * Real.sqrt (v i) + Real.sqrt R) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (eLpNorm_two_le_sqrt_of_integral_sq_le (hT i hi) (hmean i hi)).trans
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ Real.sqrt (cE * e i + cV * v i) + Real.sqrt R :=
          sqrt_add_energy_le_sqrt_terms
            (add_nonneg (mul_nonneg hcE (he i)) (mul_nonneg hcV (hv i))) hR
        _ ≤ (Real.sqrt (cE * e i) + Real.sqrt (cV * v i)) + Real.sqrt R :=
          add_le_add (sqrt_add_energy_le_sqrt_terms
            (mul_nonneg hcE (he i)) (mul_nonneg hcV (hv i))) le_rfl
        _ = _ := by rw [Real.sqrt_mul hcE, Real.sqrt_mul hcV]
    _ = ENNReal.ofReal (∑ i ∈ s, (Real.sqrt cE * Real.sqrt (e i) +
        Real.sqrt cV * Real.sqrt (v i) + Real.sqrt R)) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] using
        add_le_add hsumroot (le_refl ((s.card : ℝ) * Real.sqrt R))

/-- The actual number and width of the bands give the original physical
power coefficients, with the uniform remainder still counted per band. -/
theorem birthBand_traffic_memLp_two_of_quadratic_power_budget_remainder
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ bands, MemLp (T i) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {E V t s C R : ℝ} (ht : 0 < t) (hs : 0 < s) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hNs : (bands.card : ℝ) * s = 8 * t)
    (hE : (∑ i ∈ bands, e i) ≤ E) (hV : (∑ i ∈ bands, v i) ≤ V)
    (rE rV : ℝ)
    (hmean : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      C * s ^ 2 * (t ^ rE * e i + t ^ rV * v i) + R) :
    MemLp (fun x ↦ ∑ i ∈ bands, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤
        ENNReal.ofReal (Real.sqrt 8 * Real.sqrt C * Real.sqrt (s / t) *
          (t ^ (rE / 2 + 1) * Real.sqrt E + t ^ (rV / 2 + 1) * Real.sqrt V) +
            (bands.card : ℝ) * Real.sqrt R) := by
  have h := finiteBand_traffic_memLp_two_of_quadratic_energy_budget_remainder
    P bands T hT e v he hv
    (cE := C * s ^ 2 * t ^ rE) (cV := C * s ^ 2 * t ^ rV)
    (by positivity) (by positivity) hR hE hV
    (by intro i hi; simpa only [mul_add, mul_assoc] using hmean i hi)
  refine ⟨h.1, h.2.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  have hE' := birthBand_sqrt_quadratic_coefficient ht hs hC hNs rE
  have hV' := birthBand_sqrt_quadratic_coefficient ht hs hC hNs rV
  calc
    _ = (Real.sqrt (bands.card : ℝ) * Real.sqrt (C * s ^ 2 * t ^ rE)) * Real.sqrt E +
        (Real.sqrt (bands.card : ℝ) * Real.sqrt (C * s ^ 2 * t ^ rV)) * Real.sqrt V +
        (bands.card : ℝ) * Real.sqrt R := by ring
    _ = _ := by rw [hE', hV']; ring

/-- The large physical traffic level keeps the sharp shared-energy decay and
adds only the actual finite-band uniform-error cost. -/
theorem birthBand_large_traffic_level_norm_remainder
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (bands : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ bands, MemLp (T i) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {E t s C q R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s)
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hNs : (bands.card : ℝ) * s = 8 * t)
    (hE : (∑ i ∈ bands, e i) ≤ E) (hV : (∑ i ∈ bands, v i) ≤ E)
    (hmean : ∀ i ∈ bands, (∫ x, T i x ^ 2 ∂P) ≤
      C * s ^ 2 * (t ^ (-2 + 1 / q) * e i + t ^ (-1 + 1 / q) * v i) + R) :
    MemLp (fun x ↦ ∑ i ∈ bands, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i x) 2 P ≤
        ENNReal.ofReal (2 * Real.sqrt 8 * Real.sqrt C * Real.sqrt E *
          t ^ (1 / (2 * q)) * Real.sqrt (s / t) + (bands.card : ℝ) * Real.sqrt R) := by
  have h := birthBand_traffic_memLp_two_of_quadratic_power_budget_remainder
    P bands T hT e v he hv ht hs hC hR hNs hE hV (-2 + 1 / q) (-1 + 1 / q) hmean
  have hp₁ : (-2 + 1 / q) / 2 + 1 = 1 / (2 * q) := by ring
  have hp₂ : (-1 + 1 / q) / 2 + 1 = (1 / (2 * q)) + 1 / 2 := by ring
  rw [hp₁, hp₂] at h
  refine ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  apply add_le_add _ le_rfl
  have hb := sqrt_energy_power_pair_le (a := 1 / (2 * q)) (b := (1 / 2 : ℝ))
    ht ht1 (σ := s / t) (by positivity)
    (A := Real.sqrt 8 * Real.sqrt C) (by positivity) (by norm_num) (V := E) le_rfl
  simpa only [mul_assoc] using hb

end OTSelector.Probability
