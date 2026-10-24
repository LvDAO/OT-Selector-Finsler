import OTSelector.Probability.PoissonCountExhaustion
import OTSelector.Reconstruction.OriginalStationaryFiniteIntensityCounts

/-! Uniform full-input count bounds for finite deterministic candidate families. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Probability

/-- A finite exponential-moment bound gives the same upper count-tail estimate;
an integer-valued selector or an exact law of a later selected count is unnecessary. -/
theorem measure_ge_ennreal_count_le_exp_of_exp_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {N : Ω → ℝ≥0∞} {r t : ℝ} (ht : 0 ≤ t)
    (hint : Integrable (fun ω ↦ Real.exp (t * (N ω).toReal)) P)
    (hbound : (∫ ω, Real.exp (t * (N ω).toReal) ∂P) ≤
      Real.exp (r * (Real.exp t - 1))) (x : ℝ) :
    P.real {ω | x ≤ (N ω).toReal} ≤ Real.exp (r * (Real.exp t - 1) - t * x) := by
  have h := measure_ge_le_exp_mul_mgf (μ := P) (X := fun ω ↦ (N ω).toReal) x ht hint
  calc
    _ ≤ Real.exp (-t * x) * (∫ ω, Real.exp (t * (N ω).toReal) ∂P) := by
      simpa only [mgf] using h
    _ ≤ Real.exp (-t * x) * Real.exp (r * (Real.exp t - 1)) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Exponentially many full original finite-intensity counts obey one uniform
exceptional-event estimate; candidate independence is not used. -/
theorem measure_biUnion_ennreal_count_le_exp
    {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (S : Finset I) (N : I → Ω → ℝ≥0∞) (rate : I → ℝ)
    (hint : ∀ i ∈ S, Integrable (fun ω ↦ Real.exp ((N i ω).toReal)) P)
    (hbound : ∀ i ∈ S, (∫ ω, Real.exp ((N i ω).toReal) ∂P) ≤
      Real.exp (rate i * (Real.exp 1 - 1)))
    {a b m K : ℝ} (hcard : (S.card : ℝ) ≤ Real.exp (a * m))
    (hrate : ∀ i ∈ S, rate i ≤ b * m) :
    P.real (⋃ i ∈ S, {ω | K * m ≤ (N i ω).toReal}) ≤
      Real.exp (-(K - a - b * (Real.exp 1 - 1)) * m) := by
  have he : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr
    (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num))
  have hsingle (i : I) (hi : i ∈ S) :
      P.real {ω | K * m ≤ (N i ω).toReal} ≤
        Real.exp (b * m * (Real.exp 1 - 1) - K * m) := by
    have h := measure_ge_ennreal_count_le_exp_of_exp_moment (N := N i) (t := 1)
      (by norm_num) (by simpa only [one_mul] using hint i hi)
      (by simpa only [one_mul] using hbound i hi) (K * m)
    apply h.trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (hrate i hi) he]
  calc
    _ ≤ ∑ i ∈ S, P.real {ω | K * m ≤ (N i ω).toReal} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ S, Real.exp (b * m * (Real.exp 1 - 1) - K * m) :=
      Finset.sum_le_sum hsingle
    _ = (S.card : ℝ) * Real.exp (b * m * (Real.exp 1 - 1) - K * m) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (a * m) * Real.exp (b * m * (Real.exp 1 - 1) - K * m) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end OTSelector.Probability
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The genuine original source input satisfies the uniform candidate bound on
arbitrary measurable finite-intensity sets, before any adaptive path selection. -/
theorem LegalWeightedStationaryPoissonMatching.original_source_candidates_count_le_exp
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {I : Type*} (S : Finset I) (B : I → Set (LegalMarkedPhysicalPoint q))
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hfin : ∀ i ∈ S, ((volume : Measure (Fin q → ℝ)).prod α) (B i) ≠ ∞)
    {a b m K : ℝ} (hcard : (S.card : ℝ) ≤ Real.exp (a * m))
    (hrate : ∀ i ∈ S, (((volume : Measure (Fin q → ℝ)).prod α) (B i)).toReal ≤ b * m) :
    (M.law : Measure (LegalMarkedOptimalInputScene q)).real
      (⋃ i ∈ S, {s | K * m ≤ ((s.2 : Measure (LegalColoredInputPoint q))
        (B i ×ˢ {0})).toReal}) ≤
          Real.exp (-(K - a - b * (Real.exp 1 - 1)) * m) := by
  have hm := fun i hi ↦ M.original_source_exp_moment_of_finite_intensity (hB i hi)
    (hfin i hi) (show (0 : ℝ) ≤ 1 by norm_num)
  exact measure_biUnion_ennreal_count_le_exp S _ _
    (fun i hi ↦ by simpa only [one_mul] using (hm i hi).2.1)
    (fun i hi ↦ by simpa only [one_mul] using (hm i hi).2.2) hcard hrate

/-- The same unchanged original-input estimate holds for target candidates. -/
theorem LegalWeightedStationaryPoissonMatching.original_target_candidates_count_le_exp
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {I : Type*} (S : Finset I) (B : I → Set (LegalMarkedPhysicalPoint q))
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hfin : ∀ i ∈ S, ((volume : Measure (Fin q → ℝ)).prod β) (B i) ≠ ∞)
    {a b m K : ℝ} (hcard : (S.card : ℝ) ≤ Real.exp (a * m))
    (hrate : ∀ i ∈ S, (((volume : Measure (Fin q → ℝ)).prod β) (B i)).toReal ≤ b * m) :
    (M.law : Measure (LegalMarkedOptimalInputScene q)).real
      (⋃ i ∈ S, {s | K * m ≤ ((s.2 : Measure (LegalColoredInputPoint q))
        (B i ×ˢ {1})).toReal}) ≤
          Real.exp (-(K - a - b * (Real.exp 1 - 1)) * m) := by
  have hm := fun i hi ↦ M.original_target_exp_moment_of_finite_intensity (hB i hi)
    (hfin i hi) (show (0 : ℝ) ≤ 1 by norm_num)
  exact measure_biUnion_ennreal_count_le_exp S _ _
    (fun i hi ↦ by simpa only [one_mul] using (hm i hi).2.1)
    (fun i hi ↦ by simpa only [one_mul] using (hm i hi).2.2) hcard hrate

end OTSelector.Reconstruction
