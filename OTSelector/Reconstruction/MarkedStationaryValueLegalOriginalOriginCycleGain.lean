import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalRelativeCycleSelector
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalWeightedSourceReadout

/-! Actual two-source signed gains of the constructed origin-cell selector. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false

variable {q : ℕ} {c : LegalMarkedPhysicalEdge q → ℝ} {ell ε : ℝ}

/-- Saving charged to the first original source atom, and zero on inactive scenes. -/
def OriginalOriginCycleSelector.firstGain (S : OriginalOriginCycleSelector q c ell ε)
    (s : LegalMarkedOptimalInputScene q) : ℝ :=
  S.active.indicator (fun s ↦ c (S.pair s).1 - c ((S.pair s).1.1, (S.pair s).2.2)) s

/-- Saving charged to the second unchanged original source atom. -/
def OriginalOriginCycleSelector.secondGain (S : OriginalOriginCycleSelector q c ell ε)
    (s : LegalMarkedOptimalInputScene q) : ℝ :=
  S.active.indicator (fun s ↦ c (S.pair s).2 - c ((S.pair s).2.1, (S.pair s).1.2)) s

/-- Exact total saving of the same two original sources in the reference cell. -/
def OriginalOriginCycleSelector.gain (S : OriginalOriginCycleSelector q c ell ε)
    (s : LegalMarkedOptimalInputScene q) : ℝ := S.firstGain s + S.secondGain s

theorem OriginalOriginCycleSelector.measurable_firstGain
    (S : OriginalOriginCycleSelector q c ell ε) (hc : Measurable c) :
    Measurable S.firstGain :=
  ((hc.comp S.measurable_pair.fst).sub (hc.comp
    (S.measurable_pair.fst.fst.prodMk S.measurable_pair.snd.snd))).indicator S.measurable_active

theorem OriginalOriginCycleSelector.measurable_secondGain
    (S : OriginalOriginCycleSelector q c ell ε) (hc : Measurable c) :
    Measurable S.secondGain :=
  ((hc.comp S.measurable_pair.snd).sub (hc.comp
    (S.measurable_pair.snd.fst.prodMk S.measurable_pair.fst.snd))).indicator S.measurable_active

theorem OriginalOriginCycleSelector.measurable_gain
    (S : OriginalOriginCycleSelector q c ell ε) (hc : Measurable c) : Measurable S.gain :=
  (S.measurable_firstGain hc).add (S.measurable_secondGain hc)

/-- The certificate yields a pointwise positive threshold for the literal gain. -/
theorem OriginalOriginCycleSelector.threshold_le_gain
    (S : OriginalOriginCycleSelector q c ell ε) (s : LegalMarkedOptimalInputScene q) :
    S.active.indicator (fun _ ↦ ε) s ≤ S.gain s := by
  by_cases ha : s ∈ S.active
  · have hcert := (S.certificate s ha).2.2.2.2.2
    simp only [gain, firstGain, secondGain, Set.indicator_of_mem ha]
    linarith
  · simp only [gain, firstGain, secondGain, Set.indicator_of_notMem ha, add_zero, le_refl]

theorem OriginalOriginCycleSelector.gain_nonneg
    (S : OriginalOriginCycleSelector q c ell ε) (hε : 0 ≤ ε)
    (s : LegalMarkedOptimalInputScene q) : 0 ≤ S.gain s :=
  le_trans (Set.indicator_nonneg (fun _ _ ↦ hε) s) (S.threshold_le_gain s)

/-- Two endpoints in the actual same cell differ by at most its side length
in each coordinate; no mark or clock bound is introduced here. -/
theorem sum_sq_displacement_le_of_originalCompleteGridCell
    {ell : ℝ} (_hell : 0 ≤ ell) (b : Fin q → ℝ)
    (e : LegalMarkedPhysicalEdge q) (he : e ∈ originalCompleteGridCell q ell b 0) :
    (∑ i, (e.2.1 - e.1.1) i ^ 2) ≤ (q : ℝ) * ell ^ 2 := by
  have hsum : (∑ i, (e.2.1 - e.1.1) i ^ 2) ≤ ∑ _ : Fin q, ell ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have h₁ := he.1 i (Set.mem_univ i)
    have h₂ := he.2 i (Set.mem_univ i)
    simp only [zero_vadd] at h₁ h₂
    change 0 < e.1.1 i - b i ∧ e.1.1 i - b i ≤ ell at h₁
    change 0 < e.2.1 i - b i ∧ e.2.1 i - b i ≤ ell at h₂
    change (e.2.1 i - e.1.1 i) ^ 2 ≤ ell ^ 2
    have hab : |e.2.1 i - e.1.1 i| ≤ ell := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [sq_abs (e.2.1 i - e.1.1 i)]
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum

/-- The already produced global quadratic coefficient bound controls the
actual weighted cost inside a complete cell, including the two crossed edges. -/
theorem abs_originalWeightedEdgeCost_le_of_completeGridCell
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G) {ell : ℝ} (hell : 0 ≤ ell)
    (b : Fin q → ℝ) (e : LegalMarkedPhysicalEdge q)
    (he : e ∈ originalCompleteGridCell q ell b 0) :
    |originalWeightedEdgeCost kin g t e| ≤ C * ((q : ℝ) * ell ^ 2) + |t| * G := by
  apply le_trans (abs_add_le _ _)
  apply add_le_add
  · exact (hkb _ _ _).trans (mul_le_mul_of_nonneg_left
      (sum_sq_displacement_le_of_originalCompleteGridCell hell b e he) hC)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hgb _ _) (abs_nonneg _)

/-- Both literal source-atom gains are integrable under every finite original
scene law. The required bound is derived from the existing quadratic bound. -/
theorem OriginalOriginCycleSelector.atomGains_integrable
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ} (t : ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |g a b| ≤ G) (hell : 0 ≤ ell)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin g t) ell ε)
    (P : Measure (LegalMarkedOptimalInputScene q)) [IsFiniteMeasure P] :
    Integrable S.firstGain P ∧ Integrable S.secondGain P := by
  let B := C * ((q : ℝ) * ell ^ 2) + |t| * G
  have hG : 0 ≤ G := (abs_nonneg (g 0 0)).trans (hgb 0 0)
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hC (mul_nonneg (Nat.cast_nonneg q)
    (sq_nonneg ell))) (mul_nonneg (abs_nonneg t) hG)
  have hb := abs_originalWeightedEdgeCost_le_of_completeGridCell kin g t hC hkb hgb hell 0
  have hbound (s : LegalMarkedOptimalInputScene q) :
      |S.firstGain s| ≤ 2 * B ∧ |S.secondGain s| ≤ 2 * B := by
    by_cases ha : s ∈ S.active
    · have he := (S.certificate s ha).2.1
      have hf := (S.certificate s ha).2.2.1
      have hc₁ := hb (S.pair s).1 he
      have hc₂ := hb (S.pair s).2 hf
      have hc₃ := hb ((S.pair s).1.1, (S.pair s).2.2) ⟨he.1, hf.2⟩
      have hc₄ := hb ((S.pair s).2.1, (S.pair s).1.2) ⟨hf.1, he.2⟩
      simp only [firstGain, secondGain, Set.indicator_of_mem ha]
      exact ⟨(abs_sub _ _).trans (by linarith), (abs_sub _ _).trans (by linarith)⟩
    · simp only [firstGain, secondGain, Set.indicator_of_notMem ha, abs_zero]
      exact ⟨by positivity, by positivity⟩
  have hc := measurable_originalWeightedEdgeCost kin hk g hg t
  constructor
  · exact (integrable_const (2 * B)).mono' (S.measurable_firstGain hc).aestronglyMeasurable
      (Eventually.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using (hbound s).1))
  · exact (integrable_const (2 * B)).mono' (S.measurable_secondGain hc).aestronglyMeasurable
      (Eventually.of_forall (fun s ↦ by simpa only [Real.norm_eq_abs] using (hbound s).2))

/-- Positive probability of a certified original pair gives a strictly
positive mean saving, with the literal event mass and certificate threshold. -/
theorem OriginalOriginCycleSelector.integral_gain_pos
    (S : OriginalOriginCycleSelector q c ell ε) (P : Measure (LegalMarkedOptimalInputScene q))
    [IsFiniteMeasure P] (hε : 0 < ε) (hi : Integrable S.gain P) (hA : 0 < P S.active) :
    0 < ∫ s, S.gain s ∂P := by
  have hthr : Integrable (S.active.indicator (fun _ ↦ ε)) P :=
    (integrable_const ε).indicator S.measurable_active
  have hle := integral_mono hthr hi (S.threshold_le_gain)
  have he : (∫ s, S.active.indicator (fun _ ↦ ε) s ∂P) = (P S.active).toReal * ε := by
    rw [integral_indicator S.measurable_active, setIntegral_const, measureReal_def, smul_eq_mul]
  rw [he] at hle
  exact (mul_pos (ENNReal.toReal_pos hA.ne' (measure_ne_top P S.active)) hε).trans_le hle

end OTSelector.Reconstruction
