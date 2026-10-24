import OTSelector.Reconstruction.FinslerRelativeLawLegalCountExpectation

/-! Original independent binomial prefixes with their changing physical kinetic multiplier. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem abs_legalFixedSeqValue_multiplier_sub_le (q m k : ℕ)
    (source : A → ℝ) (target : B → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (probe : A → B → ℝ) (t c d : ℝ)
    (z : (ℕ → (Fin q → ℝ) × A) × (ℕ → (Fin q → ℝ) × B)) :
    |legalFixedSeqValue q source target 1 (fun a b v ↦ c * kin a b v) probe t m k z -
      legalFixedSeqValue q source target 1 (fun a b v ↦ d * kin a b v) probe t m k z| ≤
      (|c - d| * (C * q)) * ((min m k : ℕ) : ℝ) := by
  let ω : TwoMarkedCloudSpace q A B := ((m, z.1), (k, z.2))
  have hentry (i : Fin m) (j : Fin k) :
      |(mKineticCost q 1 (fun a b v ↦ c * kin a b v) ω i j + t * mProbe probe ω i j) -
        (mKineticCost q 1 (fun a b v ↦ d * kin a b v) ω i j + t * mProbe probe ω i j)| ≤
        |c - d| * (C * q) := by
    have hk : |kin (mSourceMark ω i) (mTargetMark ω j)
        (mDisplacement (mSourcePoint ω i) (mTargetPoint ω j))| ≤ C * q :=
      (hkb _ _ _).trans (mul_le_mul_of_nonneg_left (mDisplacement_sq_sum_le q _ _) hC)
    simp only [mKineticCost, Real.one_rpow, one_mul]
    rw [add_sub_add_right_eq_sub, ← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left hk (abs_nonneg _)
  have h := PartialMatching.abs_legalMaximumValue_sub_le_of_allowed
    (legalMarkedGraph q m k source target ω)
    (fun i j ↦ mKineticCost q 1 (fun a b v ↦ c * kin a b v) ω i j + t * mProbe probe ω i j)
    (fun i j ↦ mKineticCost q 1 (fun a b v ↦ d * kin a b v) ω i j + t * mProbe probe ω i j)
    (fun i j _ ↦ hentry i j)
  exact h.trans ((mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (PartialMatching.legalMaximumCard_le_min _))
    (mul_nonneg (abs_nonneg _) (mul_nonneg hC (Nat.cast_nonneg q)))).trans_eq (by ring))

theorem abs_legalFixedSeqExpectation_multiplier_sub_le (q m k : ℕ)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t c d : ℝ) :
    |legalFixedSeqExpectation q source target α β 1 (fun a b v ↦ c * kin a b v) probe t m k -
      legalFixedSeqExpectation q source target α β 1 (fun a b v ↦ d * kin a b v) probe t m k| ≤
      (|c - d| * (C * q)) * ((min m k : ℕ) : ℝ) := by
  have hki (s : ℝ) : ∀ a b v, |s * kin a b v| ≤ (|s| * C) * ∑ l, v l ^ 2 := by
    intro a b v
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hkb a b v) (abs_nonneg s)).trans_eq (by ring)
  have hi (s : ℝ) := integrable_legalFixedSeqValue (kin := fun a b v ↦ s * kin a b v) q m k hs ht α β (by norm_num : (0:ℝ) ≤ 1)
    (mul_nonneg (abs_nonneg s) hC) hG (hk.const_mul s) (hki s) hp hpb t
  rw [legalFixedSeqExpectation, legalFixedSeqExpectation, ← integral_sub (hi c) (hi d),
    ← Real.norm_eq_abs]
  have h := norm_integral_le_of_norm_le_const
    (μ := (markedSeqLaw q A α).prod (markedSeqLaw q B β))
    (C := (|c - d| * (C * q)) * ((min m k : ℕ) : ℝ))
    (Filter.Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs]
      exact abs_legalFixedSeqValue_multiplier_sub_le q m k source target hC kin hkb probe t c d z)
  simpa [measureReal_def] using h

/-- Rounded physical scales and original independent binomial counts converge
jointly to the literal legal Poisson model, including Hall-deficient clouds. -/
theorem tendsto_legalMarkedTilted_binomial_multiplier (q : ℕ)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G)
    (c : ℕ → ℝ) {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀))
    (p : ℕ → I) (r : ℝ≥0)
    (hr : Tendsto (fun n : ℕ ↦ (n : ℝ) * (p n : ℝ)) atTop (𝓝 (r : ℝ))) (t : ℝ) :
    Tendsto (fun n ↦ ∫ ω, legalMarkedTilted q source target 1
        (fun a b v ↦ c n * kin a b v) probe t ω
        ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial n (p n))) atTop
      (𝓝 (∫ ω, legalMarkedTilted q source target 1 (fun a b v ↦ c₀ * kin a b v) probe t ω
        ∂twoMarkedCloudLaw q A B α β r)) := by
  let F := fun n m k ↦ legalFixedSeqExpectation q source target α β 1
    (fun a b v ↦ c n * kin a b v) probe t m k
  let H := legalFixedSeqExpectation q source target α β 1
    (fun a b v ↦ c₀ * kin a b v) probe t
  have hki (s : ℝ) : ∀ a b v, |s * kin a b v| ≤ (|s| * C) * ∑ l, v l ^ 2 := by
    intro a b v
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (hkb a b v) (abs_nonneg s)).trans_eq (by ring)
  have hH : ∀ m k, |H m k| ≤ (|c₀| * C * q + |t| * G) * ((min m k : ℕ) : ℝ) := by
    intro m k
    simpa only [H, Real.one_rpow, one_mul, mul_assoc] using
      abs_legalFixedSeqExpectation_le q m k source target α β (by norm_num : (0:ℝ) ≤ 1)
        (mul_nonneg (abs_nonneg c₀) hC) hG (hki c₀) hpb t
  have hδ : Tendsto (fun n ↦ |c n - c₀| * (C * q)) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_mul] using (hc.sub (tendsto_const_nhds (x := c₀))).abs.mul_const (C * q)
  have hlimit := tendsto_two_count_binomial_poisson_varying F H
    (by positivity : 0 ≤ |c₀| * C * q + |t| * G) hH
    (fun n ↦ |c n - c₀| * (C * q)) (fun _ ↦ by positivity) hδ
    (fun n m k ↦ abs_legalFixedSeqExpectation_multiplier_sub_le q m k hs ht α β hC hG
      hk hkb hp hpb t (c n) c₀) p r hr
  have hbinomial (n : ℕ) : (∫ ω, legalMarkedTilted q source target 1
      (fun a b v ↦ c n * kin a b v) probe t ω
      ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial n (p n))) =
      binomialPairExpectation n (p n) (F n) := by
    rw [integral_legalMarkedTilted_countLaw_eq_fixed
      (kin := fun a b v ↦ c n * kin a b v) q hs ht α β _ (integrable_binomial _)
      (by norm_num : (0:ℝ) ≤ 1) (mul_nonneg (abs_nonneg (c n)) hC) hG
      (hk.const_mul (c n)) (hki (c n)) hp hpb t]
    simp_rw [integral_binomial_real]
    simp only [binomialPairExpectation, Finset.mul_sum, ← mul_assoc, F]
  have hpoisson : (∫ ω, legalMarkedTilted q source target 1
      (fun a b v ↦ c₀ * kin a b v) probe t ω ∂twoMarkedCloudLaw q A B α β r) =
      ∑' m, poissonMass r m * ∑' k, poissonMass r k * H m k := by
    rw [show twoMarkedCloudLaw q A B α β r = twoMarkedCountLaw q α β (poissonMeasure r) from rfl,
      integral_legalMarkedTilted_countLaw_eq_fixed
        (kin := fun a b v ↦ c₀ * kin a b v) q hs ht α β _ (integrable_id_poissonMeasure r)
        (by norm_num : (0:ℝ) ≤ 1) (mul_nonneg (abs_nonneg c₀) hC) hG
        (hk.const_mul c₀) (hki c₀) hp hpb t]
    simp_rw [integral_poissonMeasure]
    rfl
  simpa only [hbinomial, hpoisson] using hlimit

end OTSelector.Reconstruction
