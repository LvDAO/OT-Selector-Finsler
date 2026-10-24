import OTSelector.Reconstruction.FinslerRelativeLawLegalCountExpectation

/-! Exact tilt modulus for the original independent binomial legal clouds. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The actual signed binomial legal mean has its original expected-count tilt
modulus, regardless of the kinetic scale or the realized Hall deficit. -/
theorem abs_integral_legalMarkedTilted_binomial_tilt_sub_le (q : ℕ)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) {r C G : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t u : ℝ) :
    |(∫ cloud, legalMarkedTilted q source target r kin probe t cloud
        ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)) -
      (∫ cloud, legalMarkedTilted q source target r kin probe u cloud
        ∂twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p))| ≤
      ((N : ℝ) * (p : ℝ)) * (G * |t - u|) := by
  let P := twoMarkedCountLaw q α β (ProbabilityTheory.binomial N p)
  have hi (s : ℝ) : Integrable (legalMarkedTilted q source target r kin probe s) P :=
    integrable_legalMarkedTilted_countLaw q hs ht α β (ProbabilityTheory.binomial N p)
      (integrable_binomial _) hr hC hG hk hkb hp hpb s
  have hc : Integrable (fun cloud : TwoMarkedCloudSpace q A B ↦ (mSourceCount cloud : ℝ)) P :=
    ((integrable_binomial (n := N) (p := p) (fun n ↦ (n : ℝ))).comp_fst (markedSeqLaw q A α)).comp_fst
      (markedCountLaw q β (ProbabilityTheory.binomial N p))
  have hmean : (∫ cloud : TwoMarkedCloudSpace q A B, (mSourceCount cloud : ℝ) ∂P) =
      (N : ℝ) * (p : ℝ) := by
    change (∫ cloud : MarkedCloudSpace q A × MarkedCloudSpace q B, (cloud.1.1 : ℝ)
      ∂(markedCountLaw q α (ProbabilityTheory.binomial N p)).prod
        (markedCountLaw q β (ProbabilityTheory.binomial N p))) = _
    rw [integral_fun_fst (fun z : MarkedCloudSpace q A ↦ (z.1 : ℝ))]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    change (∫ z : ℕ × (ℕ → (Fin q → ℝ) × A), (z.1 : ℝ)
      ∂(ProbabilityTheory.binomial N p).prod (markedSeqLaw q A α)) = _
    rw [integral_fun_fst (fun n : ℕ ↦ (n : ℝ))]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    exact integral_binomial_id N p
  have hpoint : ∀ cloud : TwoMarkedCloudSpace q A B,
      |legalMarkedTilted q source target r kin probe t cloud -
        legalMarkedTilted q source target r kin probe u cloud| ≤
      (mSourceCount cloud : ℝ) * (G * |t - u|) := by
    intro cloud
    exact (abs_legalMarkedTilted_sub_le q source target kin probe
      (fun a b _ ↦ hpb a b) r t u cloud).trans
      (mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr ((PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _)))
        (mul_nonneg hG (abs_nonneg _)))
  rw [← integral_sub (hi t) (hi u)]
  calc
    _ ≤ ∫ cloud, |legalMarkedTilted q source target r kin probe t cloud -
      legalMarkedTilted q source target r kin probe u cloud| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ cloud : TwoMarkedCloudSpace q A B,
        (mSourceCount cloud : ℝ) * (G * |t - u|) ∂P :=
      integral_mono (hi t |>.sub (hi u) |>.abs) (hc.mul_const _) hpoint
    _ = _ := by rw [integral_mul_const, hmean]

end OTSelector.Reconstruction
