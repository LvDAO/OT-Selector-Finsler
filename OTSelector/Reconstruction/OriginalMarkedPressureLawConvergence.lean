import OTSelector.Reconstruction.OriginalMarkedPressureLawContinuity

/-! Actual original common-sampling convergence gives true fixed-box legal
pressure convergence. Only original used-prefix disagreements are charged. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- Vanishing actual original common-sampling disagreement implies convergence
of the full original finite-intensity pressure, with unchanged positions/counts. -/
theorem tendsto_legalMarkedPressure_of_original_mark_couplings
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableEq A] [MeasurableEq B]
    (q : ℕ) {range : Set ℝ} {gap : ℝ} (coarse : FiniteScalarBins range gap) (hgap : 0 < gap)
    (source : A → ℝ) (target : B → ℝ) (hs : Measurable source) (ht : Measurable target)
    (κS : ℕ → ProbabilityMeasure (A × A)) (κT : ℕ → ProbabilityMeasure (B × B))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (hmapS : ∀ n, (κS n : Measure (A × A)).map Prod.snd = α)
    (hmapT : ∀ n, (κT n : Measure (B × B)).map Prod.snd = β)
    (hsource : ∀ n, ∀ᵐ a ∂(κS n : Measure (A × A)), source a.1 ∈ range ∧ source a.2 ∈ range)
    (hsep : ∀ n, ∀ᵐ p ∂(κS n : Measure (A × A)).prod (κT n : Measure (B × B)),
      gap ≤ |target p.2.1 - source p.1.1| ∧ gap ≤ |target p.2.2 - source p.1.2|)
    (hdisagreement : Tendsto (fun n ↦
      ((κS n : Measure (A × A)) {p | p.1 ≠ p.2}).toReal +
      ((κT n : Measure (B × B)) {p | p.1 ≠ p.2}).toReal) atTop (𝓝 0))
    (r : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (probe : A → B → ℝ) (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    Tendsto (fun n ↦ legalMarkedPressure q source target
      ((κS n).map measurable_fst.aemeasurable : Measure A)
      ((κT n).map measurable_fst.aemeasurable : Measure B) r kin probe t) atTop
        (𝓝 (legalMarkedPressure q source target α β r kin probe t)) := by
  let coefficient := 4 * ((coarse.count : ℝ) + 1) *
    ((r : ℝ) ^ (2 / (q : ℝ)) * (C * (q : ℝ)) + |t| * G) * (r : ℝ)
  have hsmall : Tendsto (fun n ↦ coefficient *
      (((κS n : Measure (A × A)) {p | p.1 ≠ p.2}).toReal +
       ((κT n : Measure (B × B)) {p | p.1 ≠ p.2}).toReal)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hdisagreement.const_mul coefficient
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ dist_nonneg) _ hsmall
  apply Filter.Eventually.of_forall
  intro n
  have hb := abs_legalMarkedPressure_projected_laws_sub_le q coarse hgap source target hs ht
    (κS n : Measure (A × A)) (κT n : Measure (B × B)) (hsource n) (hsep n) r hC hG
    kin hk hkb probe hp hpb t
  dsimp only at hb
  simpa only [ProbabilityMeasure.toMeasure_map,hmapS n,hmapT n,Real.dist_eq,coefficient] using hb

/-- The exact original law convergence holds at every fixed real spatial box,
including the zero normalization convention at nonpositive box sizes. -/
theorem tendsto_legalMarkedScalePressure_of_original_mark_couplings
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableEq A] [MeasurableEq B]
    (q : ℕ) {range : Set ℝ} {gap : ℝ} (coarse : FiniteScalarBins range gap) (hgap : 0 < gap)
    (source : A → ℝ) (target : B → ℝ) (hs : Measurable source) (ht : Measurable target)
    (κS : ℕ → ProbabilityMeasure (A × A)) (κT : ℕ → ProbabilityMeasure (B × B))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (hmapS : ∀ n, (κS n : Measure (A × A)).map Prod.snd = α)
    (hmapT : ∀ n, (κT n : Measure (B × B)).map Prod.snd = β)
    (hsource : ∀ n, ∀ᵐ a ∂(κS n : Measure (A × A)), source a.1 ∈ range ∧ source a.2 ∈ range)
    (hsep : ∀ n, ∀ᵐ p ∂(κS n : Measure (A × A)).prod (κT n : Measure (B × B)),
      gap ≤ |target p.2.1 - source p.1.1| ∧ gap ≤ |target p.2.2 - source p.1.2|)
    (hdisagreement : Tendsto (fun n ↦
      ((κS n : Measure (A × A)) {p | p.1 ≠ p.2}).toReal +
      ((κT n : Measure (B × B)) {p | p.1 ≠ p.2}).toReal) atTop (𝓝 0))
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (probe : A → B → ℝ) (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (L t : ℝ) :
    Tendsto (fun n ↦ legalMarkedScalePressure q source target
      ((κS n).map measurable_fst.aemeasurable : Measure A)
      ((κT n).map measurable_fst.aemeasurable : Measure B) kin probe L t) atTop
        (𝓝 (legalMarkedScalePressure q source target α β kin probe L t)) := by
  by_cases hL : 0 < L
  · have h := (tendsto_legalMarkedPressure_of_original_mark_couplings q coarse hgap source target
      hs ht κS κT α β hmapS hmapT hsource hsep hdisagreement (Real.toNNReal (L ^ q))
      hC hG kin hk hkb probe hp hpb t).div_const (L ^ q)
    change Tendsto (fun n ↦ legalMarkedPressure q source target
      ((κS n).map measurable_fst.aemeasurable : Measure A)
      ((κT n).map measurable_fst.aemeasurable : Measure B) (Real.toNNReal (L ^ q)) kin probe t / L ^ q)
      atTop (𝓝 (legalMarkedPressure q source target α β (Real.toNNReal (L ^ q)) kin probe t / L ^ q)) at h
    simpa only [legalMarkedScalePressure,hL,↓reduceIte] using h
  · simp only [legalMarkedScalePressure,hL,↓reduceIte]
    exact tendsto_const_nhds

end OTSelector.Reconstruction
