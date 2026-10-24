import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonOriginal

/-!
# Original Poisson source defects for legal spatial repair

Equal original Poisson color means identify the expected unused-source part of
color imbalance with half its absolute discrepancy. Together with the proved
original scalar-bin Hall bound, this yields an integrable source-only legal
matching defect of square-root order under the unchanged original marked cloud
law. The natural-number representation is also proved for finite repair.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

open OTSelector.Probability

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Equal original Poisson color means identify the expected unmatched source
count with half the absolute color imbalance. -/
theorem integral_sourceCount_sub_min_eq_half_abs (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) :
    (∫ ω : TwoMarkedCloudSpace q A B,
      (mSourceCount ω : ℝ) - ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
      ∂twoMarkedCloudLaw q A B α β r) =
      (1 / 2 : ℝ) * (∫ ω, |(mSourceCount ω : ℝ) - (mTargetCount ω : ℝ)|
        ∂twoMarkedCloudLaw q A B α β r) := by
  have hs := integrable_mSourceCount q α β r
  have ht := integrable_mTargetCount q α β r
  have hm := integrable_mMinCount q α β r
  have hpt : (fun ω : TwoMarkedCloudSpace q A B ↦
      |(mSourceCount ω : ℝ) - (mTargetCount ω : ℝ)|) = fun ω ↦
      (mSourceCount ω : ℝ) + (mTargetCount ω : ℝ) -
        2 * ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) := by
    funext ω
    exact abs_cast_sub_eq_cast_add_sub_two_mul_min _ _
  have hsum : Integrable (fun ω : TwoMarkedCloudSpace q A B ↦
      (mSourceCount ω : ℝ) + (mTargetCount ω : ℝ)) (twoMarkedCloudLaw q A B α β r) := hs.add ht
  rw [integral_sub hs hm, hpt, integral_sub hsum (hm.const_mul 2),
    integral_add hs ht, integral_const_mul, integral_mSourceCount_eq, integral_mTargetCount_eq]
  ring

/-- The expected unused-source part of the color imbalance has a square-root bound. -/
theorem integral_sourceCount_sub_min_le (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) :
    (∫ ω : TwoMarkedCloudSpace q A B,
      (mSourceCount ω : ℝ) - ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)
      ∂twoMarkedCloudLaw q A B α β r) ≤ (1 / 2 : ℝ) * Real.sqrt (2 * (r : ℝ)) := by
  rw [integral_sourceCount_sub_min_eq_half_abs q α β r]
  exact mul_le_mul_of_nonneg_left (integral_mAbsCountsSub_le q α β r) (by norm_num)

/-- The literal unmatched-source count of the actual forward legal maximum. -/
def legalMarkedSourceDefect (q : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (ω : TwoMarkedCloudSpace q A B) : ℝ :=
  (mSourceCount ω : ℝ) - legalMarkedMaximumCard q sourceClock targetClock ω

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- The real source defect is exactly the natural-number unmatched source count. -/
theorem legalMarkedSourceDefect_eq_nat (q : ℕ) (sourceClock : A → ℝ) (targetClock : B → ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    legalMarkedSourceDefect q sourceClock targetClock ω =
      ((mSourceCount ω - legalMarkedMaximumCard q sourceClock targetClock ω : ℕ) : ℝ) := by
  unfold legalMarkedSourceDefect legalMarkedMaximumCard
  rw [Nat.cast_sub ((PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _))]

/-- The actual original legal source defect is integrable. -/
theorem integrable_legalMarkedSourceDefect (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) :
    Integrable (legalMarkedSourceDefect q sourceClock targetClock)
      (twoMarkedCloudLaw q A B α β r) := by
  have hmeas : Measurable (legalMarkedSourceDefect q sourceClock targetClock) :=
    (measurable_from_nat.comp (measurable_mSourceCount q)).sub
      (measurable_legalMarkedMaximumCard_cast q hs ht)
  refine (integrable_mSourceCount q α β r).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with ω
  have hcard : (legalMarkedMaximumCard q sourceClock targetClock ω : ℝ) ≤
      (mSourceCount ω : ℝ) :=
    Nat.cast_le.mpr ((PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _))
  rw [Real.norm_eq_abs, legalMarkedSourceDefect, abs_of_nonneg (sub_nonneg.mpr hcard)]
  exact sub_le_self _ (Nat.cast_nonneg _)

/-- Min-cardinality Hall-defect control pays the source-only defect by the exact
original color imbalance term. -/
theorem integral_legalMarkedSourceDefect_le_of_minDefect (q : ℕ)
    {sourceClock : A → ℝ} {targetClock : B → ℝ}
    (hs : Measurable sourceClock) (ht : Measurable targetClock)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {C : ℝ}
    (hmin : (∫ ω, ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) -
      legalMarkedMaximumCard q sourceClock targetClock ω ∂twoMarkedCloudLaw q A B α β r) ≤ C) :
    (∫ ω, legalMarkedSourceDefect q sourceClock targetClock ω
      ∂twoMarkedCloudLaw q A B α β r) ≤ C + (1 / 2 : ℝ) * Real.sqrt (2 * (r : ℝ)) := by
  have hpt : legalMarkedSourceDefect q sourceClock targetClock = fun ω ↦
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ) -
        legalMarkedMaximumCard q sourceClock targetClock ω +
      ((mSourceCount ω : ℝ) - ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)) := by
    funext ω
    simp only [legalMarkedSourceDefect]
    ring
  have hdiff : Integrable (fun ω : TwoMarkedCloudSpace q A B ↦ (mSourceCount ω : ℝ) -
      ((min (mSourceCount ω) (mTargetCount ω) : ℕ) : ℝ)) (twoMarkedCloudLaw q A B α β r) :=
    (integrable_mSourceCount q α β r).sub (integrable_mMinCount q α β r)
  rw [hpt, integral_add (integrable_legalMarkedMaximumCard_defect q hs ht α β r) hdiff]
  exact add_le_add hmin (integral_sourceCount_sub_min_le q α β r)

/-- Scalar-bin populations produce the actual source-defect bound on the
unchanged original independent Poisson cloud, with no type count balance premise. -/
theorem scalarBinPopulationTypes_poisson_sourceDefect
    {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace J] [MeasurableSingletonClass J] [Fintype J]
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    [MeasurableSpace (Option (J × Fin D.count × Fin D.count))]
    [MeasurableSingletonClass (Option (J × Fin D.count × Fin D.count))]
    (chart : X × Y → J) (source : X → ℝ) (target : Y → ℝ)
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) (hchart : Measurable chart)
    (hs : Measurable source) (ht : Measurable target)
    (hI : ∀ᵐ p ∂π, source p.1 ∈ I ∧ target p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1) (q : ℕ) (r : ℝ≥0) :
    Integrable (legalMarkedSourceDefect q source target) (twoMarkedCloudLaw q X Y μ ν r) ∧
      (∫ ω, legalMarkedSourceDefect q source target ω ∂twoMarkedCloudLaw q X Y μ ν r) ≤
        Real.sqrt (2 * (r : ℝ) * Fintype.card (Option (J × Fin D.count × Fin D.count))) := by
  obtain ⟨-, hmin⟩ := scalarBinPopulationTypes_poisson_legalMaximumCard_defect D hδ chart
    source target π μ ν hπ hchart hs ht hI hgap q r
  have h := integral_legalMarkedSourceDefect_le_of_minDefect q hs ht μ ν r hmin
  refine ⟨integrable_legalMarkedSourceDefect q hs ht μ ν r, h.trans ?_⟩
  have hK : (1 : ℝ) ≤ (Fintype.card (Option (J × Fin D.count × Fin D.count)) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (show Nonempty (Option (J × Fin D.count × Fin D.count)) from ⟨none⟩)
  have hscale : Real.sqrt (2 * (r : ℝ)) ≤
      Real.sqrt (2 * (r : ℝ) * Fintype.card (Option (J × Fin D.count × Fin D.count))) :=
    Real.sqrt_le_sqrt (le_mul_of_one_le_right (by positivity) hK)
  linarith

end OTSelector.Reconstruction
