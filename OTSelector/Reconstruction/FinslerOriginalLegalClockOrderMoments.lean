import OTSelector.Reconstruction.FinslerOriginalAbstractCarrierConstruction
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryTightCut

/-!
# Clock order and clock-difference moments for the recoded legal Palm

`FinslerOriginalAbstractCarrierConstruction` constructs the abstract
`StationaryForwardMatching` carrier from the recoded legal Palm, assuming
* almost-sure clock order `p.1.1 < p.2.1`, and
* a finite, bounded clock-difference second moment `∫ (b - a)^2`.

Both are derived here for the actual legal stationary Poisson matching:

* `ae_carrierRecodedLegalPalm_forward`: strict clock order almost surely on the
  recoded legal Palm, transferred from
  `LegalWeightedStationaryPoissonMatching.ae_palm_forward` along the measurable
  recoding.
* `integrable_clockDiff_sq_legalPalm`: the clock-difference square is integrable
  on the legal Palm as soon as the two original clock marginals `α`, `β` have
  finite second moments, using the pointwise bound `(b - a)^2 ≤ 2a^2 + 2b^2`.
* `integral_clockDiff_sq_le`: its integral is at most
  `2 ∫ t^2 dα + 2 ∫ t^2 dβ`.
* `integrable_edgeDisplacement_sq_carrierRecodedLegalPalm` and the integral
  formula transfer both statements to the recoded abstract Palm.
* `nonempty_boundedSecondMomentClass_legal_unconditional`: composing with the
  carrier construction gives a genuinely nonempty abstract bounded second-moment
  class for the recoded legal Palm, with no remaining interface hypothesis beyond
  the finite clock second moments of `α` and `β`.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology
  OTSelector.PointProcess OTSelector.Probability
open scoped Topology ENNReal BigOperators

noncomputable section

namespace OTSelector.Reconstruction

open OTSelector.PointProcess
open OTSelector.PointProcess.StationaryForwardMatching

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-! ## Clock order on the recoded legal Palm -/

/-- Strict clock order holds almost surely on the recoded legal Palm. -/
theorem ae_carrierRecodedLegalPalm_forward
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∀ᵐ p ∂carrierRecodedLegalPalm Q, p.1.1 < p.2.1 := by
  have hmeas : MeasurableSet
      {p : MarkedCloudPoint × MarkedCloudPoint | p.1.1 < p.2.1} :=
    measurableSet_lt (measurable_fst.comp measurable_fst)
      (measurable_fst.comp measurable_snd)
  rw [carrierRecodedLegalPalm,
    ae_map_iff measurable_carrierRecodePair.aemeasurable hmeas]
  filter_upwards [Q.ae_palm_forward] with m hm
  exact hm

/-! ## Clock squares and the clock-difference second moment -/

/-- Generalized form of the first-clock-square integral, with the dependence on the
clock marginal separated from the matching datum. -/
theorem integral_fstClock_sq_aux
    (μ : Measure (PhysicalPairPalmMark (Fin q)))
    (hμ : μ.map (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) = α) :
    ∫ m : PhysicalPairPalmMark (Fin q), m.1.1 ^ 2 ∂μ = ∫ t : ℝ, t ^ 2 ∂α := by
  rw [← hμ]
  exact (integral_map (measurable_fst.comp measurable_fst).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun t : ℝ ↦ t ^ 2)
      (Measure.map (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) μ))).symm

theorem integral_sndClock_sq_aux
    (μ : Measure (PhysicalPairPalmMark (Fin q)))
    (hμ : μ.map (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.2) = β) :
    ∫ m : PhysicalPairPalmMark (Fin q), m.1.2 ^ 2 ∂μ = ∫ t : ℝ, t ^ 2 ∂β := by
  rw [← hμ]
  exact (integral_map (measurable_snd.comp measurable_fst).aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun t : ℝ ↦ t ^ 2)
      (Measure.map (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.2) μ))).symm

theorem integral_fstClock_sq_legalPalm
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∫ m : PhysicalPairPalmMark (Fin q), m.1.1 ^ 2 ∂(legalMarkedJointPalm q Q.law) =
      ∫ t : ℝ, t ^ 2 ∂α :=
  integral_fstClock_sq_aux (legalMarkedJointPalm q Q.law) Q.source_clock

theorem integral_sndClock_sq_legalPalm
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∫ m : PhysicalPairPalmMark (Fin q), m.1.2 ^ 2 ∂(legalMarkedJointPalm q Q.law) =
      ∫ t : ℝ, t ^ 2 ∂β :=
  integral_sndClock_sq_aux (legalMarkedJointPalm q Q.law) Q.target_clock

theorem integrable_clock_sq_aux
    (μ : Measure (PhysicalPairPalmMark (Fin q)))
    (hμ : μ.map (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1) = α)
    (hα2 : Integrable (fun t : ℝ ↦ t ^ 2) α) :
    Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1 ^ 2) μ := by
  have h := (integrable_map_measure (μ := μ)
    (f := fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1)
    (g := fun t : ℝ ↦ t ^ 2) (by fun_prop)
    (measurable_fst.comp measurable_fst).aemeasurable)
  rw [hμ] at h
  simpa only [Function.comp_def] using h.mp hα2

theorem integrable_sndClock_sq_aux
    (μ : Measure (PhysicalPairPalmMark (Fin q)))
    (hμ : μ.map (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.2) = β)
    (hβ2 : Integrable (fun t : ℝ ↦ t ^ 2) β) :
    Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.2 ^ 2) μ := by
  have h := (integrable_map_measure (μ := μ)
    (f := fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.2)
    (g := fun t : ℝ ↦ t ^ 2) (by fun_prop)
    (measurable_snd.comp measurable_fst).aemeasurable)
  rw [hμ] at h
  simpa only [Function.comp_def] using h.mp hβ2

theorem integrable_clock_sq_legalPalm
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hα2 : Integrable (fun t : ℝ ↦ t ^ 2) α)
    (hβ2 : Integrable (fun t : ℝ ↦ t ^ 2) β) :
    Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.1 ^ 2)
      (legalMarkedJointPalm q Q.law) ∧
    Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦ m.1.2 ^ 2)
      (legalMarkedJointPalm q Q.law) :=
  ⟨integrable_clock_sq_aux _ Q.source_clock hα2,
    integrable_sndClock_sq_aux _ Q.target_clock hβ2⟩

/-- The clock-difference square is integrable on the legal Palm. -/
theorem integrable_clockDiff_sq_legalPalm
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hα2 : Integrable (fun t : ℝ ↦ t ^ 2) α)
    (hβ2 : Integrable (fun t : ℝ ↦ t ^ 2) β) :
    Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦ (m.1.2 - m.1.1) ^ 2)
      (legalMarkedJointPalm q Q.law) := by
  obtain ⟨hsrc, htgt⟩ := integrable_clock_sq_legalPalm Q hα2 hβ2
  have hInt : Integrable
      (fun m : PhysicalPairPalmMark (Fin q) ↦ 2 * m.1.1 ^ 2 + 2 * m.1.2 ^ 2)
      (legalMarkedJointPalm q Q.law) :=
    (hsrc.const_mul 2).add (htgt.const_mul 2)
  refine hInt.mono' ?_ ?_
  · exact (by fun_prop : Measurable
      (fun m : PhysicalPairPalmMark (Fin q) ↦ (m.1.2 - m.1.1) ^ 2)).aestronglyMeasurable
  · filter_upwards with m
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (m.1.1 + m.1.2)]

theorem integral_clockDiff_sq_le
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hα2 : Integrable (fun t : ℝ ↦ t ^ 2) α)
    (hβ2 : Integrable (fun t : ℝ ↦ t ^ 2) β) :
    ∫ m : PhysicalPairPalmMark (Fin q), (m.1.2 - m.1.1) ^ 2
        ∂(legalMarkedJointPalm q Q.law) ≤
      2 * (∫ t : ℝ, t ^ 2 ∂α) + 2 * (∫ t : ℝ, t ^ 2 ∂β) := by
  obtain ⟨hsrc, htgt⟩ := integrable_clock_sq_legalPalm Q hα2 hβ2
  have hInt : Integrable
      (fun m : PhysicalPairPalmMark (Fin q) ↦ 2 * m.1.1 ^ 2 + 2 * m.1.2 ^ 2)
      (legalMarkedJointPalm q Q.law) :=
    (hsrc.const_mul 2).add (htgt.const_mul 2)
  have hdiff := integrable_clockDiff_sq_legalPalm Q hα2 hβ2
  have hmono : ∫ m : PhysicalPairPalmMark (Fin q), (m.1.2 - m.1.1) ^ 2
      ∂(legalMarkedJointPalm q Q.law) ≤
      ∫ m : PhysicalPairPalmMark (Fin q), 2 * m.1.1 ^ 2 + 2 * m.1.2 ^ 2
        ∂(legalMarkedJointPalm q Q.law) :=
    integral_mono hdiff hInt (fun m ↦ by nlinarith [sq_nonneg (m.1.1 + m.1.2)])
  have hcalc : ∫ m : PhysicalPairPalmMark (Fin q), 2 * m.1.1 ^ 2 + 2 * m.1.2 ^ 2
      ∂(legalMarkedJointPalm q Q.law) =
      2 * (∫ t : ℝ, t ^ 2 ∂α) + 2 * (∫ t : ℝ, t ^ 2 ∂β) := by
    rw [integral_add (hsrc.const_mul 2) (htgt.const_mul 2),
      integral_const_mul, integral_const_mul, integral_fstClock_sq_legalPalm Q,
      integral_sndClock_sq_legalPalm Q]
  linarith [hmono, hcalc]

/-! ## Transfer to the recoded abstract Palm -/

/-- Measurability of the abstract displacement square. -/
theorem measurable_edgeDisplacement_sq :
    Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ edgeDisplacement p ^ 2) := by
  unfold edgeDisplacement
  exact ((measurable_fst.comp measurable_snd).sub
    (measurable_fst.comp measurable_fst)).pow_const 2

theorem integrable_edgeDisplacement_sq_carrierRecodedLegalPalm
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hα2 : Integrable (fun t : ℝ ↦ t ^ 2) α)
    (hβ2 : Integrable (fun t : ℝ ↦ t ^ 2) β) :
    Integrable (fun p : MarkedCloudPoint × MarkedCloudPoint ↦ edgeDisplacement p ^ 2)
      (carrierRecodedLegalPalm Q) := by
  have hdiff := integrable_clockDiff_sq_legalPalm Q hα2 hβ2
  have hcomp : Integrable
      ((fun p : MarkedCloudPoint × MarkedCloudPoint ↦ edgeDisplacement p ^ 2)
        ∘ carrierRecodePair) (legalMarkedJointPalm q Q.law) := by
    refine hdiff.congr ?_
    filter_upwards with m
    simp only [Function.comp_apply, edgeDisplacement_carrierRecodePair]
  rw [carrierRecodedLegalPalm]
  exact (integrable_map_measure measurable_edgeDisplacement_sq.aestronglyMeasurable
    measurable_carrierRecodePair.aemeasurable).mpr hcomp

theorem integral_edgeDisplacement_sq_carrierRecodedLegalPalm
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∫ p : MarkedCloudPoint × MarkedCloudPoint, edgeDisplacement p ^ 2
        ∂(carrierRecodedLegalPalm Q) =
      ∫ m : PhysicalPairPalmMark (Fin q), (m.1.2 - m.1.1) ^ 2
        ∂(legalMarkedJointPalm q Q.law) := by
  rw [carrierRecodedLegalPalm,
    integral_map measurable_carrierRecodePair.aemeasurable
      measurable_edgeDisplacement_sq.aestronglyMeasurable]
  simp only [edgeDisplacement_carrierRecodePair]

/-! ## Unconditional nonemptiness of the abstract bounded class -/

theorem nonempty_boundedSecondMomentClass_legal_unconditional
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hα2 : Integrable (fun t : ℝ ↦ t ^ 2) α)
    (hβ2 : Integrable (fun t : ℝ ↦ t ^ 2) β) :
    ∃ B : ℝ,
      (boundedSecondMomentClass
        (α := (legalMarkedJointPalm q Q.law).map carrierRecodePair |>.map
          (fun p ↦ p.1.2))
        (β := (legalMarkedJointPalm q Q.law).map carrierRecodePair |>.map
          (fun p ↦ p.2.2)) B).Nonempty := by
  refine ⟨∫ p : MarkedCloudPoint × MarkedCloudPoint, edgeDisplacement p ^ 2
    ∂(carrierRecodedLegalPalm Q), ?_⟩
  exact nonempty_boundedSecondMomentClass_carrierRecodedLegalPalm Q
    (ae_carrierRecodedLegalPalm_forward Q)
    (integrable_edgeDisplacement_sq_carrierRecodedLegalPalm Q hα2 hβ2) le_rfl

end OTSelector.Reconstruction

end
