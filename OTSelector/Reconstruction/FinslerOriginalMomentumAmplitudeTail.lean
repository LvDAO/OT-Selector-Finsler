import OTSelector.Reconstruction.FinslerOriginalCommonScaleWholePathProbability

/-!
# Amplitude moment and tail estimates for the normalized momentum field

The whole-path L2 probability lane keeps the two amplitude walls of the
common-scale counting event as explicit probability terms. This file controls
them by the standard second-moment (Chebyshev/Markov) estimate: the probability
that a measurable field exceeds a threshold is bounded by its squared-norm
integral divided by the squared threshold.

Three layers are provided.

* A general `L²` amplitude tail estimate for a measurable field: a squared-norm
  `lintegral` budget `K` bounds the measure of every large-amplitude set by
  `K / t²`, and hence every multiplicative wall `{1 < c * ‖F‖}` by `K * c²`.
* A moment budget from an almost-sure amplitude bound: an amplitude budget `H`
  gives the squared-norm `lintegral` budget `H²` on a probability scene law.
* The concrete instantiation for the actual original minimizer's normalized
  momentum field: the two amplitude walls of `commonScaleCountBadEvent` are
  bounded by the explicit moment terms, and the whole bad-event probability is
  bounded by the exact normalized phase-walk exponential tail plus those terms.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-! ## The general squared-norm amplitude tail estimate -/

/-- **Chebyshev amplitude tail.** A squared-norm `lintegral` budget `K` bounds
the probability that a measurable norm exceeds any positive threshold `t` by
`K / t²`. -/
theorem measureReal_norm_gt_le_of_lintegral_sq_le
    {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → V} (hf : Measurable f) {K t : ℝ} (ht : 0 < t) (hK : 0 ≤ K)
    (hmom : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≤ ENNReal.ofReal K) :
    μ.real {x | t < ‖f x‖} ≤ K / t ^ 2 := by
  set A : Set α := {x | t < ‖f x‖} with hAdef
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const (continuous_norm.measurable.comp hf)
  have hpoint : ∀ x ∈ A, t ^ 2 ≤ ‖f x‖ ^ 2 := by
    intro x hx
    have hx' : t < ‖f x‖ := hx
    nlinarith [ht, norm_nonneg (f x)]
  have hstep : ∫⁻ x in A, ENNReal.ofReal (t ^ 2) ∂μ ≤
      ∫⁻ x in A, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hA] with x hx
    exact ENNReal.ofReal_le_ofReal (hpoint x hx)
  have hconst : ∫⁻ x in A, ENNReal.ofReal (t ^ 2) ∂μ = ENNReal.ofReal (t ^ 2) * μ A := by
    rw [lintegral_const, Measure.restrict_apply_univ]
  have hle : ∫⁻ x in A, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  have hmain : ENNReal.ofReal (t ^ 2) * μ A ≤ ENNReal.ofReal K := by
    rw [← hconst]
    exact hstep.trans (hle.trans hmom)
  have hfin : (μ A).toReal * t ^ 2 ≤ K := by
    have htoReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal hK, mul_comm] at htoReal
  rw [measureReal_def]
  rw [le_div_iff₀ (by positivity)]
  linarith [hfin]

/-- **Multiplicative amplitude wall.** For a positive scale `c`, the wall
`{1 < c * ‖f‖}` has measure at most `K * c²` under the squared-norm budget `K`. -/
theorem measureReal_one_lt_mul_norm_le_of_lintegral_sq_le
    {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → V} (hf : Measurable f) {K c : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hmom : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≤ ENNReal.ofReal K) :
    μ.real {x | 1 < c * ‖f x‖} ≤ K * c ^ 2 := by
  have hset : {x | 1 < c * ‖f x‖} = {x | 1 / c < ‖f x‖} := by
    ext x
    change (1 < c * ‖f x‖) ↔ (1 / c < ‖f x‖)
    rw [div_lt_iff₀ hc, mul_comm c (‖f x‖)]
  rw [hset]
  have h := measureReal_norm_gt_le_of_lintegral_sq_le μ hf (t := 1 / c)
    (by positivity) hK hmom
  calc μ.real {x | 1 / c < ‖f x‖} ≤ K / (1 / c) ^ 2 := h
    _ = K * c ^ 2 := by
        field_simp

/-- **Moment budget from an almost-sure amplitude bound.** On a probability
scene law, an almost-sure amplitude bound `H` gives the squared-norm
`lintegral` budget `H²`. -/
theorem lintegral_sq_le_of_ae_norm_le
    {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → V} {H : ℝ} (hH : 0 ≤ H) (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ H) :
    ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≤ ENNReal.ofReal (H ^ 2) := by
  have hmono : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≤
      ∫⁻ _x, ENNReal.ofReal (H ^ 2) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hf] with x hx
    apply ENNReal.ofReal_le_ofReal
    nlinarith [norm_nonneg (f x)]
  rwa [lintegral_const, measure_univ, mul_one] at hmono

/-! ## The actual normalized momentum field -/

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual normalized momentum field read at the origin of physical coordinates
is measurable in the original scene. -/
theorem measurable_normalizedMomentumPhaseField_at_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0) :
    Measurable (fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
      D.normalizedMomentumPhaseField T cut h L s 0) :=
  (D.measurable_normalizedMomentumPhaseField hF hw T hcut h L).comp
    (measurable_id.prodMk measurable_const)

/-- **Source amplitude wall.** Under the squared-norm moment budget of the actual
normalized momentum field, the first amplitude wall of the common-scale counting
event has measure at most `K * (2 * (rho + 1))²`. -/
theorem commonScale_amplitudeWall_source_measureReal_le
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    {ρ K : ℝ} (hρ : 0 ≤ ρ) (hK : 0 ≤ K)
    (hmom : ∫⁻ s, ENNReal.ofReal
        (‖D.normalizedMomentumPhaseField T cut h L s 0‖ ^ 2)
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
        ≤ ENNReal.ofReal K) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
        {s | 1 < 2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖} ≤
      K * (2 * (ρ + 1)) ^ 2 :=
  measureReal_one_lt_mul_norm_le_of_lintegral_sq_le
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    (D.measurable_normalizedMomentumPhaseField_at_zero hF hw T hcut h L)
    (by linarith) hK hmom

/-- **Target amplitude wall.** Under the squared-norm moment budget of the actual
normalized momentum field and a positive Lipschitz scale, the second amplitude
wall of the common-scale counting event has measure at most
`K * (4 * (1 + L) * A)²`. -/
theorem commonScale_amplitudeWall_target_measureReal_le
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    {A K : ℝ} (hA : 0 < A) (hK : 0 ≤ K)
    (hmom : ∫⁻ s, ENNReal.ofReal
        (‖D.normalizedMomentumPhaseField T cut h L s 0‖ ^ 2)
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
        ≤ ENNReal.ofReal K) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
        {s | 1 < 4 * (1 + (L : ℝ)) * A *
          ‖D.normalizedMomentumPhaseField T cut h L s 0‖} ≤
      K * (4 * (1 + (L : ℝ)) * A) ^ 2 :=
  measureReal_one_lt_mul_norm_le_of_lintegral_sq_le
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    (D.measurable_normalizedMomentumPhaseField_at_zero hF hw T hcut h L)
    (by positivity) hK hmom

/-- **Both amplitude walls from one moment budget.** The sum of the two amplitude
wall measures of the common-scale counting event is bounded by the two explicit
moment terms. -/
theorem commonScale_amplitudeWalls_measureReal_le
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    {ρ A K : ℝ} (hρ : 0 ≤ ρ) (hA : 0 < A) (hK : 0 ≤ K)
    (hmom : ∫⁻ s, ENNReal.ofReal
        (‖D.normalizedMomentumPhaseField T cut h L s 0‖ ^ 2)
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
        ≤ ENNReal.ofReal K) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
        {s | 1 < 2 * (ρ + 1) * ‖D.normalizedMomentumPhaseField T cut h L s 0‖} +
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
        {s | 1 < 4 * (1 + (L : ℝ)) * A *
          ‖D.normalizedMomentumPhaseField T cut h L s 0‖} ≤
      K * (2 * (ρ + 1)) ^ 2 + K * (4 * (1 + (L : ℝ)) * A) ^ 2 :=
  add_le_add
    (D.commonScale_amplitudeWall_source_measureReal_le hF hw T Q hcut h L hρ hK hmom)
    (D.commonScale_amplitudeWall_target_measureReal_le hF hw T Q hcut h L hA hK hmom)

/-- **The whole bad-event probability with moment-controlled amplitude walls.**
The exact normalized phase-walk exponential tail plus the two explicit
Chebyshev moment terms. -/
theorem commonScaleCountBadEvent_measure_real_le_of_moment
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (ρ A radius K : ℝ) (hρ : 0 ≤ ρ) (hA : 0 < A) {Kmom : ℝ} (hKmom : 0 ≤ Kmom)
    (hmom : ∫⁻ s, ENNReal.ofReal
        (‖D.normalizedMomentumPhaseField T cut h L s 0‖ ^ 2)
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
        ≤ ENNReal.ofReal Kmom) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
        (D.commonScaleCountBadEvent T cut h L ρ A radius K) ≤
      Real.exp (-(K - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
          (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) -
          2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
            (D.normalizedSourcePhaseCell T cut 0 0 (radius + 2))).toReal *
            (Real.exp 1 - 1))) +
        Kmom * (2 * (ρ + 1)) ^ 2 + Kmom * (4 * (1 + (L : ℝ)) * A) ^ 2 := by
  have hbad := D.commonScaleCountBadEvent_measure_real_le hF hw T hcut h L ρ A radius K Q
  have hwalls := D.commonScale_amplitudeWalls_measureReal_le hF hw T Q hcut h L hρ hA hKmom hmom
  linarith [hbad, hwalls]

/-- **The whole bad-event probability from an almost-sure amplitude budget.**
An amplitude budget `H` gives the squared-norm moment budget `H²`, hence the
two amplitude-wall probabilities are bounded by `H² * c²` and the entire bad
event is bounded by the exact exponential tail plus those explicit terms. -/
theorem commonScaleCountBadEvent_measure_real_le_of_amplitude
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (ρ A radius Kbad : ℝ) (hρ : 0 ≤ ρ) (hA : 0 < A)
    {H : ℝ} (hH : 0 ≤ H)
    (hamp : ∀ᵐ s ∂(Q.law : Measure
        (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).real
        (D.commonScaleCountBadEvent T cut h L ρ A radius Kbad) ≤
      Real.exp (-(Kbad - (3 * (2 * finrank ℝ S.covector.ker : ℝ) +
          (3 : ℝ) ^ (2 * finrank ℝ S.covector.ker)) -
          2 * (((volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)).prod μ)
            (D.normalizedSourcePhaseCell T cut 0 0 (radius + 2))).toReal *
            (Real.exp 1 - 1))) +
        H ^ 2 * (2 * (ρ + 1)) ^ 2 + H ^ 2 * (4 * (1 + (L : ℝ)) * A) ^ 2 := by
  have hmom : ∫⁻ s, ENNReal.ofReal
      (‖D.normalizedMomentumPhaseField T cut h L s 0‖ ^ 2)
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
      ≤ ENNReal.ofReal (H ^ 2) :=
    lintegral_sq_le_of_ae_norm_le
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
      hH hamp
  exact D.commonScaleCountBadEvent_measure_real_le_of_moment hF hw T Q hcut h L ρ A radius
    Kbad hρ hA (sq_nonneg H) hmom

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
