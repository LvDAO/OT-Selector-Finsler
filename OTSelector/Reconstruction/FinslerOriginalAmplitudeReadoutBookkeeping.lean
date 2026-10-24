import OTSelector.Topology.MetricSpace.ReadoutBallContainment
import OTSelector.Reconstruction.FinslerOriginalMomentumAmplitudeTail
import OTSelector.Reconstruction.FinslerOriginalCommonScaleLargeAmplitude

/-!
# Readout Lipschitz constant and amplitude radius bookkeeping

This file closes sub-gaps (i) and (iii) of
FinslerOriginalAmplitudeBallContainment.lean.

Sub-gap (i): the readout inverse-Lipschitz constant.  The chart readout of the
retained atlas window is locally bi-Lipschitz; the inverse direction needed for
the ball containment, dist x c <= C * ||readout x - readout c||, is extracted
from a Lipschitz bound on the inverse chart map that fixes the readout.  Both the
global and the on-window (LipschitzOnWith) forms are provided, together with the
composition into the frozen core entry ball containment
forall i, dist (X i) c <= C * Drad.

Sub-gap (iii): amplitude radius bookkeeping.  The bounded-amplitude radius PB is
the retained good event of the frozen core: the event
commonScaleAmplitudeBoundedEvent = {||field 0|| <= PB} is Borel, and -- under a
squared-norm moment budget -- its complement (the large-amplitude wall) has
measure at most K / PB^2 by the Chebyshev estimate of
FinslerOriginalMomentumAmplitudeTail.lean.  Finally every scene splits into three
bookkeeping branches: bounded amplitude (ball bounds apply with radius H), small
amplitude below the comparability threshold, or the large-amplitude branch, which
is contained in the retained canonical integer certificate set by
FinslerOriginalCommonScaleLargeAmplitude.largeCanonicalAmplitudeBranch_subset.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction

/-! ## Sub-gap (i): the readout inverse-Lipschitz constant -/

/-- **Readout inverse-Lipschitz constant.**  If the inverse chart map Psi is
L-Lipschitz and fixes the readout, then the manifold distance is bounded by the
readout difference with the constant L.  This is the inverse direction of the
chart smoothness (the chart inverse is locally Lipschitz on the retained
window); it is exactly the hypothesis hread of the ball containment. -/
theorem dist_le_of_leftInverse_lipschitz {M G : Type*} [PseudoMetricSpace M]
    [NormedAddCommGroup G] {Φ : M → G} {Ψ : G → M} {L : ℝ≥0}
    (hleft : ∀ x, Ψ (Φ x) = x) (hΨ : LipschitzWith L Ψ) (x x₀ : M) :
    dist x x₀ ≤ (L : ℝ) * ‖Φ x - Φ x₀‖ := by
  have h := hΨ.dist_le_mul (Φ x) (Φ x₀)
  rw [hleft x, hleft x₀] at h
  calc dist x x₀ ≤ (L : ℝ) * dist (Φ x) (Φ x₀) := h
    _ = (L : ℝ) * ‖Φ x - Φ x₀‖ := by rw [dist_eq_norm]

/-- **Readout inverse-Lipschitz constant on the retained window.**  Only the
window points of the chart target are used, so the Lipschitz constant of the
inverse chart map is required only on the retained chart set. -/
theorem dist_le_of_leftInverse_lipschitzOn {M G : Type*} [PseudoMetricSpace M]
    [NormedAddCommGroup G] {Φ : M → G} {Ψ : G → M} {L : ℝ≥0} {s : Set G}
    (hleft : ∀ x, Φ x ∈ s → Ψ (Φ x) = x)
    (hΨ : LipschitzOnWith L Ψ s) {x x₀ : M} (hx : Φ x ∈ s) (hx₀ : Φ x₀ ∈ s) :
    dist x x₀ ≤ (L : ℝ) * ‖Φ x - Φ x₀‖ := by
  have h := hΨ.dist_le_mul (Φ x) hx (Φ x₀) hx₀
  rw [hleft x hx, hleft x₀ hx₀] at h
  calc dist x x₀ ≤ (L : ℝ) * dist (Φ x) (Φ x₀) := h
    _ = (L : ℝ) * ‖Φ x - Φ x₀‖ := by rw [dist_eq_norm]

/-- **Frozen core entry ball containment from the readout constant.**  With the
readout inverse-Lipschitz constant L and the chart amplitude bound Drad, every
retained source or target lies in the metric ball of explicit radius L * Drad.
This is the ball containment of FinslerOriginalFrozenCoreEntryBound.lean with the
readout constant now explicit. -/
theorem frozenCoreEntry_ballContainment_of_readout_lipschitz {ι M G : Type*}
    [PseudoMetricSpace M] [NormedAddCommGroup G] {X : ι → M} {Φ : M → G}
    {Ψ : G → M} {c : M} {L : ℝ≥0} {Drad : ℝ}
    (hleft : ∀ x, Ψ (Φ x) = x) (hΨ : LipschitzWith L Ψ)
    (hamp : ∀ i, ‖Φ (X i) - Φ c‖ ≤ Drad) :
    ∀ i, dist (X i) c ≤ (L : ℝ) * Drad := by
  intro i
  exact (dist_le_of_leftInverse_lipschitz hleft hΨ (X i) c).trans
    (mul_le_mul_of_nonneg_left (hamp i) (NNReal.coe_nonneg L))

/-- **Real amplitude split.**  Every real amplitude is either below the
bounded-amplitude radius, or above it while respecting the comparability
threshold, or below the comparability threshold.  This is the elementary
bookkeeping behind the three-branch amplitude cover. -/
theorem real_three_way_cover (z H c : ℝ) : z ≤ H ∨ (H < z ∧ c ≤ z) ∨ z < c := by
  by_cases hz : z ≤ H
  · exact Or.inl hz
  · have hz' : H < z := not_le.mp hz
    by_cases hc : c ≤ z
    · exact Or.inr (Or.inl ⟨hz', hc⟩)
    · exact Or.inr (Or.inr (not_le.mp hc))

/-! ## Sub-gap (iii): amplitude radius bookkeeping -/

namespace OriginalSeedConditionalMoments

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- **The bounded-amplitude (retained good) event.**  The event on which the
normalized momentum phase field at the base clock is bounded by the amplitude
radius PB.  This is the retained good event of the frozen core: on it the
amplitude-ball radii of FinslerOriginalAmplitudeBallContainment.lean apply with
radius PB. -/
def commonScaleAmplitudeBoundedEvent
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (cut h : ℝ) (L : ℝ≥0) (PB : ℝ) :
    Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :=
  {s | ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ PB}

/-- The bounded-amplitude retained event is Borel. -/
theorem measurableSet_commonScaleAmplitudeBoundedEvent
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0) (PB : ℝ) :
    MeasurableSet (D.commonScaleAmplitudeBoundedEvent T cut h L PB) := by
  unfold commonScaleAmplitudeBoundedEvent
  apply measurableSet_le
  · exact (D.measurable_normalizedMomentumPhaseField_at_zero hF hw T hcut h L).norm
  · exact measurable_const

/-- **Amplitude wall bookkeeping.**  The complement of the retained bounded
amplitude event is the large-amplitude wall, and its measure is controlled by the
Chebyshev estimate: under a squared-norm moment budget K it has measure at most
K / PB^2.  This is the probability bookkeeping matching the retained good event
to the amplitude-tail modules. -/
theorem commonScaleAmplitudeBoundedEvent_compl_measureReal_le
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0) {PB : ℝ}
    (Pscene : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    [IsFiniteMeasure Pscene] {K : ℝ} (hPB : 0 < PB) (hK : 0 ≤ K)
    (hmom : ∫⁻ s, ENNReal.ofReal
        (‖D.normalizedMomentumPhaseField T cut h L s 0‖ ^ 2) ∂Pscene ≤
      ENNReal.ofReal K) :
    Pscene.real ((D.commonScaleAmplitudeBoundedEvent T cut h L PB)ᶜ) ≤ K / PB ^ 2 := by
  have hset : (D.commonScaleAmplitudeBoundedEvent T cut h L PB)ᶜ =
      {s | PB < ‖D.normalizedMomentumPhaseField T cut h L s 0‖} := by
    ext s
    simp only [commonScaleAmplitudeBoundedEvent, Set.mem_compl_iff, Set.mem_ofPred_eq,
      not_le]
  rw [hset]
  exact measureReal_norm_gt_le_of_lintegral_sq_le Pscene
    (D.measurable_normalizedMomentumPhaseField_at_zero hF hw T hcut h L) hPB hK hmom

/-- **Three-branch amplitude cover with the retained certificate.**  Every scene
is in one of three bookkeeping branches: (a) amplitude bounded by H, so the
frozen-core ball bounds apply with radius H; (b) amplitude below the
comparability threshold 2 (L a + b); or (c) the large-amplitude branch, which is
contained in the retained canonical integer certificate set.  This is the
requested match between the bounded-amplitude radius and the retention event. -/
theorem amplitude_cover_retained_certificate
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T] {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    (ρ A : ℝ) {a b H : ℝ} {N : ℕ} (hH : 1 ≤ H) (hN : 1 ≤ N)
    (hNH : (N : ℝ) ≤ canonicalPhaseCurveScaleCoefficient (L : ℝ) ρ A * H)
    (s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤ H ∨
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖ < 2 * ((L : ℝ) * a + b) ∨
      ((N : ℝ) ≤ (D.normalizedCanonicalCurveIntegerScale T cut h L ρ A s : ℝ) ∧
        1 ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
          2 * ((L : ℝ) * a + b) ≤
            ‖D.normalizedMomentumPhaseField T cut h L s 0‖) := by
  rcases real_three_way_cover (‖D.normalizedMomentumPhaseField T cut h L s 0‖) H
      (2 * ((L : ℝ) * a + b)) with h1 | ⟨h2, h3⟩ | h4
  · exact Or.inl h1
  · exact Or.inr (Or.inr
      (D.largeCanonicalAmplitudeBranch_subset hF hw T hcut h L ρ A hH hN hNH ⟨h2, h3⟩))
  · exact Or.inr (Or.inl h4)

/-- **Retained good event implies the bounded amplitude radius.**  On the
complement of the large-amplitude branch the amplitude is bounded by the maximum
of the truncation level H and the comparability threshold, so the retained good
event carries the explicit amplitude radius
PB = max H (2 (L a + b)).  This is the quantitative form of sub-gap (iii). -/
theorem retained_amplitude_le_max
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {cut h : ℝ} {L : ℝ≥0} {a b H : ℝ}
    {s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)}
    (hnot : s ∉ {s | H < ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ∧
      2 * ((L : ℝ) * a + b) ≤ ‖D.normalizedMomentumPhaseField T cut h L s 0‖}) :
    ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤
      max H (2 * ((L : ℝ) * a + b)) := by
  have hcover := real_three_way_cover (‖D.normalizedMomentumPhaseField T cut h L s 0‖) H
    (2 * ((L : ℝ) * a + b))
  rcases hcover with h1 | ⟨h2, h3⟩ | h4
  · exact h1.trans (le_max_left _ _)
  · exact absurd ⟨h2, h3⟩ hnot
  · exact h4.le.trans (le_max_right _ _)

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
