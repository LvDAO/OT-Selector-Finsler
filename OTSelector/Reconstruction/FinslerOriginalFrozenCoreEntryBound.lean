import OTSelector.Reconstruction.FinslerFrozenCoreDomination
import OTSelector.Reconstruction.FinslerOriginalOffBadDomination

/-!
# Good-event per-edge bound for the concrete frozen core matrix

This file closes the remaining input of FinslerOriginalOffBadDomination.lean: the
per-edge bound E i j <= K for the concrete frozen core matrix
frozenCoreMatrix C eps z0 X Y k t h.

The proof has two geometric inputs, both already available:

* the clipped pointwise domination frozenCoreMatrix_le_slack_add_probeBound of
  FinslerFrozenCoreDomination.lean, which bounds the frozen core matrix on the
  retained Taylor mask by the physical tilted edge cost plus the probe constant:
  E i j <= k * slack i j + t * g i j + |t| * Bg;
* the amplitude event, in its metric form: on the bounded-amplitude event all
  sources and targets lie in a ball of radius Drad.  Then the distance slack of
  a one-Lipschitz potential is at most twice the radius,
  slack i j <= 4 * Drad, and the probe term is bounded by |t| * Bg.

Together they give the per-edge bound with kinetic-class constant
K = k * (4 * Drad) + 2 * (|t| * Bg): off the bad event the frozen physical cost
and the probes are bounded by the amplitude of the event, exactly the kinetic
class constant of the good event.  Composing with
fractionalAssignmentCost_div_le_of_entryBound and with the masked-cost
definition yields the normalized frozen-core cost bound
frozenCoreCost / n <= K on the good event, which is the form consumed by the
off-bad domination bridge.

The constant Bg bounds the physical probe and dominates the model-probe error;
Drad is the amplitude-event radius.  No compactness or properness of the
manifold metric is needed: the ball containment is the amplitude-event content.
-/
open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-! ## The amplitude event in metric form: bounded ball implies bounded slack -/

/-- **Bounded amplitude gives bounded distance slack.**  If all sources and
targets of a sample lie in the ball of radius Drad around a center, then the
one-Lipschitz slack cost of every pair is at most 4 * Drad.  This is the metric
form of the good/amplitude event used for the frozen core. -/
theorem distanceSlackEdgeCost_le_two_ball {n : ℕ} [PseudoMetricSpace M]
    {X Y : Fin n → M} {φ : M → ℝ} (hφ : LipschitzWith 1 φ) {c : M} {Drad : ℝ}
    (hX : ∀ i, dist (X i) c ≤ Drad) (hY : ∀ j, dist (Y j) c ≤ Drad) (i j : Fin n) :
    distanceSlackEdgeCost X Y φ i j ≤ 4 * Drad := by
  have hd : dist (X i) (Y j) ≤ 2 * Drad := by
    calc dist (X i) (Y j) ≤ dist (X i) c + dist c (Y j) := dist_triangle _ _ _
      _ ≤ Drad + Drad :=
          add_le_add (hX i) (by simpa only [dist_comm] using hY j)
      _ = 2 * Drad := by ring
  have hp : φ (X i) - φ (Y j) ≤ dist (X i) (Y j) := by
    have h := hφ.dist_le_mul (X i) (Y j)
    rw [NNReal.coe_one, one_mul, Real.dist_eq] at h
    exact (abs_le.mp h).2
  unfold distanceSlackEdgeCost
  linarith

/-! ## The per-edge bound for the frozen core matrix -/

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instFrozenCoreEntryMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- **Good-event per-edge bound for the concrete frozen core matrix.**

On the retained Taylor mask Q, with a radius-Drad ball containing all sources and
targets (the amplitude event), the frozen core matrix is bounded by the
kinetic-class constant k * (4 * Drad) + 2 * (|t| * Bg).  The physical probe g is
bounded by Bg and the model-probe error is at most Bg. -/
theorem frozenCoreMatrix_le_of_ball {n : ℕ} [PseudoMetricSpace M]
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (Dm : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {X Y : Fin n → M} {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    (hφ : LipschitzWith 1 φ)
    {k t probeError Bg : ℝ} (hk : 0 ≤ k)
    {z₀ : Fin n → Fin n → Z} {h g : Matrix (Fin n) (Fin n) ℝ}
    {Q : Set (Fin n × Fin n)}
    (hgeom : ∀ i j, (i, j) ∈ Q → FrozenCoreEdgeGeometry C Dm z₀ X Y i j)
    (hgh : ∀ i j, (i, j) ∈ Q → |g i j - h i j| ≤ probeError)
    (hg_bound : ∀ i j, |g i j| ≤ Bg)
    (hprobeError_le : probeError ≤ Bg)
    {c : M} {Drad : ℝ} (hX : ∀ i, dist (X i) c ≤ Drad)
    (hY : ∀ j, dist (Y j) c ≤ Drad) :
    ∀ i j, (i, j) ∈ Q →
      frozenCoreMatrix C ε z₀ X Y k t h i j ≤ k * (4 * Drad) + 2 * (|t| * Bg) := by
  intro i j hij
  have hbase := frozenCoreMatrix_le_slack_add_probeBound (n := n)
    (k := k) (t := t) (probeError := probeError) (Bg := Bg)
    hF hcomplete hu ha hinj Dm hε hε1 hdist hφu hφ hk hgeom hgh hg_bound hprobeError_le
    i j hij
  have hsl : distanceSlackEdgeCost X Y φ i j ≤ 4 * Drad :=
    distanceSlackEdgeCost_le_two_ball hφ hX hY i j
  have hks : k * distanceSlackEdgeCost X Y φ i j ≤ k * (4 * Drad) :=
    mul_le_mul_of_nonneg_left hsl hk
  have htg : t * g i j ≤ |t| * Bg := by
    have h1 : t * g i j ≤ |t * g i j| := le_abs_self _
    rw [abs_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hg_bound i j) (abs_nonneg t))
  linarith

/-- **The masked per-edge bound.**  Packaging the per-edge bound for the masked
frozen core matrix used by the finite-domination inequality: the entries off the
mask vanish and the constant is nonnegative on the good event. -/
theorem maskedFrozenCoreMatrix_entryBound_of_ball {n : ℕ} [PseudoMetricSpace M]
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (Dm : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {X Y : Fin n → M} {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    (hφ : LipschitzWith 1 φ)
    {k t probeError Bg : ℝ} (hk : 0 ≤ k)
    {z₀ : Fin n → Fin n → Z} {h g : Matrix (Fin n) (Fin n) ℝ}
    {Q : Set (Fin n × Fin n)}
    (hgeom : ∀ i j, (i, j) ∈ Q → FrozenCoreEdgeGeometry C Dm z₀ X Y i j)
    (hgh : ∀ i j, (i, j) ∈ Q → |g i j - h i j| ≤ probeError)
    (hg_bound : ∀ i j, |g i j| ≤ Bg)
    (hprobeError_le : probeError ≤ Bg)
    {c : M} {Drad : ℝ} (hDrad : 0 ≤ Drad) (hBg : 0 ≤ Bg)
    (hX : ∀ i, dist (X i) c ≤ Drad) (hY : ∀ j, dist (Y j) c ≤ Drad) :
    ∀ i j, maskedFrozenCost Q (frozenCoreMatrix C ε z₀ X Y k t h) i j ≤
      k * (4 * Drad) + 2 * (|t| * Bg) := by
  intro i j
  by_cases hij : (i, j) ∈ Q
  · rw [maskedFrozenCost_apply_of_mem hij]
    exact frozenCoreMatrix_le_of_ball hF hcomplete hu ha hinj Dm hε hε1 hdist hφu hφ hk
      hgeom hgh hg_bound hprobeError_le hX hY i j hij
  · rw [maskedFrozenCost_apply_of_not_mem hij]
    have hb : 0 ≤ |t| * Bg := mul_nonneg (abs_nonneg t) hBg
    have h1 : 0 ≤ k * (4 * Drad) := mul_nonneg hk (by linarith)
    nlinarith

/-- **Normalized frozen-core cost bound on the good event.**  For any doubly
stochastic fractional assignment, the normalized masked frozen-core cost of the
concrete frozen core matrix is at most the kinetic-class constant of the
amplitude event.  This is exactly the input E i j <= K consumed by
FinslerOriginalOffBadDomination.lean. -/
theorem maskedFrozenCoreCost_div_le_of_ball {n : ℕ} [PseudoMetricSpace M]
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    (Dm : C.TaylorRootCover ε) (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    {X Y : Fin n → M} {φ : M → ℝ} (hφu : ∀ x, φ x = u x)
    (hφ : LipschitzWith 1 φ)
    {k t probeError Bg : ℝ} (hk : 0 ≤ k)
    {z₀ : Fin n → Fin n → Z} {h g : Matrix (Fin n) (Fin n) ℝ}
    {Q : Set (Fin n × Fin n)}
    (hgeom : ∀ i j, (i, j) ∈ Q → FrozenCoreEdgeGeometry C Dm z₀ X Y i j)
    (hgh : ∀ i j, (i, j) ∈ Q → |g i j - h i j| ≤ probeError)
    (hg_bound : ∀ i j, |g i j| ≤ Bg)
    (hprobeError_le : probeError ≤ Bg)
    {c : M} {Drad : ℝ} (hDrad : 0 ≤ Drad) (hBg : 0 ≤ Bg)
    (hX : ∀ i, dist (X i) c ≤ Drad) (hY : ∀ j, dist (Y j) c ≤ Drad)
    {Pmat : Matrix (Fin n) (Fin n) ℝ}
    (hP : Pmat ∈ doublyStochastic ℝ (Fin n)) (hn : 0 < n) :
    fractionalAssignmentCost (maskedFrozenCost Q (frozenCoreMatrix C ε z₀ X Y k t h)) Pmat /
        (n : ℝ) ≤
      k * (4 * Drad) + 2 * (|t| * Bg) :=
  fractionalAssignmentCost_div_le_of_entryBound hn hP
    (maskedFrozenCoreMatrix_entryBound_of_ball hF hcomplete hu ha hinj Dm hε hε1 hdist
      hφu hφ hk hgeom hgh hg_bound hprobeError_le hDrad hBg hX hY)

end OTSelector.Reconstruction
