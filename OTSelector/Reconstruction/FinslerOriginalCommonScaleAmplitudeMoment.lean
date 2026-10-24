import OTSelector.Reconstruction.FinslerOriginalCommonScaleAmplitudeTail
import OTSelector.Reconstruction.FinslerOriginalMinimizerNormalizedField
import OTSelector.Reconstruction.OriginalCountingFieldEverywhereLipschitz

/-!
# Amplitude first moment of the divided normalized momentum field

The literal normalized momentum field is a coordinatewise infimum over the
actual occupied eligible nodes. On the actual node-error event the field at any
ambient point is comparable to the node data of one measurable completed atom:
the field value at the origin is bounded by the completed atom momentum plus the
explicit node error plus the field Lipschitz times the completed atom position.
This reduces the amplitude first moment to the completed-atom node-data first
moment, which is the remaining Poisson/Palm input.
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

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- On the actual node-error event the literal field amplitude at the origin is
bounded by the completed-atom node data: its covariantly transformed momentum,
the explicit original node error, and the field Lipschitz times its normalized
position. -/
theorem ae_amplitude_le_completedNodeData
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    let b := Real.sqrt (8 * |t| * G / h)
    let e₀ := fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
      originalCountingCompletedAtom
        (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
        (D.normalizedMomentumPhaseNodeMeasure T cut h s) 0
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤
        ‖normalizedMomentumNodeValue S w T (e₀ s)‖ + b +
          (L : ℝ) * ‖normalizedMomentumNodePosition S w T (cut + S.level) (e₀ s)‖ := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let b := Real.sqrt (8 * |t| * G / h)
  let e₀ := fun s : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
    originalCountingCompletedAtom
      (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
      (D.normalizedMomentumPhaseNodeMeasure T cut h s) 0
  have hfield := D.original_minimizer_canonical_normalized_momentum_field hF hw hgap hbounds
    T hg hgb t Q hmin hcut hh
  dsimp only at hfield
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  filter_upwards [hfield.2.2, Q.full_matching] with s herror hs
  have hcount := ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  have hn : IsLegalCountingMeasure
      (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
      (D.normalizedMomentumPhaseNodeMeasure T cut h s) :=
    isLegalCountingMeasure_originalCountingNodeRestriction
      (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) s.1.1 hcount
      (D.normalizedMomentumPhaseEligibleEdges T cut h)
  by_cases hactive : D.normalizedMomentumPhaseNodeMeasure T cut h s ∈
      originalCountingSupportActive (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
  · have he₀ : e₀ s ∈ (D.normalizedMomentumPhaseNodeMeasure T cut h s :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).support :=
      originalCountingCompletedAtom_mem_support _ _ hn hactive 0
    have hnode := herror (e₀ s) he₀
    set z := normalizedMomentumNodePosition S w T (cut + S.level) (e₀ s) with hz
    set pv := normalizedMomentumNodeValue S w T (e₀ s) with hpv
    have hval : ‖pv - D.normalizedMomentumPhaseField T cut h L s z‖ ≤ b := hnode
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have hlip := lipschitzWith_originalCountingRoughField_everywhere
      (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) L
      (fun e ↦ normalizedMomentumNodePosition S w T (cut + S.level) e)
      (fun e ↦ normalizedMomentumNodeValue S w T e i)
      (D.normalizedMomentumPhaseNodeMeasure T cut h s)
    have hd := hlip.dist_le_mul 0 z
    rw [Real.dist_eq, dist_eq_norm, zero_sub, norm_neg] at hd
    have hd' : |D.normalizedMomentumPhaseField T cut h L s 0 i -
        D.normalizedMomentumPhaseField T cut h L s z i| ≤ (L : ℝ) * ‖z‖ := hd
    have h1 : |pv i - D.normalizedMomentumPhaseField T cut h L s z i| ≤ b := by
      have := norm_le_pi_norm (pv - D.normalizedMomentumPhaseField T cut h L s z) i
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using this.trans hval
    have h2 : |D.normalizedMomentumPhaseField T cut h L s z i - pv i| ≤ b := by
      rw [abs_sub_comm]; exact h1
    have hb2 : |D.normalizedMomentumPhaseField T cut h L s z i| ≤ |pv i| + b := by
      calc |D.normalizedMomentumPhaseField T cut h L s z i|
          = |(D.normalizedMomentumPhaseField T cut h L s z i - pv i) + pv i| := by
            ring_nf
        _ ≤ |D.normalizedMomentumPhaseField T cut h L s z i - pv i| + |pv i| :=
            abs_add_le _ _
        _ ≤ b + |pv i| := by linarith
        _ = |pv i| + b := by ring
    have hpi : |pv i| ≤ ‖pv‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm pv i
    calc |D.normalizedMomentumPhaseField T cut h L s 0 i|
        ≤ |D.normalizedMomentumPhaseField T cut h L s 0 i -
            D.normalizedMomentumPhaseField T cut h L s z i| +
          |D.normalizedMomentumPhaseField T cut h L s z i| := by
          have h := abs_add_le
            (D.normalizedMomentumPhaseField T cut h L s 0 i -
              D.normalizedMomentumPhaseField T cut h L s z i)
            (D.normalizedMomentumPhaseField T cut h L s z i)
          simpa only [sub_add_cancel] using h
      _ ≤ (L : ℝ) * ‖z‖ + (|pv i| + b) := add_le_add hd' hb2
      _ ≤ ‖pv‖ + b + (L : ℝ) * ‖z‖ := by linarith
  · have hzero : D.normalizedMomentumPhaseField T cut h L s 0 = 0 := by
      funext i
      rw [normalizedMomentumPhaseField, originalCountingVectorField,
        originalCountingRoughField]
      rw [if_neg hactive]
      simp only [Pi.zero_apply]
    rw [hzero, norm_zero]
    exact add_nonneg (add_nonneg (norm_nonneg _) hb0) (mul_nonneg hL0 (norm_nonneg _))

/-- Amplitude first-moment assembly: a first-moment bound for the completed-atom
node data (its transformed momentum, the explicit node error and the field
Lipschitz times its normalized position) bounds the literal divided normalized
momentum field amplitude first moment by the same constant. This closes the
moment hypothesis of the amplitude-tail whole-path theorem. -/
theorem amplitudeMoment_of_completedNodeDataMoment
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    [Invertible T]
    {G : ℝ} {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value t ≤ P.value t)
    {cut h : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (hh : 0 < h)
    {M : ℝ}
    (hM : (∫⁻ s, ENNReal.ofReal (‖normalizedMomentumNodeValue S w T
        (originalCountingCompletedAtom
          (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
          (D.normalizedMomentumPhaseNodeMeasure T cut h s) 0)‖ +
        Real.sqrt (8 * |t| * G / h) +
        ((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
          Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ) *
          ‖normalizedMomentumNodePosition S w T (cut + S.level)
            (originalCountingCompletedAtom
              (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
              (D.normalizedMomentumPhaseNodeMeasure T cut h s) 0)‖)
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
      ≤ ENNReal.ofReal M) :
    let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
    (∫⁻ s, ENNReal.ofReal (‖D.normalizedMomentumPhaseField T cut h L s 0‖)
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤
      ENNReal.ofReal M := by
  dsimp only
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  have hred := D.ae_amplitude_le_completedNodeData hF hw hgap hbounds T hg hgb t Q hmin
    hcut hh
  dsimp only at hred
  have key : ∀ᵐ s ∂(Q.law : Measure
      (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ENNReal.ofReal ‖D.normalizedMomentumPhaseField T cut h L s 0‖ ≤
        ENNReal.ofReal (‖normalizedMomentumNodeValue S w T
          (originalCountingCompletedAtom
            (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
            (D.normalizedMomentumPhaseNodeMeasure T cut h s) 0)‖ +
          Real.sqrt (8 * |t| * G / h) +
          ((⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2),
            Real.sqrt_nonneg _⟩ : ℝ≥0) : ℝ) *
            ‖normalizedMomentumNodePosition S w T (cut + S.level)
              (originalCountingCompletedAtom
                (0 : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))
                (D.normalizedMomentumPhaseNodeMeasure T cut h s) 0)‖) := by
    filter_upwards [hred] with s hs
    exact ENNReal.ofReal_le_ofReal hs
  exact (lintegral_mono_ae key).trans hM

end OriginalSeedConditionalMoments

end OTSelector.Reconstruction
