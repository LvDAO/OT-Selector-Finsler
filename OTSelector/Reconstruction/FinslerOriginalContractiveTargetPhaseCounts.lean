import OTSelector.Analysis.ContractivePairCurve
import OTSelector.Reconstruction.FinslerOriginalAdaptiveTargetPhaseCurveCounts

/-!
# Actual original edge counts near an internally generated inverse curve

The same original-data event controls all Lipschitz fields and small mobility
families chosen from the entire matching scene. No curve, finite code, or
selected-edge count law is supplied as an assumption.
-/
open Set Function MeasureTheory Module Manifold Matrix
open scoped ContDiff Topology Matrix.Norms.Operator Classical ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- A single data-only bad event controls all original physical contributors to
all small-mobility rough fields, including fields selected using the whole scene. -/
theorem ae_count_contractiveTargetContributors_lt_of_not_badEvent
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) {m : ℕ} (hm : 1 ≤ m)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {L ρ A a b K : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    let C := max (2 * (a + ρ * b)) (b + 2 * L * (a + ρ * b))
    let z := fun e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) ↦
      originalSeedCompletePath S w e.1.1 (physicalPairAnchor e).2 (cut + S.level)
    let p := fun e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker) ↦
      originalSeedPairMomentum S w (physicalPairAnchor e).2
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      s ∉ D.targetPhaseCurveBadEvent cut m C K →
      ∀ P : (Fin (finrank ℝ S.covector.ker) → ℝ) → (Fin (finrank ℝ S.covector.ker) → ℝ),
      (∀ x y, ‖P x - P y‖ ≤ L * ‖x - y‖) →
      ∀ R : ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
        (Fin (finrank ℝ S.covector.ker) → ℝ),
      (∀ t ∈ Icc (0 : ℝ) 1, ‖R t‖ * L ≤ (1 / 2 : ℝ)) →
      (∀ t ∈ Icc (0 : ℝ) 1, ‖R t‖ ≤ ρ) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        ‖R t - R v‖ ≤ A * |t - v|) →
      2 * (ρ + 1) * ‖P 0‖ ≤ (m : ℝ) →
      4 * (1 + L) * A * ‖P 0‖ ≤ (m : ℝ) →
      ∀ V : Set (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)),
      (∀ e ∈ V, e.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧
        e.2.2 ∈ D.targetPhaseClocks cut ∧ e.1.2 < e.2.2 ∧
        ∃ t ∈ Icc (0 : ℝ) 1, ‖z e + R t (p e)‖ ≤ a ∧ ‖p e - P (z e)‖ ≤ b) →
      (s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) V < (∞ : ℝ≥0∞) ∧
        ((s.1.1 : Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) V).toReal <
          K * (m : ℝ) := by
  dsimp only
  have hC : 0 ≤ max (2 * (a + ρ * b)) (b + 2 * L * (a + ρ * b)) := by positivity
  filter_upwards [D.ae_count_targetPathPhaseTube_lt_of_not_badEvent hF hw hcut hm Q hC]
    with s hs
  intro hsnot P hP R hsmall hR hRLip hroot hspeed V hV
  obtain ⟨z₀, γ, _, _, hγroot, hγspeed, htube⟩ :=
    exists_contractive_phasePairCurve hL hP R hsmall hρ hA hR hRLip
  have ht0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  apply hs hsnot γ ((hγroot 0 ht0).trans hroot)
    (fun t ht v hv ↦ (hγspeed t ht v hv).trans
      (mul_le_mul_of_nonneg_right hspeed (abs_nonneg _))) V
  intro e he
  obtain ⟨hsource, htarget, horder, t, ht, hphysical, hrough⟩ := hV e he
  exact ⟨hsource, htarget, horder, t, ht, htube t ht _ _ a b hphysical hrough⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
