import OTSelector.Reconstruction.FinslerQuadraticCostDifferenceOriginal
import OTSelector.Reconstruction.OriginalSeedPairCoefficientContinuity

/-!
# Continuity of the original frozen cost on its full open legal domain

Every strictly ordered interior pair has a compact interior neighborhood. The
existing same-kernel compliance continuity theorem therefore supplies continuity
on the entire open legal domain, without a global extension across illegal pairs.
-/

open Set Filter MeasureTheory Manifold Module
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Reconstruction.OriginalSeedConditionalMoments

open OTSelector.Geometry ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

omit [BorelSpace E] in
/-- The literal original pair coefficient is continuous throughout its full
strictly ordered interior domain, in the original scalar clock. -/
theorem continuousOn_pair_coefficient_legal
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ContinuousOn (originalSeedPairCoefficient S w)
      {p | p.1 - S.level ∈ Ioo D.lo D.hi ∧
        p.2 - S.level ∈ Ioo D.lo D.hi ∧ p.1 < p.2} := by
  intro p hp
  obtain ⟨a, ha₀, ha₁⟩ := exists_between
    (show D.lo + S.level < p.1 by linarith [hp.1.1])
  obtain ⟨b, hb₀, hb₁⟩ := exists_between
    (show p.2 < D.hi + S.level by linarith [hp.2.1.2])
  have hab : a ≤ b := by linarith [hp.2.2]
  have ha : a - S.level ∈ Ioo D.lo D.hi :=
    ⟨by linarith, by linarith [hp.1.2]⟩
  have hb : b - S.level ∈ Ioo D.lo D.hi :=
    ⟨by linarith [hp.2.1.1], by linarith⟩
  have hneigh : {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ q.2 ∈ Icc a b ∧ q.1 < q.2} ∈ 𝓝 p :=
    inter_mem
      (continuousAt_fst.preimage_mem_nhds
        (Icc_mem_nhds ha₁ (by linarith [hp.2.2])))
      (inter_mem
        (continuousAt_snd.preimage_mem_nhds
          (Icc_mem_nhds (by linarith [hp.2.2]) hb₀))
        ((isOpen_lt continuous_fst continuous_snd).mem_nhds hp.2.2))
  exact ((D.continuousOn_pair_coefficient hF hw hab ha hb).continuousAt
    hneigh).continuousWithinAt

omit [BorelSpace E] in
/-- The original frozen quadratic cost is jointly continuous on its actual open
legal endpoint domain, using the same coefficient as the distance expansion. -/
theorem continuousOn_quadratic_cost_legal
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ContinuousOn (Function.uncurry (Probability.cavitySpatialDifferenceCost
      (fun s t v ↦ matrixQuadratic (originalSeedPairCoefficient S w (s, t)) v)))
      (originalQuadraticLegalDomain S.level D.lo D.hi id) := by
  let X := (Fin (finrank ℝ S.covector.ker) → ℝ) × ℝ
  have hclock : Continuous (fun p : X × X ↦ (p.1.2, p.2.2)) :=
    (continuous_snd.comp continuous_fst).prodMk
      (continuous_snd.comp continuous_snd)
  have hdelta : Continuous (fun p : X × X ↦ p.2.1 - p.1.1) :=
    (continuous_fst.comp continuous_snd).sub (continuous_fst.comp continuous_fst)
  have hA := (D.continuousOn_pair_coefficient_legal hF hw).comp
    hclock.continuousOn (fun p hp ↦ hp)
  exact continuous_matrixQuadratic.comp_continuousOn (hA.prodMk hdelta.continuousOn)

end OTSelector.Reconstruction.OriginalSeedConditionalMoments
