import OTSelector.Reconstruction.FinslerOriginalMomentumField
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate

/-! The actual jointly measurable covariant momentum field has the same law
at every physical spatial point under the original stationary matching law. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Full original spatial stationarity and actual field covariance give exact
equality of its one-point laws, even though the field depends on the whole scene. -/
theorem OriginalSeedConditionalMoments.map_momentumPhaseField_at_eq
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cut : ℝ} (hcut : cut ∈ Ioo D.lo D.hi) (h : ℝ) (L : ℝ≥0)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (x y : Fin (finrank ℝ S.covector.ker) → ℝ) :
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).map
      (fun s ↦ D.momentumPhaseField cut h L s x) =
    (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).map
      (fun s ↦ D.momentumPhaseField cut h L s y) := by
  have hm := D.measurable_momentumPhaseField hF hw hcut h L
  have hsection : Measurable (fun s : LegalMarkedOptimalInputScene
      (finrank ℝ S.covector.ker) ↦ (s, y)) := measurable_id.prodMk measurable_const
  have hy := hm.comp hsection
  have hcov : (fun s ↦ D.momentumPhaseField cut h L
      (legalMarkedInputSceneReroot _ (x - y) s) y)
        =ᵐ[(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))]
        (fun s ↦ D.momentumPhaseField cut h L s x) := by
    filter_upwards [Q.full_matching] with s hs
    have hc := D.momentumPhaseField_reroot hF hw hcut h L s hs (x - y) x
    have hxy : x - (x - y) = y := by abel
    rw [hxy] at hc
    exact hc
  calc
    _ = (Q.law : Measure _).map ((fun s ↦ D.momentumPhaseField cut h L s y) ∘
        legalMarkedInputSceneReroot _ (x - y)) := Measure.map_congr hcov.symm
    _ = ((Q.law : Measure _).map (legalMarkedInputSceneReroot _ (x - y))).map
        (fun s ↦ D.momentumPhaseField cut h L s y) :=
      (Measure.map_map hy (Q.stationary (x - y)).measurable).symm
    _ = _ := by rw [(Q.stationary (x - y)).map_eq]

end OTSelector.Reconstruction
