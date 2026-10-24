import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOrientedPortLaws
import OTSelector.Reconstruction.OriginalStagePortAtomArrays

/-! Actual same-frame original ports packaged without a spatial sampling premise. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal BigOperators Topology ContDiff Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- A family records only unchanged endpoint labels and their actual point
measure. Its probability smoothing laws and error bounds are then derived. -/
structure OriginalOrientedPortAtomFamily {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (π : Measure (LegalMarkedPhysicalPoint q)) where
  count : ℕ
  points : Fin count → LegalMarkedPhysicalPoint q
  measure_eq : π = ∑ i, Measure.dirac (points i)
  point_mem : ∀ i, (points i).1 ∈ originalCenteredPhysicalCubeRegion b (2*R)

namespace OriginalOrientedPortAtomFamily
variable {q : ℕ} {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {R : ℝ} {π : Measure (LegalMarkedPhysicalPoint q)}
  (A : OriginalOrientedPortAtomFamily b R π)

/-- The canonical physical probability law attached to the unchanged original label. -/
def law (i : Fin A.count) : Measure (EuclideanSpace ℝ (Fin q)) :=
  originalPhysicalOrientedPortLaw b R (A.points i).1

/-- Exact per-label probabilities, actual Euclidean smoothing cost and every
clock-class marginal are derived from the real reflected kernel. -/
theorem spec (hR : 1 ≤ R) :
    (∀ i, IsProbabilityMeasure (A.law i)) ∧
    (∀ i, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (A.points i).1) v^2)
      (A.law i)) ∧
    (∑ i, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (A.points i).1) v^2 ∂A.law i) ≤ π.real univ ∧
    ∀ C : Set ℝ, MeasurableSet C →
      (((volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))).withDensity
        (fun z ↦ ENNReal.ofReal (originalOrientedStageReflectedClassDensity b R C π z))).map
        (EuclideanSpace.equiv _ ℝ).symm) =
        ∑ i, if (A.points i).2 ∈ C then A.law i else 0 := by
  have hs i := originalPhysicalOrientedPortLaw_spec b hR (A.point_mem i)
  refine ⟨fun i ↦ (hs i).1, fun i ↦ (hs i).2.1, ?_, ?_⟩
  · have hm : π.real univ = (A.count : ℝ) := by
      rw [measureReal_def]
      conv_lhs => rw [A.measure_eq]
      simp [Measure.finsetSum_apply]
    rw [hm]
    calc
      _ ≤ ∑ _i : Fin A.count, (1 : ℝ) := Finset.sum_le_sum (fun i _ ↦ (hs i).2.2)
      _ = _ := by simp
  · intro C hC
    conv_lhs => rw [A.measure_eq]
    exact originalFiniteEndpointAtoms_physicalOrientedPortClassMeasure A.points C hC b R
end OriginalOrientedPortAtomFamily

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The same actual original scene produces both finite families. Original
integer structure, finiteness and cube support are proved by the port producer. -/
theorem ae_exists_originalPhysicalOrientedStagePortFamilies
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      let A := originalOrientedPathLengthRetained S w b R ell
      let K := originalCenteredPhysicalCubeRegion b (2*R)
      Nonempty (OriginalOrientedPortAtomFamily b R
        (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge _)).fst) ∧
      Nonempty (OriginalOrientedPortAtomFamily b R
        (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge _)).snd) := by
  filter_upwards [D.ae_exists_originalOrientedStagePortArrays hF hw Q b hell hR] with scene hs
  obtain ⟨⟨ns,xs,hxs,hx⟩,⟨nt,xt,hxt,hy⟩⟩ := hs
  exact ⟨⟨⟨ns,xs,hxs,hx⟩⟩,⟨⟨nt,xt,hxt,hy⟩⟩⟩
end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
