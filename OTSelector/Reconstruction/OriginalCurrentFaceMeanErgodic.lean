import OTSelector.Reconstruction.OriginalCurrentSceneStrongContinuity
import OTSelector.Analysis.InnerProductSpace.OrthonormalFaceCoordinates
import OTSelector.Reconstruction.StationaryFaceBoxMeanErgodic
import OTSelector.Reconstruction.OriginalMinimizerCurrentHilbert

/-! Actual face averages of scalar L² readouts of the same original minimizing
current. The whole Koopman continuity and the mean-ergodic limit are produced
internally. Only the current's second moment remains an explicit input. -/

open Set Function Filter MeasureTheory
open scoped ENNReal InnerProductSpace Topology BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm Module Manifold
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section SameLaw
variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching q α β kin g)

/-- The literal original physical reroot, written in Euclidean coordinates
so a true orthonormal frame can be selected without changing the scene law. -/
def LegalWeightedStationaryPoissonMatching.sceneEuclideanKoopman
    (v : EuclideanSpace ℝ (Fin q)) :
    Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) :=
  stationaryKoopman (Q.law : Measure _) (legalMarkedInputSceneReroot q) Q.stationary
    (legalMarkedInputSceneReroot_zero q) (legalMarkedInputSceneReroot_add q)
    (EuclideanSpace.equiv (Fin q) ℝ v)

/-- Euclidean coordinates retain the exact additive law of the original
joint scene translations. -/
theorem LegalWeightedStationaryPoissonMatching.sceneEuclideanKoopman_add
    (v w : EuclideanSpace ℝ (Fin q))
    (f : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) :
    Q.sceneEuclideanKoopman v (Q.sceneEuclideanKoopman w f) =
      Q.sceneEuclideanKoopman (v + w) f := by
  simpa only [LegalWeightedStationaryPoissonMatching.sceneEuclideanKoopman, map_add] using
    stationaryKoopman_add (Q.law : Measure _) (legalMarkedInputSceneReroot q) Q.stationary
      (legalMarkedInputSceneReroot_zero q) (legalMarkedInputSceneReroot_add q)
      (EuclideanSpace.equiv (Fin q) ℝ v) (EuclideanSpace.equiv (Fin q) ℝ w) f

/-- Strong continuity holds for every L² vector of the same actual scene law. -/
theorem LegalWeightedStationaryPoissonMatching.continuous_sceneEuclideanKoopman
    (f : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) :
    Continuous (fun v ↦ Q.sceneEuclideanKoopman v f) :=
  (Q.continuous_sceneL2Koopman f).comp (EuclideanSpace.equiv (Fin q) ℝ).continuous

/-- Actual normalized Haar box averages on a codimension-one spatial face.
Every translated observable is under the original joint law Q. -/
def LegalWeightedStationaryPoissonMatching.sceneFaceHaarCubeAverage
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (i : Fin q)
    (R : ℝ) : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) →L[ℝ]
      Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)) :=
  stationaryHaarCubeAverage (fun v ↦ Q.sceneEuclideanKoopman (orthonormalFaceMap b i v))
    (fun f ↦ (Q.continuous_sceneEuclideanKoopman f).comp
      (orthonormalFaceMap b i).continuous_of_finiteDimensional) R

/-- At every positive radius this is the literal L²-valued average of the
original scene reroot over the genuine q−1 dimensional face cube. -/
theorem LegalWeightedStationaryPoissonMatching.sceneFaceHaarCubeAverage_apply
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (i : Fin q)
    {R : ℝ} (hR : 0 < R)
    (f : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) :
    Q.sceneFaceHaarCubeAverage b i R f =
      ∫ v, Lp.compMeasurePreserving
        (legalMarkedInputSceneReroot q
          (EuclideanSpace.equiv (Fin q) ℝ (orthonormalFaceMap b i v)))
        (Q.stationary (EuclideanSpace.equiv (Fin q) ℝ (orthonormalFaceMap b i v))) f
        ∂haarCubeRootLaw {k : Fin q // k ≠ i} R := by
  exact stationaryHaarCubeAverage_apply _ _ hR f

/-- The actual face averages converge to the original action's projection
onto invariants of this face; continuity and the box limit are theorems. -/
theorem LegalWeightedStationaryPoissonMatching.tendsto_sceneFaceHaarCubeAverage_projection
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (i : Fin q)
    (f : Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q))) :
    Tendsto (fun R : ℝ ↦ Q.sceneFaceHaarCubeAverage b i R f) atTop
      (𝓝 ((translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection f)) := by
  simpa only [LegalWeightedStationaryPoissonMatching.sceneFaceHaarCubeAverage,
    range_orthonormalFaceMap] using
    tendsto_stationaryFaceHaarCubeAverage_projection Q.sceneEuclideanKoopman
      Q.sceneEuclideanKoopman_add (orthonormalFaceMap b i)
      (fun f ↦ (Q.continuous_sceneEuclideanKoopman f).comp
        (orthonormalFaceMap b i).continuous_of_finiteDimensional) f

/-- A countable family of globally centered actual L² observations has one
common orthonormal frame on whose EVERY true face its actual averages vanish. -/
theorem LegalWeightedStationaryPoissonMatching.exists_basis_tendsto_sceneFaceHaarCubeAverage_zero
    {J : Type*} [Countable J] (hq : 2 < q)
    (f : J → Lp ℝ 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (hf : ∀ j y, y ∈ translationFixedSubspace Q.sceneEuclideanKoopman ⊤ →
      ⟪f j, y⟫_ℝ = 0) :
    ∃ b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)), ∀ i j,
      Tendsto (fun R : ℝ ↦ Q.sceneFaceHaarCubeAverage b i R (f j)) atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_hyperplane_invariant_projections_eq_zero
    (volume : Measure (EuclideanSpace ℝ (Fin q))) (by simpa using hq)
    Q.sceneEuclideanKoopman Q.sceneEuclideanKoopman_add f hf
  let e : Fin (finrank ℝ (EuclideanSpace ℝ (Fin q))) ≃ Fin q :=
    finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ))
  refine ⟨b.reindex e, fun i j ↦ ?_⟩
  simpa only [OrthonormalBasis.reindex_apply, hb] using
    Q.tendsto_sceneFaceHaarCubeAverage_projection (b.reindex e) i (f j)

end SameLaw

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Countably many scalar readouts of the SAME original minimizing
clock-set currents admit one actual common frame with vanishing true face
averages. Their invariant centering follows from the attained minimum;
their L² moment is the explicit input supplied by the full-traffic chain. -/
theorem OriginalSeedConditionalMoments.exists_basis_tendsto_pathClockSetCurrent_faceAverage_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 2 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (τ : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ R.value τ)
    {J : Type*} [Countable J]
    (η : J → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (hη : ∀ j, Measurable (η j)) (hηI : ∀ j, Integrable (η j) volume)
    (A : J → Set ℝ)
    (C : J → (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ] ℝ)
    (hL2 : ∀ j, MemLp (C j ∘ originalSeedPathClockSetCurrent S w (η j) (A j)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) :
    ∃ b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
        (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))), ∀ i j,
      Tendsto (fun R : ℝ ↦ Q.sceneFaceHaarCubeAverage b i R
        ((hL2 j).toLp (C j ∘ originalSeedPathClockSetCurrent S w (η j) (A j))))
        atTop (𝓝 0) := by
  apply Q.exists_basis_tendsto_sceneFaceHaarCubeAverage_zero hq
    (fun j ↦ (hL2 j).toLp (C j ∘ originalSeedPathClockSetCurrent S w (η j) (A j)))
  intro j y hy
  apply D.inner_pathClockSetCurrent_invariant_eq_zero hF hw (by omega)
    hgap hbounds Q τ hmin (hη j) (hηI j) (A j) (C j) (hL2 j) y
  intro z
  exact hy ((EuclideanSpace.equiv _ ℝ).symm z) (by trivial)

end OTSelector.Reconstruction
