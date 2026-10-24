import OTSelector.Analysis.InnerProductSpace.NearFrameInvariantProjection
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessNormalReadout

/-! Nearby physical frames annihilate the true original linear and clock-current readouts. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Every prescribed physical frame has arbitrarily close frames annihilating
all centered original scalar-current readouts on the same countable family. -/
theorem LegalWeightedStationaryPoissonMatching.exists_basis_near_projection_all_linearCurrentReadouts_zero
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Type*} [Countable K] (hq : 2 < q)
    (j : K → LegalMarkedOptimalInputScene q → Fin q → ℝ)
    (hj : ∀ a k, MemLp (fun ω ↦ j a ω k) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (hcenter : ∀ a k y, y ∈ translationFixedSubspace Q.sceneEuclideanKoopman ⊤ →
      ⟪(hj a k).toLp (fun ω ↦ j a ω k), y⟫_ℝ = 0)
    (b₀ : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)),
      (∀ i, ‖b i-b₀ i‖ < δ) ∧ ∀ i a C,
      (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
        (originalLinearCurrentReadoutLtwo (Q.law : Measure _) (j a) (hj a) C) = 0 := by
  let e : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin q))) ≃ Fin q :=
    finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ))
  obtain ⟨b,hnear,hb⟩ := exists_orthonormalBasis_near_hyperplane_invariant_projections_eq_zero
    (volume : Measure (EuclideanSpace ℝ (Fin q))) (by simpa using hq)
    Q.sceneEuclideanKoopman Q.sceneEuclideanKoopman_add
    (fun a : K × Fin q ↦ (hj a.1 a.2).toLp (fun ω ↦ j a.1 ω a.2))
    (fun a y hy ↦ hcenter a.1 a.2 y hy) (b₀.reindex e.symm) hδ
  refine ⟨b.reindex e,?_,?_⟩
  · intro i
    simpa only [OrthonormalBasis.reindex_apply,Equiv.symm_symm,Equiv.apply_symm_apply] using hnear (e.symm i)
  · intro i a C
    have hcoords (k : Fin q) :
        (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ (b.reindex e) i)ᗮ).starProjection
          ((hj a k).toLp (fun ω ↦ j a ω k)) = 0 := by
      simpa only [OrthonormalBasis.reindex_apply] using hb (e.symm i) (a,k)
    simp only [originalLinearCurrentReadoutLtwo,map_sum,map_smul,hcoords,smul_zero,
      Finset.sum_const_zero]

section ActualMinimizer
open OTSelector.Geometry ContinuousFinslerNorm Module Manifold
open scoped ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Actual minimization centers the original clock-set currents internally.
A frame arbitrarily close to any prescribed physical frame simultaneously
annihilates all of their original scalar readouts. -/
theorem OriginalSeedConditionalMoments.exists_basis_near_projection_all_pathClockSetCurrent_readouts_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 2 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) (τ : ℝ)
    (hmin : ∀ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g, Q.value τ ≤ Q'.value τ)
    {K : Type*} [Countable K]
    (η : K → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (hη : ∀ a, Measurable (η a)) (hηI : ∀ a, Integrable (η a) volume)
    (A : K → Set ℝ)
    (hL2 : ∀ a k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w (η a) (A a) scene k) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
    (b₀ : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
      (∀ i, ‖b i-b₀ i‖ < δ) ∧ ∀ i a C,
      (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
        (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
          (originalSeedPathClockSetCurrent S w (η a) (A a)) (hL2 a) C) = 0 := by
  apply Q.exists_basis_near_projection_all_linearCurrentReadouts_zero hq
    (fun a ↦ originalSeedPathClockSetCurrent S w (η a) (A a)) hL2 ?_ b₀ hδ
  intro a k y hy
  apply D.inner_pathClockSetCurrent_invariant_eq_zero hF hw (by omega)
    hgap hbounds Q τ hmin (hη a) (hηI a) (A a) (ContinuousLinearMap.proj k) (hL2 a k) y
  intro z
  exact hy ((EuclideanSpace.equiv _ ℝ).symm z) (by trivial)

end ActualMinimizer
end OTSelector.Reconstruction
