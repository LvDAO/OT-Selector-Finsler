import OTSelector.Reconstruction.OriginalCurrentFaceMeanErgodic

/-! Fixed-coordinate selection and actual normal readouts of one original current. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Every scalar linear readout is the literal finite combination of the
original coordinate readouts, before any normal frame is selected. -/
theorem linear_current_readout_eq_sum_coordinates
    {q : ℕ} (C : (Fin q → ℝ) →ₗ[ℝ] ℝ) (v : Fin q → ℝ) :
    C v = ∑ k : Fin q, C (Pi.single k 1) * v k := by
  classical
  have hsum : (∑ k : Fin q, Pi.single k (v k)) = v := by ext k; simp
  calc
    C v = C (∑ k : Fin q, Pi.single k (v k)) := congrArg C hsum.symm
    _ = _ := ?_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hs : Pi.single k (v k) = (v k) • Pi.single k (1 : ℝ) := by
    ext j
    by_cases hj : j = k <;> simp [hj]
  rw [hs, map_smul]
  simp only [smul_eq_mul, mul_comm]

/-- The actual L2 readout of the same current, expressed using its fixed
coordinate L2 vectors. It represents the literal scalar linear functional. -/
def originalLinearCurrentReadoutLtwo
    {q Ω : Type*} [Fintype q] [DecidableEq q] [MeasurableSpace Ω]
    (μ : Measure Ω) (j : Ω → q → ℝ)
    (hj : ∀ k, MemLp (fun ω ↦ j ω k) 2 μ) (C : (q → ℝ) →ₗ[ℝ] ℝ) : Lp ℝ 2 μ :=
  ∑ k : q, C (Pi.single k 1) • (hj k).toLp (fun ω ↦ j ω k)

/-- The Hilbert readout has precisely the original scalar-current value
almost everywhere; no current is changed when the normal frame changes. -/
theorem coeFn_originalLinearCurrentReadoutLtwo
    {q : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (j : Ω → Fin q → ℝ)
    (hj : ∀ k, MemLp (fun ω ↦ j ω k) 2 μ) (C : (Fin q → ℝ) →ₗ[ℝ] ℝ) :
    originalLinearCurrentReadoutLtwo μ j hj C =ᵐ[μ] (fun ω ↦ C (j ω)) := by
  classical
  have hs := Lp.coeFn_fun_finsetSum Finset.univ
    (fun k : Fin q ↦ C (Pi.single k 1) • (hj k).toLp (fun ω ↦ j ω k))
  have hm := ae_all_iff.mpr (fun k : Fin q ↦ Lp.coeFn_smul
    (C (Pi.single k 1)) ((hj k).toLp (fun ω ↦ j ω k)))
  have hc := ae_all_iff.mpr (fun k : Fin q ↦ (hj k).coeFn_toLp)
  filter_upwards [hs, hm, hc] with ω hω hmω hcω
  change (∑ k : Fin q, C (Pi.single k 1) • (hj k).toLp (fun ω ↦ j ω k)) ω = _
  rw [hω]
  calc
    _ = ∑ k : Fin q, C (Pi.single k 1) * j ω k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hmω k]
      change C (Pi.single k 1) * ((hj k).toLp (fun ω ↦ j ω k)) ω = _
      rw [hcω k]
    _ = _ := (linear_current_readout_eq_sum_coordinates C (j ω)).symm

/-- The physical normal functional is the original Euclidean scalar flux
of the raw coordinate current, with no fitted or selected coefficient. -/
def originalEuclideanNormalReadout {q : ℕ} (n : EuclideanSpace ℝ (Fin q)) :
    (Fin q → ℝ) →ₗ[ℝ] ℝ :=
  (innerSL ℝ n).toLinearMap.comp (EuclideanSpace.equiv (Fin q) ℝ).symm.toLinearMap

/-- The actual normal Hilbert readout is the same original current dotted
with its selected true unit normal, almost everywhere under its original law. -/
theorem coeFn_originalNormalCurrentReadoutLtwo
    {q : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (j : Ω → Fin q → ℝ)
    (hj : ∀ k, MemLp (fun ω ↦ j ω k) 2 μ) (n : EuclideanSpace ℝ (Fin q)) :
    originalLinearCurrentReadoutLtwo μ j hj (originalEuclideanNormalReadout n) =ᵐ[μ]
      (fun ω ↦ ⟪n, (EuclideanSpace.equiv (Fin q) ℝ).symm (j ω)⟫_ℝ) :=
  coeFn_originalLinearCurrentReadoutLtwo μ j hj (originalEuclideanNormalReadout n)

/-- A single frame selected using only the fixed coordinate observations
annihilates every scalar linear readout on every face, including the true
normal readouts chosen after the frame. -/
theorem LegalWeightedStationaryPoissonMatching.exists_basis_projection_all_linearCurrentReadouts_zero
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Type*} [Countable K] (hq : 2 < q)
    (j : K → LegalMarkedOptimalInputScene q → Fin q → ℝ)
    (hj : ∀ a k, MemLp (fun ω ↦ j a ω k) 2 (Q.law : Measure (LegalMarkedOptimalInputScene q)))
    (hcenter : ∀ a k y, y ∈ translationFixedSubspace Q.sceneEuclideanKoopman ⊤ →
      ⟪(hj a k).toLp (fun ω ↦ j a ω k), y⟫_ℝ = 0) :
    ∃ b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)), ∀ i a C,
      (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
        (originalLinearCurrentReadoutLtwo (Q.law : Measure _) (j a) (hj a) C) = 0 := by
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_hyperplane_invariant_projections_eq_zero
    (volume : Measure (EuclideanSpace ℝ (Fin q))) (by simpa using hq)
    Q.sceneEuclideanKoopman Q.sceneEuclideanKoopman_add
    (fun a : K × Fin q ↦ (hj a.1 a.2).toLp (fun ω ↦ j a.1 ω a.2))
    (fun a y hy ↦ hcenter a.1 a.2 y hy)
  let e : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin q))) ≃ Fin q :=
    finCongr (finrank_euclideanSpace_fin (𝕜 := ℝ))
  refine ⟨b.reindex e, fun i a C ↦ ?_⟩
  have hcoords (k : Fin q) :
      (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ (b.reindex e) i)ᗮ).starProjection
        ((hj a k).toLp (fun ω ↦ j a ω k)) = 0 := by
    simpa only [OrthonormalBasis.reindex_apply] using hb (e.symm i) (a,k)
  simp only [originalLinearCurrentReadoutLtwo, map_sum, map_smul, hcoords, smul_zero,
    Finset.sum_const_zero]

section ActualMinimizer
open OTSelector.Geometry ContinuousFinslerNorm Module Manifold
open scoped ContDiff
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The same actual minimizing clock-set currents admit a single frame
whose true normal readouts all have zero face-invariant component. Only
fixed-coordinate second moments are assumed; actual minimizing centering
and all normal-frame linear combinations are produced internally. -/
theorem OriginalSeedConditionalMoments.exists_basis_projection_all_pathClockSetCurrent_readouts_zero
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
    {K : Type*} [Countable K]
    (η : K → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (hη : ∀ a, Measurable (η a)) (hηI : ∀ a, Integrable (η a) volume)
    (A : K → Set ℝ)
    (hL2 : ∀ a k, MemLp (fun s ↦ originalSeedPathClockSetCurrent S w (η a) (A a) s k) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) :
    ∃ b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
        (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))), ∀ i a C,
      (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
        (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
          (originalSeedPathClockSetCurrent S w (η a) (A a)) (hL2 a) C) = 0 := by
  apply Q.exists_basis_projection_all_linearCurrentReadouts_zero hq
    (fun a ↦ originalSeedPathClockSetCurrent S w (η a) (A a)) hL2
  intro a k y hy
  apply D.inner_pathClockSetCurrent_invariant_eq_zero hF hw (by omega)
    hgap hbounds Q τ hmin (hη a) (hηI a) (A a) (ContinuousLinearMap.proj k) (hL2 a k) y
  intro z
  exact hy ((EuclideanSpace.equiv _ ℝ).symm z) (by trivial)

end ActualMinimizer

end OTSelector.Reconstruction
