import OTSelector.Reconstruction.OriginalOmittedCurrentSpatialBridgeNorm

/-! The actual Euclidean omitted-current square is bounded by the same original traffic square. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Passing from the original coordinate sup norm to genuine Euclidean energy costs
exactly the number of coordinates in the squared estimate. -/
theorem originalEuclidean_norm_sq_le_dim_mul_raw_norm_sq {q : ℕ} (v : Fin q → ℝ) :
    ‖(EuclideanSpace.equiv (Fin q) ℝ).symm v‖^2 ≤ (q:ℝ)*‖v‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _ : Fin q, ‖v‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
    _ = _ := by simp

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The same actual full-minus-retained Euclidean current square, in any original clock
slab, is controlled by the actual omitted complete-path traffic square. All finiteness and
pointwise bounds are produced from original local traffic; no field-energy estimate is assumed. -/
theorem lintegral_originalOmittedCurrent_euclidean_sq_le_traffic_sq
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (R ell : ℝ) (A : Set ℝ) :
    let q := finrank ℝ S.covector.ker
    let η := originalEuclideanMollifier q
    (∫⁻ scene, ∫⁻ z in haarRootCube (Fin q) R,
      ENNReal.ofReal (‖(EuclideanSpace.equiv (Fin q) ℝ).symm
        (originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) A scene -
          originalRetainedSeedPathClockSetCurrent S w R ell (fun x ↦ η (x-z)) A scene)‖^2)
      ∂volume ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
    ENNReal.ofReal (q:ℝ) *
      (∫⁻ scene, ∫⁻ z in haarRootCube (Fin q) R,
        originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z))
          (originalPathLengthRetained S w R ell)ᶜ scene ^ 2
        ∂volume ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) := by
  let q := finrank ℝ S.covector.ker
  let η := originalEuclideanMollifier q
  have h := D.ae_all_originalOmittedCurrent_norm_le_traffic hF hw hbounds Q
  calc
    _ ≤ ∫⁻ scene, ∫⁻ z in haarRootCube (Fin q) R,
        ENNReal.ofReal (q:ℝ) * originalSeedRestrictedPathAbsoluteTraffic S w
          (fun x ↦ η (x-z)) (originalPathLengthRetained S w R ell)ᶜ scene ^ 2
        ∂volume ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
      apply lintegral_mono_ae
      filter_upwards [h] with scene hs
      apply lintegral_mono
      intro z
      have hb := hs R ell A η (contDiff_originalEuclideanMollifier q).continuous
        (hasCompactSupport_originalEuclideanMollifier q) (originalEuclideanMollifier_nonneg q) z
      have hn := originalEuclidean_norm_sq_le_dim_mul_raw_norm_sq
        (originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) A scene -
          originalRetainedSeedPathClockSetCurrent S w R ell (fun x ↦ η (x-z)) A scene)
      have ht := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hb.2 2) (Nat.cast_nonneg q)
      apply (ENNReal.ofReal_le_ofReal (hn.trans ht)).trans_eq
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg q), ENNReal.ofReal_pow ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hb.1.ne]
    _ = _ := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
