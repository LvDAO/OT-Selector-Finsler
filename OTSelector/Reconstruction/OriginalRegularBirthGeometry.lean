import OTSelector.Reconstruction.RegularBirthNormalization
import OTSelector.Reconstruction.OriginalRegularClockGeometry

/-! The actual original Finsler kernel supplies scalar birth geometry on every
compact regular clock strip. Short legs may shrink to zero; only their elapsed
scale is normalized, and the original kernel and compliance stay unchanged. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Integrating an actual upper mobility bound gives the physical leg-length
upper bound in the same fixed coordinate frame. -/
theorem intervalIntegral_scalar_identity_upper_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ℝ → Matrix ι ι ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hK : ContinuousOn K (Icc a b))
    (hupper : ∀ t ∈ Icc a b, (C • (1 : Matrix ι ι ℝ) - K t).PosSemidef) :
    (((b - a) * C) • (1 : Matrix ι ι ℝ) - (∫ t in a..b, K t)).PosSemidef := by
  have hKi : IntervalIntegrable K volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hK
  have hp := posSemidef_intervalIntegral hab hupper
  rw [intervalIntegral.integral_sub intervalIntegrable_const hKi,
    intervalIntegral.integral_const] at hp
  simpa only [smul_smul] using hp

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original smooth positive mobility has two-sided scalar bounds on a
compact regular clock strip, with constants produced from that same kernel. -/
theorem exists_original_kernel_compact_twoSided_bounds
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {J : Set ℝ} (hJ : IsCompact J) (hJI : J ⊆ Ioo D.lo D.hi) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ r ∈ J,
      (originalSeedKernel S w r - κ • 1).PosSemidef ∧
        (C • 1 - originalSeedKernel S w r).PosSemidef := by
  obtain ⟨κ, hκ, hlower⟩ := D.exists_original_kernel_uniform_lower_on_compact hF hw hJ hJI
  have hW := (D.original_kernel_regular hF hw).1.mono hJI
  obtain ⟨B, hB, hbound⟩ := exists_compact_matrixQuadratic_sum_bound hJ hW
  have hC : 0 < 2 * B + 1 := by linarith
  refine ⟨κ, 2 * B + 1, hκ, hC, ?_⟩
  intro r hr
  refine ⟨hlower r hr, ?_⟩
  apply posSemidef_scalar_identity_sub_of_quadratic_upper hC
    ((D.original_kernel_regular hF hw).2 r (hJI hr)).isHermitian
  intro v
  have hq := (le_abs_self (matrixQuadratic (originalSeedKernel S w r) v)).trans
    (hbound r hr v)
  have hsum := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦ sq_nonneg (v i))
  dsimp only [matrixQuadratic] at hq
  nlinarith

/-- Original regular short legs of length comparable with s normalize by s I.
Both constants are uniform as s tends to zero and the opposite endpoint may
still approach an actual focal end. -/
theorem exists_original_regular_birth_shortLeg_bounds
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {J : Set ℝ} (hJ : IsCompact J) (hJI : J ⊆ Ioo D.lo D.hi) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ {a b s : ℝ}, 0 < s → a ≤ b →
      Icc (a - (S.level : ℝ)) (b - (S.level : ℝ)) ⊆ J →
      s / 2 ≤ b - a → b - a ≤ 4 * s →
      let T := positiveMatrixNormalizer (s • (1 : Matrix (Fin (finrank ℝ S.covector.ker))
        (Fin (finrank ℝ S.covector.ker)) ℝ))
      (T * originalSeedClockCompliance S w a b * Tᵀ - (κ / 2) • 1).PosSemidef ∧
        ((4 * C) • 1 - T * originalSeedClockCompliance S w a b * Tᵀ).PosSemidef := by
  obtain ⟨κ, C, hκ, hC, hbounds⟩ := D.exists_original_kernel_compact_twoSided_bounds hF hw hJ hJI
  refine ⟨κ, C, hκ, hC, ?_⟩
  intro a b s hs hab hsub hleft hright
  have hK := (D.original_kernel_regular hF hw).1.mono (hsub.trans hJI)
  have hl := intervalIntegral_scalar_identity_lower_bound (sub_le_sub_right hab (S.level : ℝ)) hK
    (fun r hr ↦ (hbounds r (hsub hr)).1)
  have hu := intervalIntegral_scalar_identity_upper_bound (sub_le_sub_right hab (S.level : ℝ)) hK
    (fun r hr ↦ (hbounds r (hsub hr)).2)
  have heq : (b - (S.level : ℝ)) - (a - (S.level : ℝ)) = b - a := by ring
  simp only [heq] at hl hu
  change (originalSeedClockCompliance S w a b - ((b - a) * κ) • 1).PosSemidef at hl
  change (((b - a) * C) • 1 - originalSeedClockCompliance S w a b).PosSemidef at hu
  have hl' := scalar_identity_lower_bound_mono
    (show (κ / 2) * s ≤ (b - a) * κ by nlinarith) hl
  have hu' := hu.add (Matrix.PosSemidef.one.smul
    (show 0 ≤ (4 * C) * s - (b - a) * C by nlinarith))
  apply scalar_birth_normalized_leg_bounds hs
  · convert hl' using 1
    module
  · convert hu' using 1
    module

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
