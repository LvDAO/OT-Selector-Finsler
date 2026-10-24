import OTSelector.Reconstruction.RegularBirthNormalization
import OTSelector.Reconstruction.OriginalBirthNormalizerQuadraticMoment

/-! The scalar regular-birth frame spends precisely its own original
momentum budget at each elapsed scale, under the same true joint Palm law. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scalar birth momentum has an s-scaled original quadratic bound, including
zero-dimensional coordinate spaces. -/
theorem scalar_birthNormalizer_momentum_sq_le {s : ℝ} (hs : 0 < s) (p : ι → ℝ) :
    ‖((positiveMatrixNormalizer (s • (1 : Matrix ι ι ℝ)))ᵀ)⁻¹ *ᵥ p‖ ^ 2 ≤
      (s * (Fintype.card ι : ℝ)) * ‖p‖ ^ 2 := by
  have h := positiveMatrixNormalizer_momentum_norm_sq_le (Matrix.PosDef.one.smul hs) p
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul] at h
  calc
    _ ≤ s * (p ⬝ᵥ p) := h
    _ = s * (∑ i, p i ^ 2) := by simp only [dotProduct, pow_two]
    _ ≤ s * ((Fintype.card ι : ℝ) * ‖p‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_sq_le_card_mul_pi_norm_sq p) hs.le
    _ = _ := by ring

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual original true-Palm regular-birth momentum moment retains the
same band's original momentum energy, with its exact elapsed-scale factor. -/
theorem original_regular_birthNormalizer_quadraticMoment_le
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) {gap : ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {s : ℝ} (hs : 0 < s)
    (B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) :
    (∫⁻ m in B, ENNReal.ofReal
      (‖((positiveMatrixNormalizer (s • (1 : Matrix (Fin (finrank ℝ S.covector.ker))
        (Fin (finrank ℝ S.covector.ker)) ℝ)))ᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m‖ ^ 2)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
    ENNReal.ofReal (s * (finrank ℝ S.covector.ker : ℝ)) *
      (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) := by
  have hmeas : Measurable (fun m ↦ ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)) :=
    ((measurable_originalSeedPairMomentum S hF hw).norm.pow_const 2).ennreal_ofReal
  rw [← lintegral_const_mul _ hmeas]
  apply lintegral_mono
  intro m
  have h := scalar_birthNormalizer_momentum_sq_le hs (originalSeedPairMomentum S w m)
  simp only [Fintype.card_fin] at h
  exact (ENNReal.ofReal_le_ofReal h).trans_eq
    (ENNReal.ofReal_mul (show 0 ≤ s * (finrank ℝ S.covector.ker : ℝ) by positivity))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
