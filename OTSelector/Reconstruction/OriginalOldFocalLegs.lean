import OTSelector.Reconstruction.OriginalBirthNormalizedRightLegs

/-! An old leg may start arbitrarily close to its focal endpoint. A retained
terminal subsegment gives the same original focal-frame lower bound. -/
open Set Matrix Module Manifold MeasureTheory
open scoped ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

/-- Equal inward and elapsed birth scales are exactly the original focal scale. -/
theorem birthResidueScale_same_time_eq_focal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) {t : ℝ} (ht : 0 < t) :
    birthResidueScale G t t = focalResidueScale G t := by
  have hcoef : t / t ^ 2 = t⁻¹ := by field_simp
  simp only [birthResidueScale, focalResidueScale, hcoef]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original full left old legs retain a uniform lower bound in the
same focal normalizer, even when the original source tends to the pole. -/
theorem original_left_old_focal_normalizedLegs_of_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef) {geoε lower upper t a ref b : ℝ}
    (hgeo : geoε < D.hi - D.lo) (hlower : 0 ≤ lower) (hupper : 0 ≤ upper)
    (hcomp : ∀ v ∈ Ioo 0 geoε,
      (originalSeedKernel S w (D.lo + v) - lower • ((v ^ 2)⁻¹ • G + 1)).PosSemidef ∧
      (upper • ((v ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.lo + v)).PosSemidef)
    (ht : 0 < t) (hscale : 8 * t < geoε)
    (ha : a - S.level ∈ Ioo D.lo D.hi) (hb : b - S.level ∈ Ioo D.lo D.hi)
    (href : ref - S.level - D.lo ∈ Icc t (2 * t))
    (hnear : t / 4 ≤ ref - a) (hfar : (S.level : ℝ) + D.lo + 8 * t ≤ b) :
    let T := positiveMatrixNormalizer (focalResidueScale G t)
    IsUnit T.det ∧
      (T * originalSeedClockCompliance S w a ref * Tᵀ - (lower / 64) • 1).PosSemidef ∧
      (T * originalSeedClockCompliance S w ref b * Tᵀ - (lower / 64) • 1).PosSemidef := by
  let r := ref - S.level - D.lo
  let T := positiveMatrixNormalizer (focalResidueScale G t)
  have hleg := D.original_left_birth_normalizedLegs_of_comparison hF hw hG hgeo
    hlower hupper hcomp ht ht le_rfl hscale
    (a := r - t / 4) (r := r) (b := b)
    (by linarith [href.1]) (by linarith) (by linarith [href.2])
    (α := (1 / 4 : ℝ)) (β := (1 / 4 : ℝ)) (by linarith) (by linarith) hb hfar
  dsimp only at hleg
  rw [birthResidueScale_same_time_eq_focal G ht] at hleg
  have hasub : (S.level : ℝ) + D.lo + (r - t / 4) = ref - t / 4 := by dsimp [r]; ring
  have hreq : (S.level : ℝ) + D.lo + r = ref := by dsimp [r]; ring
  rw [hasub, hreq] at hleg
  have hcoef : lower * (1 / 4) / 16 = lower / 64 := by ring
  rw [hcoef] at hleg
  have hcut : ref - S.level ∈ Ioo D.lo D.hi :=
    ⟨by linarith [href.1], by linarith [href.2]⟩
  have hdiff := (D.original_compliance_subsegment_posSemidef hF hw ha hcut
    (show a ≤ ref - t / 4 by linarith) (show ref - t / 4 ≤ ref by linarith)
    le_rfl).mul_mul_conjTranspose_same T
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul] at hdiff
  refine ⟨hleg.1, ?_, scalar_identity_lower_bound_mono (by linarith) hleg.2.2.2⟩
  convert hdiff.add hleg.2.1 using 1
  abel

/-- The unchanged full right old legs have the reflected focal-frame lower bound. -/
theorem original_right_old_focal_normalizedLegs_of_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef) {geoε lower upper t a ref b : ℝ}
    (hgeo : geoε < D.hi - D.lo) (hlower : 0 ≤ lower) (hupper : 0 ≤ upper)
    (hcomp : ∀ v ∈ Ioo 0 geoε,
      (originalSeedKernel S w (D.hi - v) - lower • ((v ^ 2)⁻¹ • G + 1)).PosSemidef ∧
      (upper • ((v ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.hi - v)).PosSemidef)
    (ht : 0 < t) (hscale : 8 * t < geoε)
    (ha : a - S.level ∈ Ioo D.lo D.hi) (hb : b - S.level ∈ Ioo D.lo D.hi)
    (href : D.hi - (ref - S.level) ∈ Icc t (2 * t))
    (hnear : t / 4 ≤ b - ref) (hfar : a ≤ (S.level : ℝ) + D.hi - 8 * t) :
    let T := positiveMatrixNormalizer (focalResidueScale G t)
    IsUnit T.det ∧
      (T * originalSeedClockCompliance S w a ref * Tᵀ - (lower / 64) • 1).PosSemidef ∧
      (T * originalSeedClockCompliance S w ref b * Tᵀ - (lower / 64) • 1).PosSemidef := by
  let r := D.hi - (ref - S.level)
  let T := positiveMatrixNormalizer (focalResidueScale G t)
  have hleg := D.original_right_birth_normalizedLegs_of_comparison hF hw hG hgeo
    hlower hupper hcomp ht ht le_rfl hscale
    (a := r - t / 4) (r := r) (b := a)
    (by linarith [href.1]) (by linarith) (by linarith [href.2])
    (α := (1 / 4 : ℝ)) (β := (1 / 4 : ℝ)) (by linarith) (by linarith) ha hfar
  dsimp only at hleg
  rw [birthResidueScale_same_time_eq_focal G ht] at hleg
  have hbsub : (S.level : ℝ) + D.hi - (r - t / 4) = ref + t / 4 := by dsimp [r]; ring
  have hreq : (S.level : ℝ) + D.hi - r = ref := by dsimp [r]; ring
  rw [hbsub, hreq] at hleg
  have hcoef : lower * (1 / 4) / 16 = lower / 64 := by ring
  rw [hcoef] at hleg
  have hcut : ref - S.level ∈ Ioo D.lo D.hi :=
    ⟨by linarith [href.2], by linarith [href.1]⟩
  have hdiff₀ := D.original_compliance_subsegment_posSemidef hF hw hcut hb le_rfl
    (show ref ≤ ref + t / 4 by linarith) (show ref + t / 4 ≤ b by linarith)
  have hdiff := hdiff₀.mul_mul_conjTranspose_same T
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul] at hdiff
  refine ⟨hleg.1, scalar_identity_lower_bound_mono (by linarith) hleg.2.2.2, ?_⟩
  convert hdiff.add hleg.2.1 using 1
  abel

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
