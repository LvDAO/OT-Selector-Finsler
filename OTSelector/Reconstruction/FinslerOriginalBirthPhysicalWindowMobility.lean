import OTSelector.Reconstruction.FinslerOriginalSupportedBirthWindowWeights
import OTSelector.Reconstruction.OriginalBirthMobilityBounds

/-! The unchanged finite birth windows inherit bounds for their actual clock
mobility, including both physical endpoints and the original forward clock. -/
open Set Function MeasureTheory Matrix Module Manifold
open scoped ENNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual left window has its unchanged reference, endpoints and mobility. -/
theorem originalLeftBirthPhysicalWindow_mobility_bounds_of_band_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    {ε cap geoε B : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (hgeo : geoε < D.hi - D.lo) (hB : 0 ≤ B)
    (n j i ell : ℕ) (hi : i < dyadicBirthBandCount j)
    (hell : ell < birthPhysicalClockWindowCount cap)
    (hscale : 4 * birthDyadicShellScale ε n < geoε)
    (hbound : ∀ r ∈ Icc (birthDyadicShellScale ε n / 2)
      (4 * birthDyadicShellScale ε n),
      ‖birthDyadicElapsedScale ε n j •
        (positiveMatrixNormalizer (birthResidueScale G (birthDyadicShellScale ε n)
          (birthDyadicElapsedScale ε n j)) * originalSeedKernel S w (D.lo + r) *
          (positiveMatrixNormalizer (birthResidueScale G (birthDyadicShellScale ε n)
            (birthDyadicElapsedScale ε n j)))ᵀ)‖ ≤ B) :
    let T := positiveMatrixNormalizer
      (birthResidueScale G (birthDyadicShellScale ε n) (birthDyadicElapsedScale ε n j))
    let ref := D.originalLeftBirthPhysicalClockReference ε cap n j i ell
    let width := birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)
    let R := originalNormalizedClockMobility S w T ref width
    ref - S.level ∈ Ioo D.lo D.hi ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ref + width * r - S.level ∈ Ioo D.lo D.hi) ∧
      R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ cap * B) ∧
      ∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        ‖R r - R v‖ ≤ (cap * B) * |r - v| := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let ref := D.originalLeftBirthPhysicalClockReference ε cap n j i ell
  let width := birthPhysicalClockWindowWidth cap s
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hs : 0 < s := (birthDyadicClockBand_base_bounds hε n j i hi).1
  have hwidth : 0 < width := (birthPhysicalClockWindow_spec hcap hs).2.1
  have hwidthcap : width ≤ cap * s := (birthPhysicalClockWindow_spec hcap hs).2.2.1
  have hwin : ∀ x ∈ Icc ref (ref + width), x - S.level ∈ Ioo D.lo D.hi := by
    intro x hx
    have hx' := D.originalLeftBirthPhysicalClockWindow_inward_bounds
      hε hcap n j i ell hi hell hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hwindow : uIcc (ref - S.level) (ref - S.level + width) ⊆
      Icc (D.lo + t / 2) (D.lo + 4 * t) := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hx' := D.originalLeftBirthPhysicalClockWindow_inward_bounds
      hε hcap n j i ell hi hell
      (c := x + S.level) (show x + S.level ∈ Icc ref (ref + width) from
        ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hmob := D.original_left_birth_complianceCurve_bounds hF hw hgeo ht hs hscale hB
    hwindow hbound
  have hcoef : B * |width| / s ≤ cap * B := by
    rw [abs_of_pos hwidth]
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hwidthcap hB]
  refine ⟨hwin ref ⟨le_rfl, by linarith⟩, ?_, hmob.1, ?_, ?_⟩
  · intro r hr
    exact hwin _ ⟨by nlinarith [hr.1], by nlinarith [hr.2]⟩
  · intro r hr
    exact (hmob.2.1 r hr).trans hcoef
  · intro r hr v hv
    exact (hmob.2.2 r hr v hv).trans
      (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))

/-- The reflected window preserves its negative elapsed parameter exactly. -/
theorem originalRightBirthPhysicalWindow_mobility_bounds_of_band_bound
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    {ε cap geoε B : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (hgeo : geoε < D.hi - D.lo) (hB : 0 ≤ B)
    (n j i ell : ℕ) (hi : i < dyadicBirthBandCount j)
    (hell : ell < birthPhysicalClockWindowCount cap)
    (hscale : 4 * birthDyadicShellScale ε n < geoε)
    (hbound : ∀ r ∈ Icc (birthDyadicShellScale ε n / 2)
      (4 * birthDyadicShellScale ε n),
      ‖birthDyadicElapsedScale ε n j •
        (positiveMatrixNormalizer (birthResidueScale G (birthDyadicShellScale ε n)
          (birthDyadicElapsedScale ε n j)) * originalSeedKernel S w (D.hi - r) *
          (positiveMatrixNormalizer (birthResidueScale G (birthDyadicShellScale ε n)
            (birthDyadicElapsedScale ε n j)))ᵀ)‖ ≤ B) :
    let T := positiveMatrixNormalizer
      (birthResidueScale G (birthDyadicShellScale ε n) (birthDyadicElapsedScale ε n j))
    let ref := D.originalRightBirthPhysicalClockReference ε cap n j i ell
    let width := birthPhysicalClockWindowWidth cap (birthDyadicElapsedScale ε n j)
    let R := originalNormalizedClockMobility S w T ref (-width)
    ref - S.level ∈ Ioo D.lo D.hi ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ref + (-width) * r - S.level ∈ Ioo D.lo D.hi) ∧
      R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ cap * B) ∧
      ∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        ‖R r - R v‖ ≤ (cap * B) * |r - v| := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let ref := D.originalRightBirthPhysicalClockReference ε cap n j i ell
  let width := birthPhysicalClockWindowWidth cap s
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hs : 0 < s := (birthDyadicClockBand_base_bounds hε n j i hi).1
  have hwidth : 0 < width := (birthPhysicalClockWindow_spec hcap hs).2.1
  have hwidthcap : width ≤ cap * s := (birthPhysicalClockWindow_spec hcap hs).2.2.1
  have hwin : ∀ x ∈ Icc (ref - width) ref, x - S.level ∈ Ioo D.lo D.hi := by
    intro x hx
    have hx' := D.originalRightBirthPhysicalClockWindow_inward_bounds
      hε hcap n j i ell hi hell hx
    exact ⟨by linarith [hx'.2], by linarith [hx'.1]⟩
  have hwindow : uIcc (ref - S.level) (ref - S.level + (-width)) ⊆
      Icc (D.hi - 4 * t) (D.hi - t / 2) := by
    intro x hx
    rw [uIcc_of_ge (by linarith)] at hx
    have hx' := D.originalRightBirthPhysicalClockWindow_inward_bounds
      hε hcap n j i ell hi hell
      (c := x + S.level) (show x + S.level ∈ Icc (ref - width) ref from
        ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    exact ⟨by linarith [hx'.2], by linarith [hx'.1]⟩
  have hmob := D.original_right_birth_complianceCurve_bounds hF hw hgeo ht hs hscale hB
    hwindow hbound
  have hcoef : B * |-width| / s ≤ cap * B := by
    rw [abs_neg, abs_of_pos hwidth]
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hwidthcap hB]
  refine ⟨hwin ref ⟨by linarith, le_rfl⟩, ?_, hmob.1, ?_, ?_⟩
  · intro r hr
    exact hwin _ ⟨by nlinarith [hr.2], by nlinarith [hr.1]⟩
  · intro r hr
    exact (hmob.2.1 r hr).trans hcoef
  · intro r hr v hv
    exact (hmob.2.2 r hr v hv).trans
      (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
