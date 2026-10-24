import OTSelector.Reconstruction.FinslerOriginalBirthWindowShortLegUpper
import OTSelector.Reconstruction.FinslerOriginalBirthPhysicalWindowClockWitnesses
import OTSelector.Reconstruction.FinslerOriginalBirthPhysicalWindowMobility
import OTSelector.Reconstruction.FinslerOriginalBirthSameResidue
import OTSelector.Reconstruction.CommonPhysicalNormalizedPhaseWindow

/-! Original Finsler pole data produces one birth collar and node threshold.
Every finite physical window in its same canonical birth frame has an actual
contractive mobility curve and internally eligible occupied contributors. -/
open Set Function MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

/-- One deterministic collar respects both original geometry and clock separation. -/
theorem exists_uniformBirthWindowClockCollar {geoε gap : ℝ}
    (hgeoε : 0 < geoε) (hgap : 0 < gap) :
    ∃ ε : ℝ, 0 < ε ∧ ε < geoε ∧ 8 * ε ≤ gap ∧
      ∀ n : ℕ, 8 * birthDyadicShellScale ε n < geoε := by
  let ε := min (geoε / 8) (gap / 8)
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hg : ε ≤ geoε / 8 := min_le_left _ _
  have hs : ε ≤ gap / 8 := min_le_right _ _
  refine ⟨ε, hε, by linarith, by linarith, ?_⟩
  intro n
  have hh : 2 * birthDyadicShellScale ε n ≤ ε := by
    rw [two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  linarith

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The same original left residue produces actual eligible and contractive
birth windows at every dyadic scale, with no window eligibility oracle. -/
theorem exists_original_left_supported_contractive_birthWindows_sameResidue
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (hgap : 0 < gap) {η : ℝ} (hη : 0 < η) (hηspan : η < D.hi - D.lo)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker))
      (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-η) η))
    (hpole : ∀ r ∈ Ioo 0 η,
      originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε : ℝ, 0 < ε ∧ ε < η ∧ ∃ h : ℝ, 0 < h ∧ ∃ B ≥ 0,
      ∃ U : ℝ, 0 < U ∧ ∀ (L : ℝ≥0) (cap : ℝ), 0 < cap →
      let cap' := commonPhysicalNormalizedWindowFraction cap B (L : ℝ)
      ∀ (n j i ell : ℕ), i < dyadicBirthBandCount j →
        ell < birthPhysicalClockWindowCount cap' →
      let T := positiveMatrixNormalizer
        (birthResidueScale G (birthDyadicShellScale ε n) (birthDyadicElapsedScale ε n j))
      let ref := D.originalLeftBirthPhysicalClockReference ε cap' n j i ell
      let width := birthPhysicalClockWindowWidth cap' (birthDyadicElapsedScale ε n j)
      let R := originalNormalizedClockMobility S w T ref width
      IsUnit T.det ∧ ref - S.level ∈ Ioo D.lo D.hi ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ref + width * r - S.level ∈ Ioo D.lo D.hi) ∧
        R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ cap' * B) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
          ‖R r - R v‖ ≤ (cap' * B) * |r - v|) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) ∧
        ∀ (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (clock : ℝ),
          D.originalSupportedLeftBirthPhysicalClockWeight ε cap' n j i ell
            ((physicalPairAnchor e).2, clock) ≠ 0 →
          e ∈ D.normalizedMomentumPhaseEligibleEdges T (ref - S.level) h ∧
            (U • 1 - T * D.sourcePhaseLeg (ref - S.level) e.1.2 * Tᵀ).PosSemidef ∧
            ∃ r ∈ Icc (0 : ℝ) 1, clock = ref + width * r := by
  obtain ⟨geoε, hgeoε, hgeoη, hgeospan, lower, upper, hlower, hupper, hcomp⟩ :=
    D.exists_original_left_birth_comparison_sameResidue hF hw hη hηspan hG hRem hpole
  obtain ⟨B, hB, hmob⟩ := D.original_left_birth_mobility_bound_of_comparison
    hF hw hG hgeospan hupper.le (fun r hr ↦ (hcomp r hr).2)
  obtain ⟨ε, hε, hεgeo, hsmall, hscale⟩ :=
    exists_uniformBirthWindowClockCollar hgeoε hgap
  refine ⟨ε, hε, hεgeo.trans hgeoη, lower / 128, by positivity, B, hB,
    16 * upper, by positivity, ?_⟩
  intro L cap hcap
  let cap' := commonPhysicalNormalizedWindowFraction cap B (L : ℝ)
  have hcap' : 0 < cap' :=
    (commonPhysicalNormalizedWindowFraction_spec hcap hB L.coe_nonneg).1
  dsimp only
  intro n j i ell hi hell
  have ht : 0 < birthDyadicShellScale ε n := birthDyadicShellScale_pos hε n
  have hs : 0 < birthDyadicElapsedScale ε n j :=
    (birthDyadicClockBand_base_bounds hε n j i hi).1
  have hm := D.originalLeftBirthPhysicalWindow_mobility_bounds_of_band_bound
    hF hw hε hcap' hgeospan hB n j i ell hi hell (by linarith [hscale n])
    (G := G) (fun r hr ↦ hmob ht hs (by linarith [hscale n]) hr)
  have hu := (positiveMatrixNormalizer_spec
    (birthResidueScale_posDef (t := birthDyadicShellScale ε n) hG hs)).1
  have hc := commonPhysicalNormalizedWindowFraction_contractive hcap hB L.coe_nonneg
    hm.2.2.2.1
  refine ⟨hu, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2, hc, ?_⟩
  intro e clock hz
  have hmask := D.originalSupportedLeftBirthPhysicalClockWeight_mask_ne_zero
    ε cap' n j i ell _ hz
  exact ⟨(D.originalSupportedLeftBirthPhysicalClockMask_eligible_of_comparison hF hw hG
    hε hcap' hbounds hsmall hgeospan hlower.le hupper.le hcomp n j i ell (hscale n)
    hell e clock hmask).2.2,
    D.originalSupportedLeftBirthPhysicalClockMask_shortLeg_upper_of_comparison hF hw hG
      hε hcap' hbounds hsmall hgeospan hlower.le hupper.le hcomp n j i ell (hscale n)
      hell e clock hmask,
    D.originalSupportedLeftBirthPhysicalClockWeight_clock_witness
      hε hcap' n j i ell _ hz⟩

/-- The same actual right residue yields the reflected windows in the original
forward clock, including their genuine occupied-node eligibility. -/
theorem exists_original_right_supported_contractive_birthWindows_sameResidue
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    (hgap : 0 < gap) {η : ℝ} (hη : 0 < η) (hηspan : η < D.hi - D.lo)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker))
      (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-η) η))
    (hpole : ∀ r ∈ Ioo 0 η,
      originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) :
    ∃ ε : ℝ, 0 < ε ∧ ε < η ∧ ∃ h : ℝ, 0 < h ∧ ∃ B ≥ 0,
      ∃ U : ℝ, 0 < U ∧ ∀ (L : ℝ≥0) (cap : ℝ), 0 < cap →
      let cap' := commonPhysicalNormalizedWindowFraction cap B (L : ℝ)
      ∀ (n j i ell : ℕ), i < dyadicBirthBandCount j →
        ell < birthPhysicalClockWindowCount cap' →
      let T := positiveMatrixNormalizer
        (birthResidueScale G (birthDyadicShellScale ε n) (birthDyadicElapsedScale ε n j))
      let ref := D.originalRightBirthPhysicalClockReference ε cap' n j i ell
      let width := birthPhysicalClockWindowWidth cap' (birthDyadicElapsedScale ε n j)
      let R := originalNormalizedClockMobility S w T ref (-width)
      IsUnit T.det ∧ ref - S.level ∈ Ioo D.lo D.hi ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ref + (-width) * r - S.level ∈ Ioo D.lo D.hi) ∧
        R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ cap' * B) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
          ‖R r - R v‖ ≤ (cap' * B) * |r - v|) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) ∧
        ∀ (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (clock : ℝ),
          D.originalSupportedRightBirthPhysicalClockWeight ε cap' n j i ell
            ((physicalPairAnchor e).2, clock) ≠ 0 →
          e ∈ D.normalizedMomentumPhaseEligibleEdges T (ref - S.level) h ∧
            (U • 1 - T * D.targetPhaseLeg (ref - S.level) e.2.2 * Tᵀ).PosSemidef ∧
            ∃ r ∈ Icc (0 : ℝ) 1, clock = ref + (-width) * r := by
  obtain ⟨geoε, hgeoε, hgeoη, hgeospan, lower, upper, hlower, hupper, hcomp⟩ :=
    D.exists_original_right_birth_comparison_sameResidue hF hw hη hηspan hG hRem hpole
  obtain ⟨B, hB, hmob⟩ := D.original_right_birth_mobility_bound_of_comparison
    hF hw hG hgeospan hupper.le (fun r hr ↦ (hcomp r hr).2)
  obtain ⟨ε, hε, hεgeo, hsmall, hscale⟩ :=
    exists_uniformBirthWindowClockCollar hgeoε hgap
  refine ⟨ε, hε, hεgeo.trans hgeoη, lower / 128, by positivity, B, hB,
    16 * upper, by positivity, ?_⟩
  intro L cap hcap
  let cap' := commonPhysicalNormalizedWindowFraction cap B (L : ℝ)
  have hcap' : 0 < cap' :=
    (commonPhysicalNormalizedWindowFraction_spec hcap hB L.coe_nonneg).1
  dsimp only
  intro n j i ell hi hell
  have ht : 0 < birthDyadicShellScale ε n := birthDyadicShellScale_pos hε n
  have hs : 0 < birthDyadicElapsedScale ε n j :=
    (birthDyadicClockBand_base_bounds hε n j i hi).1
  have hm := D.originalRightBirthPhysicalWindow_mobility_bounds_of_band_bound
    hF hw hε hcap' hgeospan hB n j i ell hi hell (by linarith [hscale n])
    (G := G) (fun r hr ↦ hmob ht hs (by linarith [hscale n]) hr)
  have hu := (positiveMatrixNormalizer_spec
    (birthResidueScale_posDef (t := birthDyadicShellScale ε n) hG hs)).1
  have hc := commonPhysicalNormalizedWindowFraction_contractive hcap hB L.coe_nonneg
    hm.2.2.2.1
  refine ⟨hu, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2, hc, ?_⟩
  intro e clock hz
  have hmask := D.originalSupportedRightBirthPhysicalClockWeight_mask_ne_zero
    ε cap' n j i ell _ hz
  exact ⟨(D.originalSupportedRightBirthPhysicalClockMask_eligible_of_comparison hF hw hG
    hε hcap' hbounds hsmall hgeospan hlower.le hupper.le hcomp n j i ell (hscale n)
    hell e clock hmask).2.2,
    D.originalSupportedRightBirthPhysicalClockMask_shortLeg_upper_of_comparison hF hw hG
      hε hcap' hbounds hsmall hgeospan hlower.le hupper.le hcomp n j i ell (hscale n)
      hell e clock hmask,
    D.originalSupportedRightBirthPhysicalClockWeight_clock_witness
      hε hcap' n j i ell _ hz⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
