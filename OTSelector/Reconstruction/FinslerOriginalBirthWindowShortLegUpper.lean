import OTSelector.Reconstruction.FinslerOriginalBirthWindowEligibility

/-! Actual supported birth windows retain the uniform upper bound on the
short original phase leg in the same canonical birth frame. -/
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

/-- The literal supported left window keeps its short-leg upper bound. -/
theorem originalSupportedLeftBirthPhysicalClockMask_shortLeg_upper_of_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef) {ε cap geoε lower upper gap diameter : ℝ}
    (hε : 0 < ε) (hcap : 0 < cap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hsmall : 8 * ε ≤ gap)
    (hgeo : geoε < D.hi - D.lo) (hlower : 0 ≤ lower) (hupper : 0 ≤ upper)
    (hcomp : ∀ v ∈ Ioo 0 geoε,
      (originalSeedKernel S w (D.lo + v) - lower • ((v ^ 2)⁻¹ • G + 1)).PosSemidef ∧
      (upper • ((v ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.lo + v)).PosSemidef)
    (n j i ell : ℕ) (hscale : 8 * birthDyadicShellScale ε n < geoε)
    (hell : ell < birthPhysicalClockWindowCount cap)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (clock : ℝ)
    (hz : D.originalSupportedLeftBirthPhysicalClockMask ε cap n j i ell
      ((physicalPairAnchor e).2, clock) ≠ 0) :
    let T := positiveMatrixNormalizer
      (birthResidueScale G (birthDyadicShellScale ε n) (birthDyadicElapsedScale ε n j))
    let cut := D.originalLeftBirthPhysicalClockReference ε cap n j i ell - S.level
    ((16 * upper) • 1 - T * D.sourcePhaseLeg cut e.1.2 * Tᵀ).PosSemidef := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let ref := D.originalLeftBirthPhysicalClockReference ε cap n j i ell
  let T := positiveMatrixNormalizer (birthResidueScale G t s)
  rcases D.originalSupportedLeftBirthPhysicalClockMask_normalizedLegs_clock_bounds
    hε hcap hbounds hsmall n j i ell ((physicalPairAnchor e).2, clock) hz hell with
      ⟨ht, hs, hst, ha, har, hr, hlenL, hlenU, hb, hfar⟩
  have hleg := D.original_left_birth_normalizedLegs_of_comparison hF hw hG hgeo
    hlower hupper hcomp ht hs hst hscale ha har hr
    (α := (1 / 2 : ℝ)) (β := (4 : ℝ)) (by linarith) hlenU hb hfar
  have haeq : (S.level : ℝ) + D.lo +
      (e.1.2 - S.level - D.lo) = e.1.2 := by ring
  have hreq : (S.level : ℝ) + D.lo + (ref - S.level - D.lo) = ref := by ring
  change IsUnit T.det ∧
    (T * originalSeedClockCompliance S w
      ((S.level : ℝ) + D.lo + (e.1.2 - S.level - D.lo))
      ((S.level : ℝ) + D.lo + (ref - S.level - D.lo)) * Tᵀ -
        (lower * (1 / 2) / 16) • 1).PosSemidef ∧
    ((4 * upper * 4) • 1 - T * originalSeedClockCompliance S w
      ((S.level : ℝ) + D.lo + (e.1.2 - S.level - D.lo))
      ((S.level : ℝ) + D.lo + (ref - S.level - D.lo)) * Tᵀ).PosSemidef ∧
    (T * originalSeedClockCompliance S w
      ((S.level : ℝ) + D.lo + (ref - S.level - D.lo)) e.2.2 * Tᵀ -
        (lower / 8) • 1).PosSemidef at hleg
  rw [haeq, hreq] at hleg
  have he := D.originalSupportedLeftBirthPhysicalClockMask_eligible_of_comparison
    hF hw hG hε hcap hbounds hsmall hgeo hlower hupper hcomp n j i ell hscale hell e clock hz
  have hshort := hleg.2.2.1
  rw [show 4 * upper * 4 = 16 * upper by ring] at hshort
  simpa only [sourcePhaseLeg, indicator_of_mem he.2.2.1, originalSeedClockCompliance] using hshort


/-- The literal supported right window keeps its short-leg upper bound. -/
theorem originalSupportedRightBirthPhysicalClockMask_shortLeg_upper_of_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef) {ε cap geoε lower upper gap diameter : ℝ}
    (hε : 0 < ε) (hcap : 0 < cap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hsmall : 8 * ε ≤ gap)
    (hgeo : geoε < D.hi - D.lo) (hlower : 0 ≤ lower) (hupper : 0 ≤ upper)
    (hcomp : ∀ v ∈ Ioo 0 geoε,
      (originalSeedKernel S w (D.hi - v) - lower • ((v ^ 2)⁻¹ • G + 1)).PosSemidef ∧
      (upper • ((v ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.hi - v)).PosSemidef)
    (n j i ell : ℕ) (hscale : 8 * birthDyadicShellScale ε n < geoε)
    (hell : ell < birthPhysicalClockWindowCount cap)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (clock : ℝ)
    (hz : D.originalSupportedRightBirthPhysicalClockMask ε cap n j i ell
      ((physicalPairAnchor e).2, clock) ≠ 0) :
    let T := positiveMatrixNormalizer
      (birthResidueScale G (birthDyadicShellScale ε n) (birthDyadicElapsedScale ε n j))
    let cut := D.originalRightBirthPhysicalClockReference ε cap n j i ell - S.level
    ((16 * upper) • 1 - T * D.targetPhaseLeg cut e.2.2 * Tᵀ).PosSemidef := by
  let t := birthDyadicShellScale ε n
  let s := birthDyadicElapsedScale ε n j
  let ref := D.originalRightBirthPhysicalClockReference ε cap n j i ell
  let T := positiveMatrixNormalizer (birthResidueScale G t s)
  rcases D.originalSupportedRightBirthPhysicalClockMask_normalizedLegs_clock_bounds
    hε hcap hbounds hsmall n j i ell ((physicalPairAnchor e).2, clock) hz hell with
      ⟨ht, hs, hst, ha, har, hr, hlenL, hlenU, hb, hfar⟩
  have hleg := D.original_right_birth_normalizedLegs_of_comparison hF hw hG hgeo
    hlower hupper hcomp ht hs hst hscale ha har hr
    (α := (1 / 2 : ℝ)) (β := (4 : ℝ)) (by linarith) hlenU hb hfar
  have haeq : (S.level : ℝ) + D.hi -
      (D.hi - (e.2.2 - S.level)) = e.2.2 := by ring
  have hreq : (S.level : ℝ) + D.hi - (D.hi - (ref - S.level)) = ref := by ring
  change IsUnit T.det ∧
    (T * originalSeedClockCompliance S w
      ((S.level : ℝ) + D.hi - (D.hi - (ref - S.level)))
      ((S.level : ℝ) + D.hi - (D.hi - (e.2.2 - S.level))) * Tᵀ -
        (lower * (1 / 2) / 16) • 1).PosSemidef ∧
    ((4 * upper * 4) • 1 - T * originalSeedClockCompliance S w
      ((S.level : ℝ) + D.hi - (D.hi - (ref - S.level)))
      ((S.level : ℝ) + D.hi - (D.hi - (e.2.2 - S.level))) * Tᵀ).PosSemidef ∧
    (T * originalSeedClockCompliance S w e.1.2
      ((S.level : ℝ) + D.hi - (D.hi - (ref - S.level))) * Tᵀ -
        (lower / 8) • 1).PosSemidef at hleg
  rw [haeq, hreq] at hleg
  have he := D.originalSupportedRightBirthPhysicalClockMask_eligible_of_comparison
    hF hw hG hε hcap hbounds hsmall hgeo hlower hupper hcomp n j i ell hscale hell e clock hz
  have hshort := hleg.2.2.1
  rw [show 4 * upper * 4 = 16 * upper by ring] at hshort
  simpa only [targetPhaseLeg, indicator_of_mem he.2.2.2.1, originalSeedClockCompliance] using hshort

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
