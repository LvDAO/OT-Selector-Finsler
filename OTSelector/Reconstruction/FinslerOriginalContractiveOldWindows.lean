import OTSelector.Reconstruction.FinslerOriginalOldWindowEligibility
import OTSelector.Reconstruction.FinslerOriginalOldPhysicalClockWitnesses
import OTSelector.Reconstruction.FinslerOriginalOldPhysicalWindowMobility
import OTSelector.Reconstruction.FinslerOriginalBirthSameResidue
import OTSelector.Reconstruction.CommonPhysicalNormalizedPhaseWindow

/-! Original Finsler pole data produces one old-focal collar and node threshold.
Every finite physical window in its same canonical focal frame has an actual
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
theorem exists_uniformOldFocalWindowClockCollar {geoε gap : ℝ}
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

/-- The same original left residue and ONE h/mobility constant work
for every smaller old-focal collar, permitting all traffic regions to share
one final collar without a new geometric or normalizer choice. -/
theorem exists_original_left_shrinkable_supported_contractive_oldWindows_sameResidue
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
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < η ∧ ∃ h : ℝ, 0 < h ∧ ∃ B ≥ 0,
      ∀ {ε : ℝ}, 0 < ε → ε < ε₀ → ∀ (L : ℝ≥0) (cap : ℝ), 0 < cap →
      let cap' := commonPhysicalNormalizedWindowFraction (min cap (1 / 4)) B (L : ℝ)
      ∀ (n ell : ℕ),
        ell < birthPhysicalClockWindowCount cap' →
      let T := positiveMatrixNormalizer
        (focalResidueScale G (birthDyadicShellScale ε n))
      let ref := D.originalOldPhysicalClockReference ε cap' 0 n ell
      let width := oldPhysicalClockWindowWidth cap' (birthDyadicShellScale ε n)
      let R := originalNormalizedClockMobility S w T ref width
      IsUnit T.det ∧ ref - S.level ∈ Ioo D.lo D.hi ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ref + width * r - S.level ∈ Ioo D.lo D.hi) ∧
        R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ cap' * B) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
          ‖R r - R v‖ ≤ (cap' * B) * |r - v|) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) ∧
        ∀ (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (clock : ℝ),
          D.originalSupportedOldPhysicalClockWeight ε cap' 0 n ell
            ((physicalPairAnchor e).2, clock) ≠ 0 →
          e ∈ D.normalizedMomentumPhaseEligibleEdges T (ref - S.level) h ∧
            ∃ r ∈ Icc (0 : ℝ) 1, clock = ref + width * r := by
  obtain ⟨geoε, hgeoε, hgeoη, hgeospan, lower, upper, hlower, hupper, hcomp⟩ :=
    D.exists_original_left_birth_comparison_sameResidue hF hw hη hηspan hG hRem hpole
  obtain ⟨B, hB, hmob⟩ := D.original_left_birth_mobility_bound_of_comparison
    hF hw hG hgeospan hupper.le (fun r hr ↦ (hcomp r hr).2)
  let ε₀:=min (geoε/8) (gap/8)
  have hε₀:0<ε₀:=lt_min (by positivity) (by positivity)
  have hε₀geo:ε₀≤geoε/8:=min_le_left _ _
  have hε₀gap:ε₀≤gap/8:=min_le_right _ _
  refine ⟨ε₀,hε₀,(lt_of_lt_of_le (by linarith) hgeoη.le),lower/64,by positivity,B,hB,?_⟩
  intro ε hε hεsmall L cap hcap
  have hsmall:8*ε≤gap:=by linarith [hεsmall.le.trans hε₀gap]
  have hscale:∀n:ℕ,8*birthDyadicShellScale ε n<geoε:=by
    intro n
    have htwo:2*birthDyadicShellScale ε n≤ε:=by
      rw [two_mul_birthDyadicShellScale]
      exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
    linarith [hεsmall.trans_le hε₀geo]
  let cap' := commonPhysicalNormalizedWindowFraction (min cap (1 / 4)) B (L : ℝ)
  have hbasecap : 0 < min cap (1 / 4 : ℝ) := lt_min hcap (by norm_num)
  have hcap' : 0 < cap' :=
    (commonPhysicalNormalizedWindowFraction_spec hbasecap hB L.coe_nonneg).1
  have hcapU : cap' ≤ 1 / 4 :=
    (commonPhysicalNormalizedWindowFraction_le_cap _ _ _).trans (min_le_right _ _)
  dsimp only
  intro n ell hell
  have ht : 0 < birthDyadicShellScale ε n := birthDyadicShellScale_pos hε n
  have hm := D.originalLeftOldPhysicalWindow_mobility_bounds_of_band_bound
    hF hw hε hcap' hgeospan hB n ell hell (by linarith [hscale n])
    (G := G) (fun r hr ↦ by
      simpa only [birthResidueScale_same_time_eq_focal G ht] using
        hmob (s := birthDyadicShellScale ε n) ht ht (by linarith [hscale n]) hr)
  have hu := (positiveMatrixNormalizer_spec (focalResidueScale_posDef hG ht)).1
  have hc := commonPhysicalNormalizedWindowFraction_contractive hbasecap hB L.coe_nonneg
    hm.2.2.2.1
  refine ⟨hu, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2, hc, ?_⟩
  intro e clock hz
  exact ⟨(D.originalSupportedLeftOldPhysicalClockWeight_eligible_of_comparison hF hw hG
    hε hcap' hcapU hbounds hsmall hgeospan hlower.le hupper.le hcomp n ell (hscale n)
    hell e clock hz).2.2,
    D.originalSupportedLeftOldPhysicalClockWeight_clock_witness hε hcap' n ell _ hz⟩


/-- The same original left residue produces actual eligible and contractive
old-focal windows at every dyadic scale, with no window eligibility oracle. -/
theorem exists_original_left_supported_contractive_oldWindows_sameResidue
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
      ∀ (L : ℝ≥0) (cap : ℝ), 0 < cap →
      let cap' := commonPhysicalNormalizedWindowFraction (min cap (1 / 4)) B (L : ℝ)
      ∀ (n ell : ℕ),
        ell < birthPhysicalClockWindowCount cap' →
      let T := positiveMatrixNormalizer
        (focalResidueScale G (birthDyadicShellScale ε n))
      let ref := D.originalOldPhysicalClockReference ε cap' 0 n ell
      let width := oldPhysicalClockWindowWidth cap' (birthDyadicShellScale ε n)
      let R := originalNormalizedClockMobility S w T ref width
      IsUnit T.det ∧ ref - S.level ∈ Ioo D.lo D.hi ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ref + width * r - S.level ∈ Ioo D.lo D.hi) ∧
        R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ cap' * B) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
          ‖R r - R v‖ ≤ (cap' * B) * |r - v|) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) ∧
        ∀ (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (clock : ℝ),
          D.originalSupportedOldPhysicalClockWeight ε cap' 0 n ell
            ((physicalPairAnchor e).2, clock) ≠ 0 →
          e ∈ D.normalizedMomentumPhaseEligibleEdges T (ref - S.level) h ∧
            ∃ r ∈ Icc (0 : ℝ) 1, clock = ref + width * r := by
  obtain ⟨ε₀,hε₀,hε₀η,h,hh,B,hB,hall⟩:=
    D.exists_original_left_shrinkable_supported_contractive_oldWindows_sameResidue hF hw hbounds hgap hη hηspan hG hRem hpole
  have hε:0<ε₀/2:=by positivity
  have hεsmall:ε₀/2<ε₀:=by linarith
  refine ⟨ε₀/2,hε,hεsmall.trans hε₀η,h,hh,B,hB,?_⟩
  exact hall hε hεsmall

/-- The same original right residue and ONE h/mobility constant work
for every smaller old-focal collar, permitting all traffic regions to share
one final collar without a new geometric or normalizer choice. -/
theorem exists_original_right_shrinkable_supported_contractive_oldWindows_sameResidue
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
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < η ∧ ∃ h : ℝ, 0 < h ∧ ∃ B ≥ 0,
      ∀ {ε : ℝ}, 0 < ε → ε < ε₀ → ∀ (L : ℝ≥0) (cap : ℝ), 0 < cap →
      let cap' := commonPhysicalNormalizedWindowFraction (min cap (1 / 4)) B (L : ℝ)
      ∀ (n ell : ℕ),
        ell < birthPhysicalClockWindowCount cap' →
      let T := positiveMatrixNormalizer
        (focalResidueScale G (birthDyadicShellScale ε n))
      let ref := D.originalOldPhysicalClockReference ε cap' 1 n ell
      let width := oldPhysicalClockWindowWidth cap' (birthDyadicShellScale ε n)
      let R := originalNormalizedClockMobility S w T ref (-width)
      IsUnit T.det ∧ ref - S.level ∈ Ioo D.lo D.hi ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ref + (-width) * r - S.level ∈ Ioo D.lo D.hi) ∧
        R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ cap' * B) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
          ‖R r - R v‖ ≤ (cap' * B) * |r - v|) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) ∧
        ∀ (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (clock : ℝ),
          D.originalSupportedOldPhysicalClockWeight ε cap' 1 n ell
            ((physicalPairAnchor e).2, clock) ≠ 0 →
          e ∈ D.normalizedMomentumPhaseEligibleEdges T (ref - S.level) h ∧
            ∃ r ∈ Icc (0 : ℝ) 1, clock = ref + (-width) * r := by
  obtain ⟨geoε, hgeoε, hgeoη, hgeospan, lower, upper, hlower, hupper, hcomp⟩ :=
    D.exists_original_right_birth_comparison_sameResidue hF hw hη hηspan hG hRem hpole
  obtain ⟨B, hB, hmob⟩ := D.original_right_birth_mobility_bound_of_comparison
    hF hw hG hgeospan hupper.le (fun r hr ↦ (hcomp r hr).2)
  let ε₀:=min (geoε/8) (gap/8)
  have hε₀:0<ε₀:=lt_min (by positivity) (by positivity)
  have hε₀geo:ε₀≤geoε/8:=min_le_left _ _
  have hε₀gap:ε₀≤gap/8:=min_le_right _ _
  refine ⟨ε₀,hε₀,(lt_of_lt_of_le (by linarith) hgeoη.le),lower/64,by positivity,B,hB,?_⟩
  intro ε hε hεsmall L cap hcap
  have hsmall:8*ε≤gap:=by linarith [hεsmall.le.trans hε₀gap]
  have hscale:∀n:ℕ,8*birthDyadicShellScale ε n<geoε:=by
    intro n
    have htwo:2*birthDyadicShellScale ε n≤ε:=by
      rw [two_mul_birthDyadicShellScale]
      exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
    linarith [hεsmall.trans_le hε₀geo]
  let cap' := commonPhysicalNormalizedWindowFraction (min cap (1 / 4)) B (L : ℝ)
  have hbasecap : 0 < min cap (1 / 4 : ℝ) := lt_min hcap (by norm_num)
  have hcap' : 0 < cap' :=
    (commonPhysicalNormalizedWindowFraction_spec hbasecap hB L.coe_nonneg).1
  have hcapU : cap' ≤ 1 / 4 :=
    (commonPhysicalNormalizedWindowFraction_le_cap _ _ _).trans (min_le_right _ _)
  dsimp only
  intro n ell hell
  have ht : 0 < birthDyadicShellScale ε n := birthDyadicShellScale_pos hε n
  have hm := D.originalRightOldPhysicalWindow_mobility_bounds_of_band_bound
    hF hw hε hcap' hgeospan hB n ell hell (by linarith [hscale n])
    (G := G) (fun r hr ↦ by
      simpa only [birthResidueScale_same_time_eq_focal G ht] using
        hmob (s := birthDyadicShellScale ε n) ht ht (by linarith [hscale n]) hr)
  have hu := (positiveMatrixNormalizer_spec (focalResidueScale_posDef hG ht)).1
  have hc := commonPhysicalNormalizedWindowFraction_contractive hbasecap hB L.coe_nonneg
    hm.2.2.2.1
  refine ⟨hu, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2, hc, ?_⟩
  intro e clock hz
  exact ⟨(D.originalSupportedRightOldPhysicalClockWeight_eligible_of_comparison hF hw hG
    hε hcap' hcapU hbounds hsmall hgeospan hlower.le hupper.le hcomp n ell (hscale n)
    hell e clock hz).2.2,
    D.originalSupportedRightOldPhysicalClockWeight_clock_witness hε hcap' n ell _ hz⟩

/-- The same actual right residue yields the reflected windows in the original
forward clock, including their genuine occupied-node eligibility. -/
theorem exists_original_right_supported_contractive_oldWindows_sameResidue
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
      ∀ (L : ℝ≥0) (cap : ℝ), 0 < cap →
      let cap' := commonPhysicalNormalizedWindowFraction (min cap (1 / 4)) B (L : ℝ)
      ∀ (n ell : ℕ),
        ell < birthPhysicalClockWindowCount cap' →
      let T := positiveMatrixNormalizer
        (focalResidueScale G (birthDyadicShellScale ε n))
      let ref := D.originalOldPhysicalClockReference ε cap' 1 n ell
      let width := oldPhysicalClockWindowWidth cap' (birthDyadicShellScale ε n)
      let R := originalNormalizedClockMobility S w T ref (-width)
      IsUnit T.det ∧ ref - S.level ∈ Ioo D.lo D.hi ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ref + (-width) * r - S.level ∈ Ioo D.lo D.hi) ∧
        R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ cap' * B) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
          ‖R r - R v‖ ≤ (cap' * B) * |r - v|) ∧
        (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ)) ∧
        ∀ (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (clock : ℝ),
          D.originalSupportedOldPhysicalClockWeight ε cap' 1 n ell
            ((physicalPairAnchor e).2, clock) ≠ 0 →
          e ∈ D.normalizedMomentumPhaseEligibleEdges T (ref - S.level) h ∧
            ∃ r ∈ Icc (0 : ℝ) 1, clock = ref + (-width) * r := by
  obtain ⟨ε₀,hε₀,hε₀η,h,hh,B,hB,hall⟩:=
    D.exists_original_right_shrinkable_supported_contractive_oldWindows_sameResidue hF hw hbounds hgap hη hηspan hG hRem hpole
  have hε:0<ε₀/2:=by positivity
  have hεsmall:ε₀/2<ε₀:=by linarith
  refine ⟨ε₀/2,hε,hεsmall.trans hε₀η,h,hh,B,hB,?_⟩
  exact hall hε hεsmall


end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
