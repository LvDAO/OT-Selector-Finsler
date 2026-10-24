import OTSelector.Reconstruction.OriginalSameResiduePalmEnergy
import OTSelector.MeasureTheory.ClockBandRealEnergyBudget

/-! Every actual endpoint uses one finite original true-Palm energy budget for
all original inward clock-band levels, including reflected right half-open bands. -/
open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The unchanged original left clock and same actual residue share one
finite energy budget across all dyadic levels; no extra energy moment is assumed. -/
theorem OriginalSeedConditionalMoments.exists_original_left_sameResidue_clockBand_energy_budget
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η) (hηspan : η < D.hi - D.lo)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-η) η))
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∃ E₀ : ℝ, 1 ≤ E₀ ∧
      ∀ (a : ℝ) {width : ℝ}, 0 ≤ width → ∀ N : ℕ,
      let clock := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦ m.1.1 - (S.level : ℝ) - D.lo
      let e := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
        ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
      let v := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
        ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
      (∀ i : ℕ,
        (∫⁻ m in clock ⁻¹' clockGridBand a width i, e m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) ∧
        (∫⁻ m in clock ⁻¹' clockGridBand a width i, v m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞)) ∧
      (∑ i ∈ Finset.range N, (∫⁻ m in clock ⁻¹' clockGridBand a width i, e m
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal) ≤ E₀ ∧
      (∑ i ∈ Finset.range N, (∫⁻ m in clock ⁻¹' clockGridBand a width i, v m
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal) ≤ E₀ := by
  have hIE := (D.original_left_sameResidue_focalEnergy_integrable hF hw hη hηspan
    hG hRem hpole hgap hbounds Q).2.1
  have hIV := (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).2
  let e := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
    ENNReal.ofReal (originalSeedLeftPoleEnergy S w D.lo G m)
  let v := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
    ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
  let P := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have he : (∫⁻ m, e m ∂P) ≠ (∞ : ℝ≥0∞) :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIE.2).ne
  have hv : (∫⁻ m, v m ∂P) ≠ (∞ : ℝ≥0∞) :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIV.2).ne
  have he0 : 0 ≤ (∫⁻ m, e m ∂P).toReal := ENNReal.toReal_nonneg
  have hv0 : 0 ≤ (∫⁻ m, v m ∂P).toReal := ENNReal.toReal_nonneg
  refine ⟨(∫⁻ m, e m ∂P).toReal + (∫⁻ m, v m ∂P).toReal + 1, by linarith, ?_⟩
  intro a width hwidth N
  dsimp only
  have hm : Measurable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      m.1.1 - (S.level : ℝ) - D.lo) := (measurable_fst.fst.sub_const _).sub_const _
  have hbe := clockGridBand_realEnergy_budget P hm e he a hwidth N
  have hbv := clockGridBand_realEnergy_budget P hm v hv a hwidth N
  refine ⟨fun i ↦ ⟨hbe.1 i, hbv.1 i⟩, ?_, ?_⟩
  · exact hbe.2.trans (by linarith)
  · exact hbv.2.trans (by linarith)

/-- The unchanged original right clock and same actual residue share one
finite energy budget across all dyadic levels; no extra energy moment is assumed. -/
theorem OriginalSeedConditionalMoments.exists_original_right_sameResidue_clockBand_energy_budget
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {η : ℝ} (hη : 0 < η) (hηspan : η < D.hi - D.lo)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef)
    {Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hRem : ContinuousOn Rem (Ioo (-η) η))
    (hpole : ∀ r ∈ Ioo 0 η, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∃ E₀ : ℝ, 1 ≤ E₀ ∧
      ∀ (a : ℝ) {width : ℝ}, 0 ≤ width → ∀ N : ℕ,
      let clock := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦ D.hi - (m.1.2 - (S.level : ℝ))
      let e := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
        ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
      let v := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
        ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
      (∀ i : ℕ,
        (∫⁻ m in clock ⁻¹' clockGridBand a width i, e m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) ∧
        (∫⁻ m in clock ⁻¹' clockGridBand a width i, v m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞)) ∧
      (∑ i ∈ Finset.range N, (∫⁻ m in clock ⁻¹' clockGridBand a width i, e m
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal) ≤ E₀ ∧
      (∑ i ∈ Finset.range N, (∫⁻ m in clock ⁻¹' clockGridBand a width i, v m
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal) ≤ E₀ := by
  have hIE := (D.original_right_sameResidue_focalEnergy_integrable hF hw hη hηspan
    hG hRem hpole hgap hbounds Q).2.1
  have hIV := (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).2
  let e := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
    ENNReal.ofReal (originalSeedRightPoleEnergy S w D.hi G m)
  let v := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
    ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
  let P := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have he : (∫⁻ m, e m ∂P) ≠ (∞ : ℝ≥0∞) :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIE.2).ne
  have hv : (∫⁻ m, v m ∂P) ≠ (∞ : ℝ≥0∞) :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIV.2).ne
  have he0 : 0 ≤ (∫⁻ m, e m ∂P).toReal := ENNReal.toReal_nonneg
  have hv0 : 0 ≤ (∫⁻ m, v m ∂P).toReal := ENNReal.toReal_nonneg
  refine ⟨(∫⁻ m, e m ∂P).toReal + (∫⁻ m, v m ∂P).toReal + 1, by linarith, ?_⟩
  intro a width hwidth N
  dsimp only
  have hm : Measurable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      D.hi - (m.1.2 - (S.level : ℝ))) := measurable_const.sub (measurable_fst.snd.sub_const _)
  have hbe := clockGridBand_realEnergy_budget P hm e he a hwidth N
  have hbv := clockGridBand_realEnergy_budget P hm v hv a hwidth N
  refine ⟨fun i ↦ ⟨hbe.1 i, hbv.1 i⟩, ?_, ?_⟩
  · exact hbe.2.trans (by linarith)
  · exact hbv.2.trans (by linarith)

end OTSelector.Reconstruction
