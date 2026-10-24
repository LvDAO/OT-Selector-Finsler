import OTSelector.Reconstruction.OriginalRegularBirthEnergy
import OTSelector.MeasureTheory.ClockBandRealEnergyBudget

/-! The scalar regular-birth frame has its actual finite true-Palm momentum
budget from the unchanged original kinetic energy, without a focal residue. -/
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

/-- Original kinetic integrability supplies one real momentum budget valid
for every measurable original paired clock and every disjoint clock-band level. -/
theorem OriginalSeedConditionalMoments.exists_original_regularBirth_clockBand_momentum_budget
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∃ E₀ : ℝ, 1 ≤ E₀ ∧
      ∀ (clock : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) → ℝ), Measurable clock →
      ∀ (a : ℝ) {width : ℝ}, 0 ≤ width → ∀ N : ℕ,
      (∀ i : ℕ, (∫⁻ m in clock ⁻¹' clockGridBand a width i,
        ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞)) ∧
      (∑ i ∈ Finset.range N, (∫⁻ m in clock ⁻¹' clockGridBand a width i,
        ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal) ≤ E₀ := by
  have hIV := (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).2
  let v := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
    ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
  let P := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have hv : (∫⁻ m, v m ∂P) ≠ (∞ : ℝ≥0∞) :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIV.2).ne
  have hv0 : 0 ≤ (∫⁻ m, v m ∂P).toReal := ENNReal.toReal_nonneg
  refine ⟨(∫⁻ m, v m ∂P).toReal + 1, by linarith, ?_⟩
  intro clock hclock a width hwidth N
  have hb := clockGridBand_realEnergy_budget P hclock v hv a hwidth N
  exact ⟨hb.1, hb.2.trans (by linarith)⟩

/-- The actual scalar regular-birth normalized momentum has its real same-band
bound; the original kinetic moment internally ensures that readout is finite. -/
theorem OriginalSeedConditionalMoments.original_regular_birthNormalizer_quadraticMoment_toReal_le
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {s : ℝ} (hs : 0 < s)
    (B : Set (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) :
    (∫⁻ m in B, ENNReal.ofReal
      (‖((positiveMatrixNormalizer (s • (1 : Matrix (Fin (finrank ℝ S.covector.ker))
        (Fin (finrank ℝ S.covector.ker)) ℝ)))ᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m‖ ^ 2)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal ≤
    (s * (finrank ℝ S.covector.ker : ℝ)) *
      (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
        ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law).toReal := by
  have hIV := (D.integrable_original_pair_momentum_of_weighted_stationary hF hw hgap hbounds Q).2
  have hv : (∫⁻ m in B, ENNReal.ofReal (‖originalSeedPairMomentum S w m‖ ^ 2)
      ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hIV.2).ne
      (setLIntegral_le_lintegral _ _)
  have hfin := ENNReal.mul_ne_top
    (ENNReal.ofReal_ne_top (r := s * (finrank ℝ S.covector.ker : ℝ))) hv
  have hr := ENNReal.toReal_mono hfin
    (D.original_regular_birthNormalizer_quadraticMoment_le hF hw Q hs B)
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0 ≤ s * (finrank ℝ S.covector.ker : ℝ) by positivity)] using hr

end OTSelector.Reconstruction
