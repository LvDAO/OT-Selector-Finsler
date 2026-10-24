import OTSelector.Reconstruction.FinslerOriginalBirthSameResidue
import OTSelector.Reconstruction.OriginalFocalResiduePalmEnergy

/-! A residue already fixed by the actual physical pole has its own true-Palm
energy moment. The comparison producer preserves that matrix rather than
selecting a different residue for probability or traffic estimates. -/
open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The chosen actual left pole internally yields integrability of that
same focal energy under the original true Palm and its kinetic budget. -/
theorem OriginalSeedConditionalMoments.original_left_sameResidue_focalEnergy_integrable
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
    (∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      0 ≤ originalSeedLeftPoleEnergy S w D.lo G m) ∧
      Integrable (originalSeedLeftPoleEnergy S w D.lo G)
        (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
      ∃ C : ℝ, 0 < C ∧
        (∫ m, originalSeedLeftPoleEnergy S w D.lo G m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
        C * ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law := by
  obtain ⟨ε, hε, _, hεspan, c, _C, hc, _hC, hcomp⟩ :=
    D.exists_original_left_birth_comparison_sameResidue hF hw hη hηspan hG hRem hpole
  obtain ⟨C, hC, hbound⟩ := D.exists_original_left_residueEnergy_kinetic_bound hF hw
    hgap hbounds hε hεspan hc hG (fun r hr ↦ (hcomp r hr).1)
  obtain ⟨h0, hI, hmean⟩ := D.originalPalm_integrable_of_kinetic_domination Q
    (measurable_originalSeedLeftPoleEnergy hF hw D.lo G) hbound
  exact ⟨h0, hI, C, hC, hmean⟩

/-- The chosen actual right pole internally yields integrability of that
same focal energy under the original true Palm and its kinetic budget. -/
theorem OriginalSeedConditionalMoments.original_right_sameResidue_focalEnergy_integrable
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
    (∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
      0 ≤ originalSeedRightPoleEnergy S w D.hi G m) ∧
      Integrable (originalSeedRightPoleEnergy S w D.hi G)
        (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
      ∃ C : ℝ, 0 < C ∧
        (∫ m, originalSeedRightPoleEnergy S w D.hi G m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
        C * ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law := by
  obtain ⟨ε, hε, _, hεspan, c, _C, hc, _hC, hcomp⟩ :=
    D.exists_original_right_birth_comparison_sameResidue hF hw hη hηspan hG hRem hpole
  obtain ⟨C, hC, hbound⟩ := D.exists_original_right_residueEnergy_kinetic_bound hF hw
    hgap hbounds hε hεspan hc hG (fun r hr ↦ (hcomp r hr).1)
  obtain ⟨h0, hI, hmean⟩ := D.originalPalm_integrable_of_kinetic_domination Q
    (measurable_originalSeedRightPoleEnergy hF hw D.hi G) hbound
  exact ⟨h0, hI, C, hC, hmean⟩

end OTSelector.Reconstruction
