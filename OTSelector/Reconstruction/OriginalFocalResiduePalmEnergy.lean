import OTSelector.Reconstruction.OriginalFocalResidueGlobalEnergy

/-! The original kinetic moment produces the actual same-residue endpoint energy
moments under the true Palm law, with no extra focal-energy moment premise. -/
open Set Function Matrix Module Manifold MeasureTheory
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

omit [BorelSpace E] in
/-- The actual original support and forward-clock fields transfer a pointwise
kinetic bound to integrability and an expectation bound under the same true Palm. -/
theorem OriginalSeedConditionalMoments.originalPalm_integrable_of_kinetic_domination
    (D : OriginalSeedConditionalMoments S w μ ν)
    {gap : ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {e : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) → ℝ} (he : Measurable e)
    {C : ℝ}
    (hbound : ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      (m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support) →
      (m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support) → m.1.1 < m.1.2 →
      0 ≤ e m ∧ e m ≤ C * D.originalFocalKinetic gap m.1.1 m.1.2 m.2) :
    (∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law, 0 ≤ e m) ∧
      Integrable e (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
      (∫ m, e m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
        C * ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law := by
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  have hs : ∀ᵐ m ∂η, m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support := by
    have h : ∀ᵐ a ∂μ, a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support :=
      D.support.source.ae_open.and μ.support_mem_ae
    have hmap : ∀ᵐ a ∂η.map (fun m ↦ m.1.1),
        a - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ a ∈ μ.support := by
      simpa only [η, Q.source_clock] using h
    exact ae_of_ae_map measurable_fst.fst.aemeasurable hmap
  have ht : ∀ᵐ m ∂η, m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support := by
    have h : ∀ᵐ b ∂ν, b - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ b ∈ ν.support :=
      D.support.target.ae_open.and ν.support_mem_ae
    have hmap : ∀ᵐ b ∂η.map (fun m ↦ m.1.2),
        b - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ b ∈ ν.support := by
      simpa only [η, Q.target_clock] using h
    exact ae_of_ae_map measurable_fst.snd.aemeasurable hmap
  have haebound : ∀ᵐ m ∂η, 0 ≤ e m ∧ e m ≤ C * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 := by
    filter_upwards [hs, ht, Q.ae_palm_forward] with m hms hmt hmf
    exact hbound m hms hmt hmf
  have hI : Integrable e η := by
    apply (Q.kinetic_integrable.const_mul C).mono' he.aestronglyMeasurable
    filter_upwards [haebound] with m hm
    simpa only [Real.norm_eq_abs, abs_of_nonneg hm.1] using hm.2
  refine ⟨haebound.mono (fun _ h ↦ h.1), hI, ?_⟩
  calc
    _ ≤ ∫ m, C * D.originalFocalKinetic gap m.1.1 m.1.2 m.2 ∂η :=
      integral_mono_ae hI (Q.kinetic_integrable.const_mul C) (haebound.mono fun _ h ↦ h.2)
    _ = _ := integral_const_mul _ _

/-- The original left pole and its actual true-Palm residue energy moment are
produced together from the original geometry and kinetic moment. -/
theorem OriginalSeedConditionalMoments.exists_original_left_pole_and_focalEnergy_integrable
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∃ ε : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      G.PosSemidef ∧ ContDiffOn ℝ ∞ Rem (Ioo (-ε) ε) ∧
      (∀ r ∈ Ioo 0 ε, originalSeedKernel S w (D.lo + r) = (r ^ 2)⁻¹ • G + Rem r) ∧
      ∃ C : ℝ, 0 < C ∧
        (∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
          (m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support) →
          (m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support) → m.1.1 < m.1.2 →
          0 ≤ originalSeedLeftPoleEnergy S w D.lo G m ∧
            originalSeedLeftPoleEnergy S w D.lo G m ≤ C * D.originalFocalKinetic gap m.1.1 m.1.2 m.2) ∧
        (∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
          0 ≤ originalSeedLeftPoleEnergy S w D.lo G m) ∧
        Integrable (originalSeedLeftPoleEnergy S w D.lo G)
          (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
        (∫ m, originalSeedLeftPoleEnergy S w D.lo G m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
          C * ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law := by
  obtain ⟨ε, hε, hεh, G, Rem, hG, hRem, hpole, c, hc, C₀, hC₀, hcomp⟩ :=
    D.exists_original_kernel_left_pole_loewner_comparison hF hw
  obtain ⟨C, hC, hpoint⟩ := D.exists_original_left_residueEnergy_kinetic_bound
    hF hw hgap hbounds hε hεh hc hG (fun r hr ↦ (hcomp r hr).1)
  have hm := D.originalPalm_integrable_of_kinetic_domination Q
    (measurable_originalSeedLeftPoleEnergy hF hw D.lo G) hpoint
  exact ⟨ε, hε, hεh, G, Rem, hG, hRem, hpole, C, hC, hpoint, hm⟩

/-- The original right pole and its actual true-Palm residue energy moment are
produced together from the original geometry and kinetic moment. -/
theorem OriginalSeedConditionalMoments.exists_original_right_pole_and_focalEnergy_integrable
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∃ ε : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧
      ∃ (G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
        (Rem : ℝ → Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ),
      G.PosSemidef ∧ ContDiffOn ℝ ∞ Rem (Ioo (-ε) ε) ∧
      (∀ r ∈ Ioo 0 ε, originalSeedKernel S w (D.hi - r) = (r ^ 2)⁻¹ • G + Rem r) ∧
      ∃ C : ℝ, 0 < C ∧
        (∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
          (m.1.1 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.1 ∈ μ.support) →
          (m.1.2 - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧ m.1.2 ∈ ν.support) → m.1.1 < m.1.2 →
          0 ≤ originalSeedRightPoleEnergy S w D.hi G m ∧
            originalSeedRightPoleEnergy S w D.hi G m ≤ C * D.originalFocalKinetic gap m.1.1 m.1.2 m.2) ∧
        (∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law,
          0 ≤ originalSeedRightPoleEnergy S w D.hi G m) ∧
        Integrable (originalSeedRightPoleEnergy S w D.hi G)
          (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ∧
        (∫ m, originalSeedRightPoleEnergy S w D.hi G m
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) ≤
          C * ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
            ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law := by
  obtain ⟨ε, hε, hεh, G, Rem, hG, hRem, hpole, c, hc, C₀, hC₀, hcomp⟩ :=
    D.exists_original_kernel_right_pole_loewner_comparison hF hw
  obtain ⟨C, hC, hpoint⟩ := D.exists_original_right_residueEnergy_kinetic_bound
    hF hw hgap hbounds hε hεh hc hG (fun r hr ↦ (hcomp r hr).1)
  have hm := D.originalPalm_integrable_of_kinetic_domination Q
    (measurable_originalSeedRightPoleEnergy hF hw D.hi G) hpoint
  exact ⟨ε, hε, hεh, G, Rem, hG, hRem, hpole, C, hC, hpoint, hm⟩

end OTSelector.Reconstruction
