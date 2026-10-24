import OTSelector.Reconstruction.OriginalIIDShiftedTiltLocalReadout
import OTSelector.Reconstruction.OriginalIIDActualClockCutoffLoss

/-!
# Actual full-clock raw Palm data on an original Haar core

The old Haar core's original moment witness gives nonnegative full inverse-
compliance energy on the unchanged raw candidate. The genuine matching
profile supplies its clocks and forwardness. Its joint root/Palm mass is
exactly the original retained label mass, and the bounded signed probe shift
is nonnegative on that same joint law.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure]
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

omit [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure] in
/-- The old Haar core itself supplies the original full-clock moment witness;
no local Taylor core or desired kinetic nonnegativity is assumed. -/
theorem PopulationHaarPressureCore.ae_fixed_raw_macro_kinetic_nonneg
    (D : PopulationHaarPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count) {z : ℚ → M}
    (hz : z ∈ (D.continuous.coefficient i).roots)
    (ρ : Measure (PhysicalPairPalmMark (Fin (finrank ℝ
      (P (D.continuous.coefficient i).seedIndex).seed.covector.ker)))) (θ : ℝ)
    (hsource : ρ.map (fun m ↦ m.1.1) = ENNReal.ofReal θ • condDistrib u a μ z)
    (htarget : ρ.map (fun m ↦ m.1.2) = ENNReal.ofReal θ • condDistrib u a ν z)
    (hforward : ∀ᵐ m ∂ρ, m.1.1 < m.1.2) :
    ∀ᵐ m ∂ρ, 0 ≤ matrixQuadratic
      (physicalSceneOriginalMacroCoefficient (P := P) (a := a)
        (D.continuous.coefficient i).seedIndex
          (physicalSceneOriginalMacroLabel (P := P) (a := a)
            (D.continuous.coefficient i).seedIndex z,m.1)) m.2 := by
  let _haarRawMetric : MetricSpace M := F.metricSpace
  let _haarRawProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _haarRawPolish : PolishSpace M := inferInstance
  let _haarRawBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.continuous.coefficient i
  have hroot : z ∈ D.continuous.population.roots := by
    rw [← D.continuous.union_eq]
    exact mem_iUnion.mpr ⟨i,hz⟩
  have hpiece := C.roots_subset_piece hz
  obtain ⟨mom⟩ := ((D.continuous.population.good z hroot).2 C.seedIndex hpiece).1
  have hnonneg := mom.ae_raw_kinetic_nonneg_of_clock_marginals hF
    (populationSeedPieceLabel P a κ lambda C.seedIndex ⟨z,hpiece⟩).property
    ρ θ hsource htarget hforward
  filter_upwards [hnonneg] with m hm
  change 0 ≤ matrixQuadratic (populationSeedRootCoefficient (P C.seedIndex).seed a
    (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker)
    (physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex
      (physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex z),m.1)) m.2
  rw [physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj C.seedIndex hpiece,
    populationSeedRootCoefficient_eq_pieceCoefficient P a κ lambda
      hF hcomplete hu ha hinj C.seedIndex hpiece m.1]
  exact hm

omit [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] in
/-- Genuine original matching data supply full-clock raw kinetic nonnegativity
for this same old Haar core, without requesting Palm marginal or forward fields. -/
theorem PopulationHaarPressureCore.ae_originalIID_fixed_candidate_full_clock_kinetic_nonneg
    (D : PopulationHaarPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let label := physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex
    let K := label '' C.roots
    let ref := fun c : Fin q → ℝ ↦ a (S.curve
      ((Module.finBasis ℝ S.covector.ker).equivFunL.symm c) 0)
    let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex
    ∀ (Λ : Kernel (Fin q → ℝ) (OriginalIIDMaskedMacroInputScene (Fin q)))
      (gap : ℝ), 0 < gap →
    ∀ input : (Fin q → ℝ) → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)),
    (∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c)) →
    ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      ∀ᵐ mark ∂originalIIDRawPairPalmKernel Λ c,
        0 ≤ matrixQuadratic (physicalSceneOriginalMacroCoefficient
          (P := P) (a := a) C.seedIndex (c,mark.1)) mark.2 := by
  let _haarRawMetric : MetricSpace M := F.metricSpace
  let _haarRawProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _haarRawPolish : PolishSpace M := inferInstance
  let _haarRawBorel : BorelSpace (ℚ → M) := inferInstance
  intro C S q label K ref root Λ gap hgap input hprofile
  have hlabel : ContinuousOn label C.roots := by
    apply (Module.finBasis ℝ S.covector.ker).equivFunL.continuous.comp_continuousOn
    have hc := (D.intensity i).continuous_label
    rwa [D.intensity_roots i] at hc
  have hK : MeasurableSet K := (C.roots_compact.image_of_continuousOn hlabel).measurableSet
  filter_upwards [hprofile,ae_restrict_mem hK] with c hc hcK
  obtain ⟨z,hz,rfl⟩ := hcK
  have hr : root (label z) = z := physicalSceneOriginalMacroRootValue_at_label
    hF hcomplete hu ha hinj C.seedIndex (C.roots_subset_piece hz)
  let θ := originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref (label z))
  have hθ : 0 ≤ θ := mul_nonneg (NNReal.coe_nonneg _)
    (populationAtlasTheta_nonneg P a κ lambda C.seedIndex (ref (label z)))
  let : IsProbabilityMeasure (Λ (label z)) := hc.1
  have hraw := original_raw_campbell_of_stationary_full_input_profile q θ hθ
    (condDistrib u a μ (root (label z))) (condDistrib u a ν (root (label z))) (Λ (label z))
    hc.2.2.1 (hc.2.2.2.2.2.mono fun scene hs ↦ hs.2.1) hc.2.2.2.1
  have hforward := ae_original_raw_palm_forward_of_matching_profile q gap θ hgap
    (condDistrib u a μ (root (label z))) (condDistrib u a ν (root (label z)))
    (input (label z)) (Λ (label z)) hc
  have hs := hraw.2.2.2.1
  have ht := hraw.2.2.2.2
  rw [hr] at hs ht
  simpa only [originalIIDRawPairPalmKernel_apply,label] using
    D.ae_fixed_raw_macro_kinetic_nonneg hF hcomplete hu ha hinj i hz
      (cubePalm (Fin q) (physicalScenePairCampbell ((Λ (label z)).map Prod.fst))) θ hs ht hforward

/-- The same original root/Palm joint law has its exact original label mass,
is finite, and carries nonnegative full raw matrix and shifted tilted energy.
All clock facts come from the actual profile; no energy/Palm callback is added. -/
theorem PopulationHaarPressureCore.fixed_candidate_raw_joint_data
    (D : PopulationHaarPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.continuous.count) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let label := physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex
    let K := label '' C.roots
    let ref := fun c : Fin q → ℝ ↦ a (S.curve
      ((Module.finBasis ℝ S.covector.ker).equivFunL.symm c) 0)
    let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex
    ∀ (Λ : Kernel (Fin q → ℝ) (OriginalIIDMaskedMacroInputScene (Fin q)))
      (_hΛ : IsSFiniteKernel Λ) (gap : ℝ), 0 < gap →
    ∀ input : (Fin q → ℝ) → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)),
    (∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c)) →
    let joint := ((volume : Measure (Fin q → ℝ)).restrict K) ⊗ₘ originalIIDRawPairPalmKernel Λ
    joint univ = lambda C.roots ∧ IsFiniteMeasure joint ∧
      (∀ᵐ p ∂joint, 0 ≤ matrixQuadratic (physicalSceneOriginalMacroCoefficient
        (P := P) (a := a) C.seedIndex (p.1,p.2.1)) p.2.2) ∧
      ∀ (g : (M × M) →ᵇ ℝ) (t : ℝ), ∀ᵐ p ∂joint,
        0 ≤ physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) C.seedIndex g t p := by
  let _haarRawMetric : MetricSpace M := F.metricSpace
  let _haarRawProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _haarRawPolish : PolishSpace M := inferInstance
  let _haarRawBorel : BorelSpace (ℚ → M) := inferInstance
  intro C S q label K ref root Λ hΛ gap hgap input hprofile joint
  let := hΛ
  have hlabel : ContinuousOn label C.roots := by
    apply (Module.finBasis ℝ S.covector.ker).equivFunL.continuous.comp_continuousOn
    have hc := (D.intensity i).continuous_label
    rwa [D.intensity_roots i] at hc
  have hK : MeasurableSet K := (C.roots_compact.image_of_continuousOn hlabel).measurableSet
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let R := populationSeedRootLabelValue S a
  have hKeq : e '' (R '' C.roots) = K := by
    simp only [K,label,physicalSceneOriginalMacroLabel,image_image]
    rfl
  have hp : ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict (e '' (R '' C.roots)),
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c) := by
    rwa [hKeq]
  have hm := D.fixed_candidate_raw_palm_mass_eq_label hF hcomplete hu ha hinj i
    Λ gap (fun c ↦ condDistrib u a μ (root c)) (fun c ↦ condDistrib u a ν (root c))
    (fun c ↦ inferInstance) (fun c ↦ inferInstance) input hp C.roots_compact.measurableSet subset_rfl
  change fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ)
    (e '' (R '' C.roots)) = lambda C.roots at hm
  rw [hKeq] at hm
  have hmass : joint univ = lambda C.roots :=
    (fixedCandidate_joint_mass_eq volume (originalIIDRawPairPalmKernel Λ) K hK).trans hm
  have hfinite : IsFiniteMeasure joint :=
    ⟨by rw [hmass]; exact lt_top_iff_ne_top.mpr (measure_ne_top lambda C.roots)⟩
  have hkin := D.ae_originalIID_fixed_candidate_full_clock_kinetic_nonneg
    hF hcomplete hu ha hinj i Λ gap hgap input hprofile
  have hmeas : Measurable (fun p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
      matrixQuadratic (physicalSceneOriginalMacroCoefficient (P := P) (a := a)
        C.seedIndex (p.1,p.2.1)) p.2.2) := continuous_matrixQuadratic.measurable.comp
      (((measurable_physicalSceneOriginalMacroCoefficient hF hcomplete hu ha hinj C.seedIndex).comp
        (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)
  have hjoint : ∀ᵐ p ∂joint, 0 ≤ matrixQuadratic
      (physicalSceneOriginalMacroCoefficient (P := P) (a := a) C.seedIndex (p.1,p.2.1)) p.2.2 :=
    Measure.ae_compProd_of_ae_ae (measurableSet_le measurable_const hmeas) hkin
  refine ⟨hmass,hfinite,hjoint,?_⟩
  intro g t
  filter_upwards [hjoint] with p hp
  dsimp only [physicalSceneOriginalMacroShiftedTiltEnergy]
  have hg : |g (populationSeedPhysicalMap S (e.symm p.1,p.2.1.1),
      populationSeedPhysicalMap S (e.symm p.1,p.2.1.2))| ≤ ‖g‖ := by
    simpa only [Real.norm_eq_abs] using
      (g.norm_coe_le_norm (populationSeedPhysicalMap S (e.symm p.1,p.2.1.1),
        populationSeedPhysicalMap S (e.symm p.1,p.2.1.2)))
  have hprobe : |t * g (populationSeedPhysicalMap S (e.symm p.1,p.2.1.1),
      populationSeedPhysicalMap S (e.symm p.1,p.2.1.2))| ≤ |t| * ‖g‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hg (abs_nonneg t)
  have hneg := (abs_le.mp hprobe).1
  change 0 ≤ matrixQuadratic (physicalSceneOriginalMacroCoefficient (P := P) (a := a)
    C.seedIndex (p.1,p.2.1)) p.2.2 at hp
  change 0 ≤ matrixQuadratic (physicalSceneOriginalMacroCoefficient (P := P) (a := a)
    C.seedIndex (p.1,p.2.1)) p.2.2 +
      t * g (populationSeedPhysicalMap S (e.symm p.1,p.2.1.1),
        populationSeedPhysicalMap S (e.symm p.1,p.2.1.2)) + |t| * ‖g‖
  linarith

end OTSelector.Reconstruction
