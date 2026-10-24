import OTSelector.Reconstruction.OriginalIIDFinalValueFieldRootCandidate
import OTSelector.Reconstruction.OriginalIIDFinalValueFieldProbe
import OTSelector.Reconstruction.OriginalIIDActualCandidateLabelReadout
import OTSelector.Reconstruction.FinslerOriginalPhysicalRootPressure

/-! The actual iid macro candidate controls the same original root's full signed normalized pressure. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped ENNReal NNReal Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, (κ j).IsAddHaarMeasure] {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {b : (ℚ → M) × ℝ → M}

/-- Actual conditional endpoint recovery identifies every signed macro candidate
with the same physical root probe, retaining its original law and exact population
normalization. Only the named local focal reverse-pressure comparison is pending. -/
theorem original_signed_pressure_le_normalized_iid_macro_candidate_of_focal_reverse
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (j : ℕ) {z : ℚ → M} (hz : z ∈ populationSeedRootPiece P a κ lambda j)
    (D : OriginalSeedConditionalMoments (P j).seed
      (populationSeedPieceLabel P a κ lambda j ⟨z,hz⟩)
      (condDistrib u a η₀ z) (condDistrib u a η₁ z))
    {gap diameter : ℝ}
    (hbounds : ConditionalClockSupportBounds (condDistrib u a η₀ z) (condDistrib u a η₁ z) gap diameter)
    (f : M × M →ᵇ ℝ)
    (hsource : ∀ᵐ x ∂condDistrib u a η₀ z,
      b (z,x) = (P j).seed.curve (populationSeedRootLabelValue (P j).seed a z) (x-(P j).seed.level))
    (htarget : ∀ᵐ y ∂condDistrib u a η₁ z,
      b (z,y) = (P j).seed.curve (populationSeedRootLabelValue (P j).seed a z) (y-(P j).seed.level))
    (hreverse : ∀ Qf : LegalWeightedStationaryPoissonMatching
        (finrank ℝ (P j).seed.covector.ker) (condDistrib u a η₀ z) (condDistrib u a η₁ z)
        (D.originalFocalKinetic gap) (originalPhysicalRootProbe b f z),
      ∀ t, limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure
        (finrank ℝ (P j).seed.covector.ker) id id (condDistrib u a η₀ z) (condDistrib u a η₁ z)
        (D.originalFocalKinetic gap) (originalPhysicalRootProbe b f z) R t) ≤ Qf.value t)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ (P j).seed.covector.ker)
      (condDistrib u a η₀ (physicalSceneOriginalMacroRootValue (P := P) (a := a) j
        (physicalSceneOriginalMacroLabel (P := P) (a := a) j z)))
      (condDistrib u a η₁ (physicalSceneOriginalMacroRootValue (P := P) (a := a) j
        (physicalSceneOriginalMacroLabel (P := P) (a := a) j z)))
      (fun x y v ↦ matrixQuadratic (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j
        (physicalSceneOriginalMacroLabel (P := P) (a := a) j z,(x,y))) v)
      (fun x y ↦ originalIIDMacroPhysicalProbe (P := P) j f
        (physicalSceneOriginalMacroLabel (P := P) (a := a) j z,(x,y)))) (t : ℝ) :
    originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z ≤
      ((originalSeedCoordinateHaarFactor (P j).seed (κ j) : ℝ) *
        (populationSeedPieceHaarDensity P a κ lambda j
          ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm
            (physicalSceneOriginalMacroLabel (P := P) (a := a) j z))).toReal) ^
        (-2/(finrank ℝ (P j).seed.covector.ker : ℝ)) * Q.value (t * originalSeedCoordinateIntensity P a κ lambda j z ^
        (2/(finrank ℝ (P j).seed.covector.ker : ℝ))) := by
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : PolishSpace M := inferInstance
  let : BorelSpace (ℚ → M) := inferInstance
  have hroot := physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj j hz
  have hkin : (fun x y v ↦ matrixQuadratic (physicalSceneOriginalMacroCoefficient
      (P := P) (a := a) j (physicalSceneOriginalMacroLabel (P := P) (a := a) j z,(x,y))) v) =
      originalSeedRootKinetic (P j).seed a z := by
    funext x y v
    simp only [physicalSceneOriginalMacroCoefficient,hroot,originalSeedRootKinetic]
  obtain ⟨Q0,_hlaw,hvalue⟩ := Q.exists_sameLaw_of_eq_parameters
    (congrArg (fun w ↦ condDistrib u a η₀ w) hroot)
    (congrArg (fun w ↦ condDistrib u a η₁ w) hroot) hkin rfl
  obtain ⟨hw,_⟩ := fixed_seed_rootLabel_recovery hF hcomplete hu ha hinj j hz
  have hpoint (s : ℝ) : populationSeedPhysicalMap (P j).seed
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm
        (physicalSceneOriginalMacroLabel (P := P) (a := a) j z),s) =
      (P j).seed.curve (populationSeedRootLabelValue (P j).seed a z) (s-(P j).seed.level) := by
    rw [show (Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm
      (physicalSceneOriginalMacroLabel (P := P) (a := a) j z) =
      populationSeedRootLabelValue (P j).seed a z from
      (Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm_apply_apply _]
    exact populationSeedPhysicalMap_at_label (P j).seed ⟨_,hw⟩ s
  have hs : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q0.law,
      b (z,m.1.1) = (P j).seed.curve (populationSeedRootLabelValue (P j).seed a z) (m.1.1-(P j).seed.level) := by
    apply ae_of_ae_map (μ := legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q0.law)
      (f := fun m ↦ m.1.1)
      (p := fun s ↦ b (z,s) = (P j).seed.curve (populationSeedRootLabelValue (P j).seed a z) (s-(P j).seed.level))
      measurable_fst.fst.aemeasurable
    rw [Q0.source_clock]
    exact hsource
  have ht : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q0.law,
      b (z,m.1.2) = (P j).seed.curve (populationSeedRootLabelValue (P j).seed a z) (m.1.2-(P j).seed.level) := by
    apply ae_of_ae_map (μ := legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q0.law)
      (f := fun m ↦ m.1.2)
      (p := fun s ↦ b (z,s) = (P j).seed.curve (populationSeedRootLabelValue (P j).seed a z) (s-(P j).seed.level))
      measurable_fst.snd.aemeasurable
    rw [Q0.target_clock]
    exact htarget
  have heq : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q0.law,
      originalPhysicalRootProbe b f z m.1.1 m.1.2 =
      originalIIDMacroPhysicalProbe (P := P) j f
        (physicalSceneOriginalMacroLabel (P := P) (a := a) j z,m.1) := by
    filter_upwards [hs,ht] with m h₀ h₁
    simp only [originalPhysicalRootProbe,originalIIDMacroPhysicalProbe,hpoint,h₀,h₁]
  let Qphysical := Q0.withAEEqProbe heq
  have hp := originalSeedRootPressure_le_same_candidate_of_focal_reverse hF hcomplete hu ha hinj
    j hz D hbounds f hreverse Qphysical
      (t*originalSeedCoordinateIntensity P a κ lambda j z ^ (2/(finrank ℝ (P j).seed.covector.ker : ℝ)))
  have hq : finrank ℝ (P j).seed.covector.ker = finrank ℝ E-1 := by
    have hh := (P j).seed.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at hh
    omega
  have hqreal : (finrank ℝ (P j).seed.covector.ker : ℝ) = ((finrank ℝ E-1 : ℕ) : ℝ) := by
    exact_mod_cast hq
  have htheta : originalSeedCoordinateIntensity P a κ lambda j z =
      (originalSeedCoordinateHaarFactor (P j).seed (κ j) : ℝ) *
        (populationSeedPieceHaarDensity P a κ lambda j
          ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm
            (physicalSceneOriginalMacroLabel (P := P) (a := a) j z))).toReal := by
    simp only [originalSeedCoordinateIntensity,populationAtlasTheta]
    congr 3
    exact ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm_apply_apply _).symm
  rw [originalPhysicalFinslerRootPressure_eq_coordinate_on_piece _ j t hz,← htheta]
  have hp' := hp.trans_eq ((Q0.withAEEqProbe_value heq _).trans (hvalue _))
  have hθn : 0 ≤ originalSeedCoordinateIntensity P a κ lambda j z :=
    mul_nonneg (NNReal.coe_nonneg _) ENNReal.toReal_nonneg
  simpa only [hqreal] using mul_le_mul_of_nonneg_left hp'
    (Real.rpow_nonneg hθn (-2/(finrank ℝ (P j).seed.covector.ker : ℝ)))

end OTSelector.Reconstruction
