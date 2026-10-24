import OTSelector.Reconstruction.OriginalIIDFinalValueFieldRootCandidate
import OTSelector.Reconstruction.OriginalIIDActualCandidateLabelReadout
import OTSelector.Reconstruction.FinslerOriginalPhysicalRootPressure

/-! The actual iid macro candidate controls the same original root's normalized zero pressure. -/
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

/-- At an actual selected root, the genuine iid macro candidate has exactly the
native coefficient, original conditional clocks and Theta=cHaar*theta normalization.
Only the explicitly named local focal reverse-pressure comparison is pending. -/
theorem original_zero_pressure_le_normalized_iid_macro_candidate_of_focal_reverse
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
    (hreverse : ∀ Qf : LegalWeightedStationaryPoissonMatching
        (finrank ℝ (P j).seed.covector.ker) (condDistrib u a η₀ z) (condDistrib u a η₁ z)
        (D.originalFocalKinetic gap) (originalPhysicalRootProbe b (0 : M × M →ᵇ ℝ) z),
      ∀ t, limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure
        (finrank ℝ (P j).seed.covector.ker) id id (condDistrib u a η₀ z) (condDistrib u a η₁ z)
        (D.originalFocalKinetic gap) (originalPhysicalRootProbe b (0 : M × M →ᵇ ℝ) z) R t) ≤ Qf.value t)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ (P j).seed.covector.ker)
      (condDistrib u a η₀ (physicalSceneOriginalMacroRootValue (P := P) (a := a) j
        (physicalSceneOriginalMacroLabel (P := P) (a := a) j z)))
      (condDistrib u a η₁ (physicalSceneOriginalMacroRootValue (P := P) (a := a) j
        (physicalSceneOriginalMacroLabel (P := P) (a := a) j z)))
      (fun x y v ↦ matrixQuadratic (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j
        (physicalSceneOriginalMacroLabel (P := P) (a := a) j z,(x,y))) v)
      (fun x y ↦ originalIIDMacroPhysicalProbe (P := P) j (0 : M × M →ᵇ ℝ)
        (physicalSceneOriginalMacroLabel (P := P) (a := a) j z,(x,y)))) :
    originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b (0 : M × M →ᵇ ℝ) 0 z ≤
      ((originalSeedCoordinateHaarFactor (P j).seed (κ j) : ℝ) *
        (populationSeedPieceHaarDensity P a κ lambda j
          ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm
            (physicalSceneOriginalMacroLabel (P := P) (a := a) j z))).toReal) ^
        (-2/(finrank ℝ (P j).seed.covector.ker : ℝ)) * Q.value 0 := by
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
  have hprobe : (fun x y ↦ originalIIDMacroPhysicalProbe (P := P) j (0 : M × M →ᵇ ℝ)
      (physicalSceneOriginalMacroLabel (P := P) (a := a) j z,(x,y))) =
      originalPhysicalRootProbe b (0 : M × M →ᵇ ℝ) z := by
    funext x y
    rfl
  have transport {μ' ν' μ'' ν'' : Measure ℝ}
      {kin' kin'' : ℝ → ℝ → (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) → ℝ}
      {probe' probe'' : ℝ → ℝ → ℝ}
      (hμ : μ'=μ'') (hν : ν'=ν'') (hk : kin'=kin'') (hg : probe'=probe'')
      (Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ (P j).seed.covector.ker) μ' ν' kin' probe') :
      ∃ Q'' : LegalWeightedStationaryPoissonMatching (finrank ℝ (P j).seed.covector.ker) μ'' ν'' kin'' probe'',
        ∀ t, Q''.value t = Q'.value t := by
    subst μ''; subst ν''; subst kin''; subst probe''
    exact ⟨Q',fun _ ↦ rfl⟩
  obtain ⟨Qroot,hvalue⟩ := transport (congrArg (fun w ↦ condDistrib u a η₀ w) hroot)
    (congrArg (fun w ↦ condDistrib u a η₁ w) hroot) hkin hprobe Q
  have hp := originalSeedRootPressure_le_same_candidate_of_focal_reverse hF hcomplete hu ha hinj
    j hz D hbounds (0 : M × M →ᵇ ℝ) hreverse Qroot 0
  have hq : finrank ℝ (P j).seed.covector.ker = finrank ℝ E-1 := by
    have hh := (P j).seed.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at hh
    omega
  rw [originalPhysicalFinslerRootPressure_eq_coordinate_on_piece _ j 0 hz,zero_mul]
  have htheta : originalSeedCoordinateIntensity P a κ lambda j z =
      (originalSeedCoordinateHaarFactor (P j).seed (κ j) : ℝ) *
        (populationSeedPieceHaarDensity P a κ lambda j
          ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm
            (physicalSceneOriginalMacroLabel (P := P) (a := a) j z))).toReal := by
    simp only [originalSeedCoordinateIntensity,populationAtlasTheta]
    congr 3
    exact ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm_apply_apply _).symm
  have hqreal : (finrank ℝ (P j).seed.covector.ker : ℝ) = ((finrank ℝ E-1 : ℕ) : ℝ) := by
    exact_mod_cast hq
  rw [← htheta]
  simp only [hqreal]
  exact mul_le_mul_of_nonneg_left (hp.trans_eq (hvalue 0)) (Real.rpow_nonneg
    (mul_nonneg (NNReal.coe_nonneg _) ENNReal.toReal_nonneg) _)

end OTSelector.Reconstruction
