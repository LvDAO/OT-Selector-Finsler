import OTSelector.MeasureTheory.HomogeneousMeasureReadout
import OTSelector.Probability.DensityPressureIntegrability
import OTSelector.Reconstruction.OriginalIIDUnitColoredSceneKernel
import OTSelector.Reconstruction.OriginalIIDActualKineticIntegrability
import OTSelector.Reconstruction.MarkedStationaryValueLegalReserveIntensity

/-!
# Original density-weighted values of the same normalized actual matching

The same raw theta Palm is transported by the explicit unit-density dilation.
Its kinetic and clock-probe factors cancel the original density and tilt powers.
The nonnegative matrix-energy identity includes infinite kinetic moments.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000
local instance iidUnitValuePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace
local instance iidUnitValueInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace

/-- The explicit positive root is the existing physical intensity dilation at
the reciprocal raw intensity, so its established scaling lemmas apply. -/
theorem originalIIDUnitDilation_eq_inverse_intensity (q : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    originalIIDUnitDilation q θ = legalIntensityDilation q θ⁻¹ := by
  unfold originalIIDUnitDilation legalIntensityDilation
  simp only [hθ,↓reduceIte,Real.inv_rpow hθ.le,Real.rpow_neg hθ.le,inv_inv]

theorem originalIIDUnitDilation_jacobian (q : ℕ) (hq : 0 < q) {θ : ℝ} (hθ : 0 < θ) :
    |(originalIIDUnitDilation q θ ^ q)⁻¹| = θ⁻¹ := by
  rw [originalIIDUnitDilation_pow q hq hθ,abs_of_pos (inv_pos.mpr hθ)]

/-- The original Haar-density weight exactly cancels the kinetic intensity
factor of the same explicit unit-density spatial dilation. -/
theorem originalIIDUnitDilation_weighted_kinetic_factor (q : ℕ) (hq : 0 < q)
    {θ : ℝ} (hθ : 0 < θ) :
    θ ^ (1 - 2 / (q : ℝ)) *
      (|(originalIIDUnitDilation q θ ^ q)⁻¹| * originalIIDUnitDilation q θ ^ 2) = 1 := by
  rw [originalIIDUnitDilation_eq_inverse_intensity q hθ,
    legalIntensityDilation_kinetic_scale hq (inv_pos.mpr hθ),Real.inv_rpow hθ.le]
  exact mul_inv_cancel₀ (Real.rpow_pos_of_pos hθ _).ne'

/-- The original tilt has precisely the complementary density power needed
to restore the unchanged raw paired-clock probe. -/
theorem originalIIDUnitDilation_weighted_probe_factor (q : ℕ)
    {θ : ℝ} (hθ : 0 < θ) :
    θ ^ (1 - 2 / (q : ℝ)) * (θ ^ (2 / (q : ℝ)) * θ⁻¹) = 1 := by
  have hp := density_rpow_probe_weight (theta := θ) (a := 2 / (q : ℝ)) (t := 1) hθ.le
  simp only [one_mul,abs_of_nonneg (Real.rpow_nonneg hθ.le _),abs_one] at hp
  rw [← mul_assoc,hp,mul_inv_cancel₀ hθ.ne']

section RawReadouts
variable (q : ℕ) (Q : ProbabilityMeasure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v)
      ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)
      ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst))
    (hunit : (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)}
        ∂((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)) < ∞)

include hstat hunit

/-- The arbitrary original measurable homogeneous kinetic readout has the
exact Jacobian-times-quadratic factor on the same actual colored candidate. -/
theorem integral_originalUnitColoredLaw_homogeneous_kinetic
    (d : ℝ) (hd : d ≠ 0) (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hhom : ∀ a b v, kin a b (d • v) = d ^ 2 * kin a b v) :
    (∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q (originalUnitColoredLaw q Q d hd)) =
      |(d ^ q)⁻¹| * d ^ 2 *
        ∫ m, kin m.1.1 m.1.2 m.2 ∂cubePalm (Fin q) (physicalScenePairCampbell
          ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)) := by
  rw [originalUnitColoredLaw_palm_dilation q Q hstat hunit d hd]
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using
    integral_smul_map_of_comp_eq_mul _ (legalPairMarkDilation q d)
      (measurable_legalPairMarkDilation q d) (ENNReal.ofReal |(d ^ q)⁻¹|)
      (fun m : PhysicalPairPalmMark (Fin q) ↦ kin m.1.1 m.1.2 m.2) hk (d ^ 2)
      (fun m ↦ hhom m.1.1 m.1.2 m.2)

/-- A probe of the same original clock pair only pays the Palm intensity
Jacobian; its paired arguments are unchanged by the physical dilation. -/
theorem integral_originalUnitColoredLaw_clock_probe
    (d : ℝ) (hd : d ≠ 0) (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) :
    (∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q (originalUnitColoredLaw q Q d hd)) =
      |(d ^ q)⁻¹| *
        ∫ m, g m.1.1 m.1.2 ∂cubePalm (Fin q) (physicalScenePairCampbell
          ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)) := by
  rw [originalUnitColoredLaw_palm_dilation q Q hstat hunit d hd]
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _),mul_one] using
    integral_smul_map_of_comp_eq_mul _ (legalPairMarkDilation q d)
      (measurable_legalPairMarkDilation q d) (ENNReal.ofReal |(d ^ q)⁻¹|)
      (fun m : PhysicalPairPalmMark (Fin q) ↦ g m.1.1 m.1.2)
      (hg.comp measurable_fst) 1 (fun m ↦ (one_mul _).symm)

/-- Original density and tilt weights recover the SAME raw signed readout.
This Bochner identity imposes no hidden kinetic moment bound; the subsequent
finite-value constructor supplies the actual raw matrix integrability. -/
theorem integral_originalUnitColoredLaw_density_weighted_value
    (hq : 0 < q) {θ : ℝ} (hθ : 0 < θ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hhom : ∀ a b v, kin a b (originalIIDUnitDilation q θ • v) =
      originalIIDUnitDilation q θ ^ 2 * kin a b v)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    θ ^ (1 - 2 / (q : ℝ)) *
      ((∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q
        (originalUnitColoredLaw q Q (originalIIDUnitDilation q θ)
          (originalIIDUnitDilation_pos q θ).ne')) +
      (t * θ ^ (2 / (q : ℝ))) * ∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q
        (originalUnitColoredLaw q Q (originalIIDUnitDilation q θ)
          (originalIIDUnitDilation_pos q θ).ne')) =
      (∫ m, kin m.1.1 m.1.2 m.2 ∂cubePalm (Fin q) (physicalScenePairCampbell
        ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst))) +
      t * ∫ m, g m.1.1 m.1.2 ∂cubePalm (Fin q) (physicalScenePairCampbell
        ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)) := by
  rw [integral_originalUnitColoredLaw_homogeneous_kinetic q Q hstat hunit _ _ kin hk hhom,
    integral_originalUnitColoredLaw_clock_probe q Q hstat hunit _ _ g hg]
  have hkfac := originalIIDUnitDilation_weighted_kinetic_factor q hq hθ
  have hpfac := originalIIDUnitDilation_weighted_probe_factor q hθ
  have hjac := originalIIDUnitDilation_jacobian q hq hθ
  rw [hjac] at hkfac ⊢
  linear_combination
    (∫ m, kin m.1.1 m.1.2 m.2 ∂cubePalm (Fin q) (physicalScenePairCampbell
      ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst))) * hkfac +
    (t * ∫ m, g m.1.1 m.1.2 ∂cubePalm (Fin q) (physicalScenePairCampbell
      ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst))) * hpfac

/-- The density-weighted complete nonnegative matrix energy is exactly the
raw energy, including infinity. No finite-moment hypothesis is used. -/
theorem lintegral_originalUnitColoredLaw_density_weighted_matrix_energy
    (hq : 0 < q) {θ : ℝ} (hθ : 0 < θ)
    (A : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ) (hA : Measurable A) :
    ENNReal.ofReal (θ ^ (1 - 2 / (q : ℝ))) *
      (∫⁻ m, ENNReal.ofReal (matrixQuadratic (A m.1) m.2)
        ∂legalMarkedJointPalm q (originalUnitColoredLaw q Q (originalIIDUnitDilation q θ)
          (originalIIDUnitDilation_pos q θ).ne')) =
      ∫⁻ m, ENNReal.ofReal (matrixQuadratic (A m.1) m.2)
        ∂cubePalm (Fin q) (physicalScenePairCampbell
          ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)) := by
  rw [lintegral_originalUnitColoredLaw_matrix_energy q Q hstat hunit _ _ A hA]
  have hfac := congrArg ENNReal.ofReal
    (originalIIDUnitDilation_weighted_kinetic_factor q hq hθ)
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hθ.le _),
    ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_one] at hfac
  simpa only [mul_assoc,one_mul] using congrArg (fun r : ℝ≥0∞ ↦ r *
    ∫⁻ m, ENNReal.ofReal (matrixQuadratic (A m.1) m.2)
      ∂cubePalm (Fin q) (physicalScenePairCampbell
        ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst))) hfac

/-- An arbitrary nonnegative original clock-pair probe has the same exact
Jacobian readout even when its raw or unit expectation is infinite. -/
theorem lintegral_originalUnitColoredLaw_clock_probe
    (d : ℝ) (hd : d ≠ 0) (G : (ℝ × ℝ) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ m, G m.1 ∂legalMarkedJointPalm q (originalUnitColoredLaw q Q d hd)) =
      ENNReal.ofReal |(d ^ q)⁻¹| *
        ∫⁻ m, G m.1 ∂cubePalm (Fin q) (physicalScenePairCampbell
          ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)) := by
  rw [originalUnitColoredLaw_palm_dilation q Q hstat hunit d hd]
  simpa only [mul_one] using
    lintegral_smul_map_of_comp_eq_mul _ (legalPairMarkDilation q d)
      (measurable_legalPairMarkDilation q d) (ENNReal.ofReal |(d ^ q)⁻¹|)
      (fun m : PhysicalPairPalmMark (Fin q) ↦ G m.1)
      (hG.comp measurable_fst) 1 (fun m ↦ (one_mul _).symm)

end RawReadouts

/-- An actual matching profile supplies the stationary raw pair law and its
finite unit-cell mass directly. The raw Palm retains its mass theta. -/
theorem original_raw_palm_data_of_matching_profile
    (q : ℕ) (gap θ : ℝ) (hθ : 0 ≤ θ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (h : OriginalIIDConditionalMatchingProfile gap θ α β input Q) :
    let P := Q.map Prod.fst
    (∀ v, MeasurePreserving (physicalSceneReroot v) P P) ∧
      (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
        {e | e.1.1 ∈ palmUnitCube (Fin q)} ∂P) < ∞ ∧
      cubePalm (Fin q) (physicalScenePairCampbell P) univ = ENNReal.ofReal θ := by
  intro P
  have hQ : IsProbabilityMeasure Q := h.1
  have hfull := h.2.2.2.2.2.mono fun s hs ↦ hs.2.1
  have hr := original_raw_campbell_of_stationary_full_input_profile q θ hθ α β Q
    h.2.2.1 hfull h.2.2.2.1
  refine ⟨hr.1,?_,hr.2.2.1⟩
  rw [← physicalScenePairCampbell_unitCube,← cubePalm_apply (Fin q) _ MeasurableSet.univ,
    hr.2.2.1]
  exact ENNReal.ofReal_lt_top

/-- The density-weighted signed readout is produced from the same actual
conditional matching profile, without assuming a Campbell or Palm oracle. -/
theorem original_density_weighted_value_of_matching_profile
    (q : ℕ) (hq : 0 < q) (gap θ : ℝ) (hθ : 0 < θ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (h : OriginalIIDConditionalMatchingProfile gap θ α β input Q)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hhom : ∀ a b (d : ℝ), 0 ≤ d → ∀ v, kin a b (d • v) = d ^ 2 * kin a b v)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    let law := originalUnitColoredLaw q ⟨Q,h.1⟩ (originalIIDUnitDilation q θ)
      (originalIIDUnitDilation_pos q θ).ne'
    θ ^ (1 - 2 / (q : ℝ)) *
      ((∫ m, kin m.1.1 m.1.2 m.2 ∂legalMarkedJointPalm q law) +
        (t * θ ^ (2 / (q : ℝ))) * ∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q law) =
      (∫ m, kin m.1.1 m.1.2 m.2 ∂cubePalm (Fin q) (physicalScenePairCampbell (Q.map Prod.fst))) +
        t * ∫ m, g m.1.1 m.1.2 ∂cubePalm (Fin q) (physicalScenePairCampbell (Q.map Prod.fst)) := by
  have hd := original_raw_palm_data_of_matching_profile q gap θ hθ.le α β input Q h
  exact integral_originalUnitColoredLaw_density_weighted_value q ⟨Q,h.1⟩ hd.1 hd.2.1 hq hθ
    kin hk (fun a b v ↦ hhom a b _ (originalIIDUnitDilation_pos q θ).le v) g hg t

/-- The actual zero-intensity profile has zero raw Palm, rather than a
probability Palm requiring an impossible normalization. -/
theorem original_raw_palm_eq_zero_of_matching_profile
    (q : ℕ) (gap : ℝ) (α β : Measure ℝ)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (h : OriginalIIDConditionalMatchingProfile gap 0 α β input Q) :
    cubePalm (Fin q) (physicalScenePairCampbell (Q.map Prod.fst)) = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  simpa only [ENNReal.ofReal_zero] using
    (original_raw_palm_data_of_matching_profile q gap 0 le_rfl α β input Q h).2.2

/-- The fixed empty fallback scene has exactly zero Campbell Palm. It is not
misidentified with the unit-intensity probability Palm. -/
theorem cubePalm_originalIIDEmptyColoredScene (q : ℕ) :
    cubePalm (Fin q) (physicalScenePairCampbell
      ((Measure.dirac (originalColoredScene q (originalIIDEmptyInputScene q))).map Prod.fst)) = 0 := by
  have hcamp : physicalScenePairCampbell
      ((Measure.dirac (originalColoredScene q (originalIIDEmptyInputScene q))).map Prod.fst) = 0 := by
    rw [Measure.map_dirac' measurable_fst,physicalScenePairCampbell,
      Measure.dirac_bind (Kernel.measurable _),physicalScenePairKernel_apply]
    change (0 : Measure (LegalMarkedPhysicalEdge q)).map physicalPairAnchor = 0
    exact Measure.map_zero physicalPairAnchor
  ext B hB
  rw [cubePalm_apply (Fin q) _ hB,hcamp]
  simp

/-- Conditional only on genuine raw matrix integrability, the already produced
same candidate is a weighted legal matching with exactly the original signed
value. This helper introduces no kinetic-integrability assumption on a main D theorem. -/
theorem exists_originalLegalWeightedCandidate_density_value
    (q : ℕ) (hq : 0 < q) (gap θ : ℝ) (hgap : 0 < gap) (hθ : 0 < θ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (h : OriginalIIDConditionalMatchingProfile gap θ α β input Q)
    (A : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ) (hA : Measurable A)
    (hraw : Integrable (fun m ↦ matrixQuadratic (A m.1) m.2)
      (cubePalm (Fin q) (physicalScenePairCampbell (Q.map Prod.fst))))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g))
    (G : ℝ) (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) :
    ∃ M : LegalWeightedStationaryPoissonMatching q α β
        (fun a b v ↦ matrixQuadratic (A (a,b)) v) g,
      M.law = originalUnitColoredLaw q ⟨Q,h.1⟩ (originalIIDUnitDilation q θ)
        (originalIIDUnitDilation_pos q θ).ne' ∧
      θ ^ (1 - 2 / (q : ℝ)) * M.value (t * θ ^ (2 / (q : ℝ))) =
        (∫ m, matrixQuadratic (A m.1) m.2 ∂cubePalm (Fin q)
          (physicalScenePairCampbell (Q.map Prod.fst))) +
        t * ∫ m, g m.1.1 m.1.2 ∂cubePalm (Fin q) (physicalScenePairCampbell (Q.map Prod.fst)) := by
  have hd := original_raw_palm_data_of_matching_profile q gap θ hθ.le α β input Q h
  have hunitkin := (integrable_originalUnitColoredLaw_matrix_iff q ⟨Q,h.1⟩ hd.1 hd.2.1
    (originalIIDUnitDilation q θ) (originalIIDUnitDilation_pos q θ).ne' A hA).mpr hraw
  let M := originalLegalWeightedCandidate q gap θ hgap hθ α β input Q h
    (originalIIDUnitDilation q θ) (originalIIDUnitDilation_pos q θ)
    (originalIIDUnitDilation_pow q hq hθ)
    (fun a b v ↦ matrixQuadratic (A (a,b)) v) g hunitkin hg G hgb
  refine ⟨M,rfl,?_⟩
  exact original_density_weighted_value_of_matching_profile q hq gap θ hθ α β input Q h
    (fun a b v ↦ matrixQuadratic (A (a,b)) v)
    (continuous_matrixQuadratic.measurable.comp ((hA.comp measurable_fst).prodMk measurable_snd))
    (fun a b d _ v ↦ matrixQuadratic_smul (A (a,b)) d v) g hg t

/-- On the measurable same-root unit kernel the original density-weighted
signed readout equals the original raw readout at every nonnegative intensity.
The zero branch uses the proved zero raw Palm and the fixed empty fallback. -/
theorem originalIIDUnitColoredSceneKernel_density_weighted_value
    {C : Type*} [MeasurableSpace C] (q : ℕ) (hq : 0 < q)
    (θ : C → ℝ) (hθ : Measurable θ)
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsMarkovKernel Λ]
    (c : C) (hθc : 0 ≤ θ c) (gap : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (h : OriginalIIDConditionalMatchingProfile gap (θ c) α β input (Λ c))
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hhom : ∀ a b (d : ℝ), 0 ≤ d → ∀ v, kin a b (d • v) = d ^ 2 * kin a b v)
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    let raw := cubePalm (Fin q) (physicalScenePairCampbell ((Λ c).map Prod.fst))
    let normalized := cubePalm (Fin q) (physicalScenePairCampbell
      ((originalIIDUnitColoredSceneKernel q θ hθ Λ c).map Prod.fst))
    θ c ^ (1 - 2 / (q : ℝ)) *
      ((∫ m, kin m.1.1 m.1.2 m.2 ∂normalized) +
        (t * θ c ^ (2 / (q : ℝ))) * ∫ m, g m.1.1 m.1.2 ∂normalized) =
      (∫ m, kin m.1.1 m.1.2 m.2 ∂raw) + t * ∫ m, g m.1.1 m.1.2 ∂raw := by
  dsimp only
  by_cases hp : 0 < θ c
  · rw [originalIIDUnitColoredSceneKernel_pairLaw q θ hθ Λ c hp]
    have hv := original_density_weighted_value_of_matching_profile q hq gap (θ c) hp
      α β input (Λ c) h kin hk hhom g hg t
    simpa only [legalMarkedJointPalm,originalUnitColoredLaw_pairLaw,ProbabilityMeasure.coe_mk] using hv
  · have hz : θ c = 0 := le_antisymm (le_of_not_gt hp) hθc
    have hzero := original_raw_palm_eq_zero_of_matching_profile q gap α β input (Λ c)
      (by simpa only [hz] using h)
    rw [originalIIDUnitColoredSceneKernel_eq_nonpositive q θ hθ Λ c (le_of_not_gt hp),
      cubePalm_originalIIDEmptyColoredScene,hzero]
    simp

/-- The whole measurable candidate has exactly the original density-weighted
nonnegative full-matrix energy, including zero intensity and infinite moments.
No positive lower density bound or kinetic-integrability input is required. -/
theorem originalIIDUnitColoredSceneKernel_density_weighted_matrix_energy
    {C : Type*} [MeasurableSpace C] (q : ℕ) (hq : 0 < q)
    (θ : C → ℝ) (hθ : Measurable θ)
    (Λ : Kernel C (OriginalIIDMaskedMacroInputScene (Fin q))) [IsMarkovKernel Λ]
    (c : C) (hθc : 0 ≤ θ c) (gap : ℝ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (h : OriginalIIDConditionalMatchingProfile gap (θ c) α β input (Λ c))
    (A : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ) (hA : Measurable A) :
    ENNReal.ofReal (θ c ^ (1 - 2 / (q : ℝ))) *
      (∫⁻ m, ENNReal.ofReal (matrixQuadratic (A m.1) m.2)
        ∂cubePalm (Fin q) (physicalScenePairCampbell
          ((originalIIDUnitColoredSceneKernel q θ hθ Λ c).map Prod.fst))) =
      ∫⁻ m, ENNReal.ofReal (matrixQuadratic (A m.1) m.2)
        ∂cubePalm (Fin q) (physicalScenePairCampbell ((Λ c).map Prod.fst)) := by
  by_cases hp : 0 < θ c
  · rw [originalIIDUnitColoredSceneKernel_pairLaw q θ hθ Λ c hp]
    have hd := original_raw_palm_data_of_matching_profile q gap (θ c) hp.le α β input (Λ c) h
    have he := lintegral_originalUnitColoredLaw_density_weighted_matrix_energy q ⟨Λ c,h.1⟩
      hd.1 hd.2.1 hq hp A hA
    simpa only [legalMarkedJointPalm,originalUnitColoredLaw_pairLaw,ProbabilityMeasure.coe_mk] using he
  · have hz : θ c = 0 := le_antisymm (le_of_not_gt hp) hθc
    have hzero := original_raw_palm_eq_zero_of_matching_profile q gap α β input (Λ c)
      (by simpa only [hz] using h)
    rw [originalIIDUnitColoredSceneKernel_eq_nonpositive q θ hθ Λ c (le_of_not_gt hp),
      cubePalm_originalIIDEmptyColoredScene,hzero]
    simp

end OTSelector.Reconstruction
