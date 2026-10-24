import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindowLocalLaw

/-!
# Every prescribed stationary candidate retains the exact original window law

The compact Poisson Laplace functional in the actual admissible matching class
identifies its entire original input restriction law. This applies to arbitrary
stationary competitors, including those not selected as limits of finite
optima, and never assigns an iid law to adaptive selected endpoints.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalStationaryWindowLawInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryWindowLawPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Compact Laplace readouts identify the actual colored input restriction
of any scene law. The retained plan may be partial and need not be stationary. -/
theorem map_inputRestriction_eq_originalPoisson_of_laplace
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hLaplace : ∀ S : ℝ, 0 < S →
      ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
      (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
        x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) →
      (∫ s, legalMarkedInputSceneLaplace q F hF s
        ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
        ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
          ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U) :
    ∃ S > 0,
      (Q : Measure (LegalMarkedOptimalInputScene q)).map
        (fun s ↦ (s.2 : Measure (LegalColoredInputPoint q)).restrict U) =
      (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
        (fun b ↦ (legalInputTwoBlockMeasure q b).restrict U) := by
  obtain ⟨η, hηU, hη⟩ := LocalFiniteMeasure.exists_compact_cutoff hU
  obtain ⟨S, hS, hbound⟩ := (η.hasCompactSupport.image
    (continuous_fst.comp continuous_fst)).isBounded.exists_pos_norm_lt
  have hηzero (x : LegalMarkedPhysicalPoint q) (c : Fin 2)
      (hx : x.1 ∉ haarRootCube (Fin q) S) : η (x, c) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hsupp
    apply hx
    have hn : ‖x.1‖ < S := hbound _ ⟨(x, c), hsupp, rfl⟩
    have hi (i : Fin q) : |x.1 i| ≤ S := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm x.1 i).trans hn.le
    exact ⟨fun i ↦ (abs_le.mp (hi i)).1, fun i ↦ (abs_le.mp (hi i)).2⟩
  have hvol : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  have : IsProbabilityMeasure (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β) :=
    isProbabilityMeasure_legalInputPoissonWindowLaw q hS.le measurableSet_Icc (Subset.refl _) hvol α β
  let P := (Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd
  let P' := (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
    (legalInputTwoBlockLocal q)
  have : IsProbabilityMeasure P := by
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have : IsProbabilityMeasure P' := by
    exact Measure.isProbabilityMeasure_map (measurable_legalInputTwoBlockLocal q).aemeasurable
  have hLap : ∀ F : LegalNonnegativeInputTest (LegalColoredInputPoint q),
      (∫ μ, legalInputMeasureLaplace
        ⟨LocalFiniteMeasure.weightedContinuousTest F.1 η.toContinuousMap,
          fun x ↦ mul_nonneg (F.2 x) (hη x).1⟩ μ ∂P) =
      ∫ μ, legalInputMeasureLaplace
        ⟨LocalFiniteMeasure.weightedContinuousTest F.1 η.toContinuousMap,
          fun x ↦ mul_nonneg (F.2 x) (hη x).1⟩ μ ∂P' := by
    intro F
    let T : C_c(LegalColoredInputPoint q, ℝ) :=
      LocalFiniteMeasure.weightedContinuousTest F.1 η.toContinuousMap
    have hT (x) : 0 ≤ T x := mul_nonneg (F.2 x) (hη x).1
    have hTzero (x : LegalMarkedPhysicalPoint q) (c : Fin 2)
        (hx : x.1 ∉ haarRootCube (Fin q) S) : T (x, c) = 0 := by
      change F.1 (x, c) * η (x, c) = 0
      rw [hηzero x c hx, mul_zero]
    have hread := hLaplace S hS T hT hTzero
    change (∫ μ, legalInputMeasureLaplace ⟨T, hT⟩ μ ∂P) =
      ∫ μ, legalInputMeasureLaplace ⟨T, hT⟩ μ ∂P'
    dsimp only [P, P']
    rw [integral_map measurable_snd.aemeasurable
      (legalInputMeasureLaplace ⟨T, hT⟩).continuous.aestronglyMeasurable,
      integral_map (measurable_legalInputTwoBlockLocal q).aemeasurable
        (legalInputMeasureLaplace ⟨T, hT⟩).continuous.aestronglyMeasurable]
    change (∫ s, legalMarkedInputSceneLaplace q T hT s ∂(Q : Measure (LegalMarkedOptimalInputScene q))) = _
    rw [hread]
    apply integral_congr_ae
    exact .of_forall fun b ↦ by
      change Real.exp (-(legalInputBlockTest (fun x ↦ T (x, 0)) b.1 +
        legalInputBlockTest (fun x ↦ T (x, 1)) b.2)) =
          Real.exp (-(∫ x, T x ∂legalInputTwoBlockMeasure q b))
      rw [integral_legalInputTwoBlockMeasure]

  have hlocal := map_legalInput_restrict_eq_of_cutoff_laplace P P' η.toContinuousMap
    (fun x ↦ (hη x).1) hU.measurableSet hηU hLap
  have hr : Measurable (fun μ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      (μ : Measure (LegalColoredInputPoint q)).restrict U) := by
    apply Measure.measurable_of_measurable_coe
    intro V hV
    simpa only [Measure.restrict_apply hV, Function.comp_def] using
      (Measure.measurable_coe (hV.inter hU.measurableSet)).comp measurable_localFiniteMeasure_coe
  refine ⟨S, hS, ?_⟩
  simpa only [P, P', Measure.map_map hr measurable_snd,
    Measure.map_map hr (measurable_legalInputTwoBlockLocal q),
    Function.comp_def, legalInputTwoBlockLocal] using hlocal


/-- The same exact input restriction law on the locally finite carrier,
without any full-matching, marginal, or stationarity assumption on the scene. -/
theorem map_inputRestrictionLocal_eq_originalPoisson_of_laplace
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hLaplace : ∀ S : ℝ, 0 < S →
      ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
      (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
        x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) →
      (∫ s, legalMarkedInputSceneLaplace q F hF s
        ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
        ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
          ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U) :
    ∃ S > 0,
      (Q : Measure (LegalMarkedOptimalInputScene q)).map
        (fun s ↦ legalInputRestrictionLocal U s.2) =
      (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
        (fun b ↦ legalInputRestrictionLocal U (legalInputTwoBlockLocal q b)) := by
  obtain ⟨S, hS, hraw⟩ := map_inputRestriction_eq_originalPoisson_of_laplace Q hLaplace hU
  let F := finitePlanLocalVersion (id : Measure (LegalColoredInputPoint q) → Measure (LegalColoredInputPoint q))
  have hF : Measurable F := measurable_finitePlanLocalVersion id measurable_id
  have hrestrict : Measurable (fun μ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      (μ : Measure (LegalColoredInputPoint q)).restrict U) :=
    measurable_localFiniteMeasure_coe.comp (measurable_legalInputRestrictionLocal hU.measurableSet)
  have h1 : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.2 : Measure (LegalColoredInputPoint q)).restrict U) := hrestrict.comp measurable_snd
  have h2 : Measurable (fun b ↦ (legalInputTwoBlockMeasure q b).restrict U) := by
    exact hrestrict.comp (measurable_legalInputTwoBlockLocal q)
  have h := congrArg (fun P : Measure (Measure (LegalColoredInputPoint q)) ↦ P.map F) hraw
  rw [Measure.map_map hF h1, Measure.map_map hF h2] at h
  have hb (b) : F ((legalInputTwoBlockMeasure q b).restrict U) =
      legalInputRestrictionLocal U (legalInputTwoBlockLocal q b) :=
    finitePlanLocalVersion_restrict_compact_eq hU (legalInputTwoBlockLocal q b)
  refine ⟨S, hS, ?_⟩
  simpa only [Function.comp_def, hb, F, finitePlanLocalVersion_restrict_compact_eq hU] using h

/-- The complete marked input restriction of any genuine prescribed-input
stationary matching has its exact original independent Poisson-prefix law. -/
theorem LegalWeightedStationaryPoissonMatching.map_inputRestriction_eq_originalPoisson
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U) :
    ∃ S > 0,
      (M.law : Measure (LegalMarkedOptimalInputScene q)).map
        (fun s ↦ (s.2 : Measure (LegalColoredInputPoint q)).restrict U) =
      (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
        (fun b ↦ (legalInputTwoBlockMeasure q b).restrict U) := by
  exact map_inputRestriction_eq_originalPoisson_of_laplace M.law M.input_laplace hU

/-- The same exact law on the locally finite carrier permits coupling original
stationary windows to literal finite Poisson arrays without replacing inputs. -/
theorem LegalWeightedStationaryPoissonMatching.map_inputRestrictionLocal_eq_originalPoisson
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U) :
    ∃ S > 0,
      (M.law : Measure (LegalMarkedOptimalInputScene q)).map
        (fun s ↦ legalInputRestrictionLocal U s.2) =
      (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
        (fun b ↦ legalInputRestrictionLocal U (legalInputTwoBlockLocal q b)) := by
  exact map_inputRestrictionLocal_eq_originalPoisson_of_laplace M.law M.input_laplace hU

end OTSelector.Reconstruction
