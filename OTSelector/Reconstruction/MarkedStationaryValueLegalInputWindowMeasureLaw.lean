import OTSelector.PointProcess.CutoffLaplaceLaw
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointStationarity

/-!
# The actual weak input has the original finite Poisson window law

Continuous cutoffs and whole-law Laplace determination identify the literal
restriction of the same actual joint input to any compact marked window. The
comparison measure is the actual independent original two-color Poisson prefix
in a containing physical cube. Coordinates, original clocks, finite colors,
and all correlations with the limiting matching remain in the same joint law.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped CompactlySupported ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- Both finite original point arrays as one measure with immutable colors. -/
def legalInputTwoBlockMeasure (q : ℕ)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
    Measure (LegalColoredInputPoint q) :=
  legalInputBlockMeasure (mapBlockData (fun x ↦ (x, (0 : Fin 2))) b.1) +
    legalInputBlockMeasure (mapBlockData (fun x ↦ (x, (1 : Fin 2))) b.2)

instance legalInputTwoBlockMeasureIsFinite (q : ℕ)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
    IsFiniteMeasure (legalInputTwoBlockMeasure q b) := by
  unfold legalInputTwoBlockMeasure
  infer_instance

/-- This is the literal finite Poisson input measure, not a new input draw. -/
def legalInputTwoBlockLocal (q : ℕ)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
    LocalFiniteMeasure (LegalColoredInputPoint q) :=
  ⟨legalInputTwoBlockMeasure q b, inferInstance⟩

theorem measurable_legalInputTwoBlockLocal (q : ℕ) :
    Measurable (legalInputTwoBlockLocal q) := by
  apply measurable_localFiniteMeasure_of_measurable_measure
  change Measurable (legalInputTwoBlockMeasure q)
  have hc (c : Fin 2) : Measurable (fun b : BlockData (LegalMarkedPhysicalPoint q) ↦
      legalInputBlockMeasure (mapBlockData (fun x ↦ (x, c)) b)) :=
    measurable_legalInputBlockMeasure.comp
      (measurable_mapBlockData (measurable_id.prodMk measurable_const))
  apply Measure.measurable_of_measurable_coe
  intro U hU
  convert (((Measure.measurable_coe hU).comp (hc 0)).comp measurable_fst).add
      (((Measure.measurable_coe hU).comp (hc 1)).comp measurable_snd) using 1
  funext b
  exact Measure.add_apply _ _ U

/-- Integrating the actual colored measure reads the two original point sums. -/
theorem integral_legalInputTwoBlockMeasure (q : ℕ)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (F : LegalColoredInputPoint q → ℝ) :
    (∫ x, F x ∂legalInputTwoBlockMeasure q b) =
      legalInputBlockTest (fun x ↦ F (x, 0)) b.1 +
        legalInputBlockTest (fun x ↦ F (x, 1)) b.2 := by
  have hi (d : BlockData (LegalColoredInputPoint q)) : Integrable F (legalInputBlockMeasure d) := by
    unfold legalInputBlockMeasure
    exact integrable_finsetSum_measure.mpr (fun i _ ↦ integrable_dirac (by simp))
  rw [legalInputTwoBlockMeasure, integral_add_measure (hi _) (hi _),
    integral_legalInputBlockMeasure, integral_legalInputBlockMeasure]
  rfl

local instance markedStationaryValueLegalInputWindowMeasureLawInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputWindowMeasureLawPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Every fixed compact marked window in the same original weak scene has its
exact original Poisson input measure law. The containing cube and cutoff are
constructed from the window; no boundary-nullness assumption is needed. -/
theorem map_legalMarkedInput_restrict_eq_originalPoisson_of_tendsto
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q))
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
  haveI : IsProbabilityMeasure (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β) :=
    isProbabilityMeasure_legalInputPoissonWindowLaw q hS.le measurableSet_Icc (Subset.refl _) hvol α β
  let P := (Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd
  let P' := (legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β).map
    (legalInputTwoBlockLocal q)
  haveI : IsProbabilityMeasure P := by
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  haveI : IsProbabilityMeasure P' := by
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
    have hread := integral_legalMarkedInputSceneLaplace_eq_originalPoisson_window_of_tendsto
      q α β kin hk g hg t L hL hlarge hweak hS T hT hTzero
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

end OTSelector.Reconstruction
