import OTSelector.Reconstruction.OriginalIIDActualTiltSignedLower

/-! Real signed means of the genuine particle-indexed original iid optimizer remain bounded. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open scoped Topology ContDiff ENNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The actual physical kinetic energy budget controls both signs of the true
signed mean. This allows convergent extraction from any bad sample subsequence,
without a pressure bound or independence between a chosen optimizer and its input. -/
theorem original_actual_iid_signed_mean_bounds_of_energy
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (n : ℕ) (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost)) (k w : ℝ) (hw : 0 ≤ w)
    (g : M × M →ᵇ ℝ) (t : ℝ) (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (w*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
      ∂originalIIDOptimalPhysicalPlan (n := n+1) cost k ξ
      ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget) :
    let value := (∫ p, w*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p
      ∂originalIIDOptimalMeanPlan μ ν cost k (n+1));
    -(|t| * ‖g‖) ≤ value ∧ value ≤ budget.toReal+|t| * ‖g‖ := by
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : PolishSpace M := inferInstance
  let π := originalIIDOptimalMeanPlan μ ν cost k (n+1)
  let : IsProbabilityMeasure π := isProbabilityMeasure_originalIIDOptimalMeanPlan μ ν n cost hcost k
  let base := fun p : M × M ↦ w*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)
  have hbaseInt : Integrable base π := by
    simpa only [zero_mul,add_zero] using integrable_originalIIDOptimalMeanPlan_physical_tilt
      hcomplete hu hA hB hμ hν n cost hcost k w (0 : M × M →ᵇ ℝ) 0
  have hvalueInt := integrable_originalIIDOptimalMeanPlan_physical_tilt
    hcomplete hu hA hB hμ hν n cost hcost k w g t
  have hbaseNonneg (p) : 0 ≤ base p := by
    simpa only [zero_mul,abs_zero,mul_zero,add_zero] using
      originalIID_physical_shifted_tilt_nonneg hu w hw (0 : M × M →ᵇ ℝ) 0 p
  have hbaseBound : (∫ p, base p ∂π) ≤ budget.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hbaseNonneg) hbaseInt.aestronglyMeasurable]
    apply ENNReal.toReal_mono hbudget
    rw [lintegral_originalIIDOptimalMeanPlan μ ν cost hcost k (n+1) _
      ((F.measurable_distance_slack hu).const_mul w).ennreal_ofReal]
    exact henergy
  intro value
  constructor
  · have h := integral_mono_ae (integrable_const (- (|t| * ‖g‖))) hvalueInt
      (Eventually.of_forall (fun p ↦ by
        have hh := originalIID_physical_shifted_tilt_nonneg hu w hw g t p
        linarith only [hh]))
    simpa only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using h
  · have hupper : ∀ p : M × M, w*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p ≤
        base p+|t| * ‖g‖ := by
      intro p
      have hh : t*g p ≤ |t| * ‖g‖ := (le_abs_self _).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm p) (abs_nonneg t))
      dsimp only [base]
      linarith only [hh]
    have h := integral_mono_ae hvalueInt (hbaseInt.add (integrable_const (|t| * ‖g‖)))
      (Eventually.of_forall hupper)
    change value ≤ (∫ p, base p+|t| * ‖g‖ ∂π) at h
    rw [integral_add hbaseInt (integrable_const _)] at h
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at h
    linarith only [h,hbaseBound]

/-- Bounded actual means whose every convergent subsequence lies above the
same value eventually lie above that value minus any positive error. -/
theorem eventually_mean_lower_of_all_convergent_subsequences
    (mean : ℕ → ℝ) (lo hi lower : ℝ) (hbounded : ∀ n, mean n ∈ Icc lo hi)
    (hlimits : ∀ (initial : ℕ → ℕ), StrictMono initial → ∀ L : ℝ,
      Tendsto (mean ∘ initial) atTop (𝓝 L) → lower ≤ L) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, lower-ε ≤ mean n := by
  by_contra hnot
  have hbad : ∃ᶠ n in atTop, mean n < lower-ε := by
    simpa only [Filter.Frequently,not_lt] using hnot
  obtain ⟨initial,hinitial,hviolates⟩ := extraction_of_frequently_atTop hbad
  obtain ⟨L,_hL,extraction,hextraction,hlimit⟩ := isCompact_Icc.isSeqCompact
    (fun n ↦ hbounded (initial n))
  have hlower := hlimits (initial ∘ extraction) (hinitial.comp hextraction) L hlimit
  have hupper : L ≤ lower-ε := le_of_tendsto hlimit
    (Eventually.of_forall (fun n ↦ (hviolates (extraction n)).le))
  linarith only [hlower,hupper,hε]

end OTSelector.Reconstruction
