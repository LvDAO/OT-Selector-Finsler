import OTSelector.Reconstruction.MarkedStationaryValueLegalInputFiniteSimplicity

/-!
# The same original stationary weak input is simple

Every compact original marked window has its exact Poisson-prefix law.
Original Haar atomlessness gives unit atoms there. One countable compact
exhaustion and the already retained integer carrier therefore give simplicity
of the complete same-scene input. Neither simplicity of a weak limit nor an
atomless scalar-clock assumption is postulated.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

local instance markedStationaryValueLegalInputSimpleSceneColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
local instance markedStationaryValueLegalInputSimpleSceneInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputSimpleScenePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual unchanged original input is a simple integer measure in the
same joint weak limit as its legal optimal matching. Positive transverse
dimension supplies atomlessness; the scalar populations may overlap. -/
theorem ae_isLegalSimpleCountingMeasure_input_of_legalMarkedInputSceneLaw_tendsto
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q) s.2 := by
  let K := CompactExhaustion.choice (LegalColoredInputPoint q)
  have hsimple := measurableSet_isLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q)
  have hn (n : ℕ) : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q)
        (legalInputRestrictionLocal (K n) s.2) := by
    obtain ⟨S, hS, hlaw⟩ := map_legalMarkedInput_restrictionLocal_eq_originalPoisson_of_tendsto
      q α β kin hk g hg t L hL hlarge hweak (K.isCompact n)
    have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦ legalInputRestrictionLocal (K n) s.2) :=
      (measurable_legalInputRestrictionLocal (K.isCompact n).measurableSet).comp measurable_snd
    apply (ae_map_iff hm.aemeasurable hsimple).mp
    rw [hlaw]
    exact (ae_map_iff ((measurable_legalInputRestrictionLocal (K.isCompact n).measurableSet).comp
      (measurable_legalInputTwoBlockLocal q)).aemeasurable hsimple).mpr
        (ae_isLegalSimpleCountingMeasure_originalPoisson_restriction q hq hS α β (K n))
  filter_upwards [ae_all_iff.mpr hn,
    ae_isLegalCountingMeasure_of_legalMarkedInputSceneLaw_tendsto q α β kin hk g hg t L hL hweak]
    with s hs hc
  apply (isLegalSimpleCountingMeasure_iff (0 : LegalColoredInputPoint q) s.2).mpr
  refine ⟨hc.2, fun x ↦ ?_⟩
  obtain ⟨n, hxn⟩ := K.exists_mem x
  have hatom := ((isLegalSimpleCountingMeasure_iff _ _).mp (hs n)).2 x
  change ((s.2 : Measure (LegalColoredInputPoint q)).restrict (K n)) {x} ≤ 1 at hatom
  simpa only [Measure.restrict_apply (measurableSet_singleton x),
    singleton_inter_of_mem hxn] using hatom

end OTSelector.Reconstruction
