import OTSelector.Probability.WeakClosedConstraint
import OTSelector.PointProcess.LocalConfiguration.MeasureSupport

/-!
# Plan support over the same limiting integer target cloud

The support condition is closed even when the target projection is not proper.
A vacant target neighborhood has zero plan mass before the limit, and open-mass
lower semicontinuity retains that fact for the actual diffuse plan.
-/

open Function Filter MeasureTheory Set Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

open PointProcess PointProcess.LocalConfiguration

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [T2Space X] [LocallyCompactSpace X]
  [BorelSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]
  [SecondCountableTopology X]
  [MetricSpace Y] [ProperSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] {base : Y}

local instance cavitySemidiscreteConfigurationSupportLocalInst1 : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance cavitySemidiscreteConfigurationSupportLocalInst2 : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance cavitySemidiscreteConfigurationSupportLocalInst3 : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance cavitySemidiscreteConfigurationSupportLocalInst4 : PolishSpace (LocalFiniteMeasure X) := LocalFiniteMeasure.instPolishSpace

/-- Every actual plan support point projects to an occupied target site. -/
def SupportedOverConfiguration (f : X → Y) (config : LocalConfiguration base)
    (μ : LocalFiniteMeasure X) : Prop :=
  ∀ x ∈ (μ : Measure X).support, f x ∈ Function.support (multiplicity config)

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [ProperSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] in
/-- Support carrying and almost-everywhere carrying agree for a continuous
observation of the original diffuse measure. -/
theorem supportedOverConfiguration_iff_ae_mem (f : X → Y) (hf : Continuous f)
    (config : LocalConfiguration base) (μ : LocalFiniteMeasure X) :
    SupportedOverConfiguration f config μ ↔
      ∀ᵐ x ∂(μ : Measure X), f x ∈ Function.support (multiplicity config) := by
  constructor
  · intro h
    have hs : ∀ᵐ x ∂(μ : Measure X), x ∈ (μ : Measure X).support := Measure.support_mem_ae
    exact hs.mono (fun x hx ↦ h x hx)
  · intro h
    exact Measure.support_subset_of_isClosed
      ((isClosed_multiplicity_support config).preimage hf) h

omit [T2Space X] [LocallyCompactSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [ProperSpace Y] in
/-- Original marginal domination transfers the cloud support to the whole plan. -/
theorem supportedOverConfiguration_of_map_le
    (f : X → Y) (hf : Continuous f) (config : LocalConfiguration base)
    (μ : LocalFiniteMeasure X) (ν : LocalFiniteMeasure Y)
    (hdom : (μ : Measure X).map f ≤ (ν : Measure Y))
    (hν : SupportedOnConfiguration config ν) :
    SupportedOverConfiguration f config μ := by
  apply (supportedOverConfiguration_iff_ae_mem f hf config μ).mpr
  have hcar := (supportedOnConfiguration_iff_ae_mem config ν).mp hν
  have hmap : ∀ᵐ y ∂(μ : Measure X).map f,
      y ∈ Function.support (multiplicity config) :=
    hcar.filter_mono (ae_mono hdom)
  exact (ae_map_iff hf.measurable.aemeasurable
    (isClosed_multiplicity_support config).measurableSet).mp hmap

omit [T2Space X] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
/-- The original plan support relation survives arbitrary joint vague limits. -/
theorem supportedOverConfiguration_of_tendsto
    (f : X → Y) (hf : Continuous f)
    {I : Type*} {l : Filter I} [NeBot l]
    {config : I → LocalConfiguration base} {μ : I → LocalFiniteMeasure X}
    {limit : LocalConfiguration base} {ν : LocalFiniteMeasure X}
    (hc : Tendsto config l (𝓝 limit)) (hμ : Tendsto μ l (𝓝 ν))
    (hs : ∀ᶠ i in l, SupportedOverConfiguration f (config i) (μ i)) :
    SupportedOverConfiguration f limit ν := by
  intro x hx
  change multiplicity limit (f x) ≠ 0
  intro hxzero
  obtain ⟨r, hr, hno⟩ := eventually_no_atom_near_of_tendsto hc hxzero
  have hnull : ∀ᶠ i in l, (μ i : Measure X) (f ⁻¹' Metric.ball (f x) r) = 0 := by
    filter_upwards [hs, hno] with i hi hni
    apply measure_mono_null _ (Measure.measure_compl_support (μ := (μ i : Measure X)))
    intro y hy hySupp
    exact (hi y hySupp) (hni (f y) hy)
  have hopen : IsOpen (f ⁻¹' Metric.ball (f x) r) := Metric.isOpen_ball.preimage hf
  have hzero : (ν : Measure X) (f ⁻¹' Metric.ball (f x) r) ≤ 0 :=
    (LocalFiniteMeasure.lowerSemicontinuous_measure_open hopen |>.isClosed_preimage 0).mem_of_tendsto hμ (hnull.mono fun i hi ↦ hi.le)
  exact (not_lt_of_ge hzero) ((Measure.mem_support_iff_forall x).mp hx _
    (hopen.mem_nhds (Metric.mem_ball_self hr)))

/-- Closedness needs no properness of the target projection. -/
theorem isClosed_supportedOverConfiguration (f : X → Y) (hf : Continuous f) :
    IsClosed {p : LocalConfiguration base × LocalFiniteMeasure X |
      SupportedOverConfiguration f p.1 p.2} := by
  apply IsSeqClosed.isClosed
  intro p q hp hlim
  exact supportedOverConfiguration_of_tendsto f hf
    (continuous_fst.tendsto q |>.comp hlim)
    (continuous_snd.tendsto q |>.comp hlim) (Eventually.of_forall hp)

omit [T2Space X] [LocallyCompactSpace X] [BorelSpace X] [PseudoMetrizableSpace X]
  [SigmaCompactSpace X] [ProperSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [SecondCountableTopology Y] in
/-- The retained integer cloud provides the countable target carrier for the
actual diffuse plan, without an atomic-plan assumption. -/
theorem SupportedOverConfiguration.countable_carrier
    {f : X → Y} (hf : Continuous f) {config : LocalConfiguration base}
    {μ : LocalFiniteMeasure X} (h : SupportedOverConfiguration f config μ) :
    (Function.support (multiplicity config)).Countable ∧
      ∀ᵐ x ∂(μ : Measure X), f x ∈ Function.support (multiplicity config) :=
  ⟨countable_multiplicity_support config,
    (supportedOverConfiguration_iff_ae_mem f hf config μ).mp h⟩

section Laws
variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

/-- The same original joint scene retains plan support on its own integer cloud
under weak convergence of laws. -/
theorem ae_supportedOverConfiguration_of_weak_tendsto
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto Pn atTop (𝓝 P))
    (f : X → Y) (hf : Continuous f)
    (config : Ω → LocalConfiguration base) (μ : Ω → LocalFiniteMeasure X)
    (hc : Continuous config) (hμ : Continuous μ)
    (hs : ∀ n, ∀ᵐ ω ∂(Pn n : Measure Ω),
      SupportedOverConfiguration f (config ω) (μ ω)) :
    ∀ᵐ ω ∂(P : Measure Ω), SupportedOverConfiguration f (config ω) (μ ω) := by
  exact OTSelector.Probability.ae_mem_closed_of_tendsto P Pn hweak _
    ((isClosed_supportedOverConfiguration f hf).preimage (hc.prodMk hμ)) hs

end Laws
end OTSelector.Probability
