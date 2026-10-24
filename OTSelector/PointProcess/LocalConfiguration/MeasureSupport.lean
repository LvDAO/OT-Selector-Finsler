import OTSelector.MeasureTheory.FiniteMultisetEncoding
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
import OTSelector.PointProcess.LocalConfiguration
import OTSelector.PointProcess.LocalConfiguration.AtomLimit
import OTSelector.PointProcess.LocalConfiguration.Borel
import OTSelector.PointProcess.LocalConfiguration.Polish
import OTSelector.PointProcess.LocalConfiguration.Support
import OTSelector.PointProcess.LocalConfigurationTestIntegral
import OTSelector.Probability.WeakClosedConstraint
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.LocalFiniteMeasureConfigurationSupport.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.LocalFiniteMeasureConfigurationSupport`; the selected original proof blocks follow. -/
section

/-!
# PointProcess.LocalConfiguration.MeasureSupport

Conditions: A proper second-countable metric Borel carrier, its actual integer cloud and locally finite weighted measure; law transfer has the stated weak-convergence and continuity hypotheses.
Objects: The closed relation that a weighted measure is carried by occupied cloud sites, and the corresponding countable almost-everywhere carrier.
Proof detail: At a vacant limit site find eventually vacant neighborhoods, use lower semicontinuity of open mass to exclude limiting weighted mass, then apply the shared weak closed-constraint lemma.

## Mathematical sources

- Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*: Section 2.4, Definition 2.11 and following integer-ball exhaustion criterion, p. 16. https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=28
- D. H. Fremlin, *Measure Theory, Volume 4*: Section 411N(a)–(d), p. 6: self-supporting sets and the unique full-measure closed support. https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=6
- D. H. Fremlin, *Measure Theory, Volume 4*: Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation. https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61

Source relation: A locally proved joint-configuration/weighted-measure closedness theorem and Portmanteau corollary. Keeping both coordinates in the same law is part of the statement; independent replacement is not used.
-/

/-!
# Weighted support survives a joint limit with the original integer cloud

The relation that a locally finite measure is carried by an actual integer
configuration is closed. Vacant limit sites have eventually vacant neighborhoods;
lower semicontinuity of open mass then excludes weighted mass there. Keeping
the two objects in the same probability law preserves this relation in a weak
limit and supplies a countable target support.
-/

open Function Filter MeasureTheory Set Topology TopologicalSpace
open scoped Classical ENNReal

noncomputable section
namespace OTSelector.Probability

open PointProcess PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] {base : X}

local instance localFiniteMeasureConfigurationSupportLocalInst1 : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance localFiniteMeasureConfigurationSupportLocalInst2 : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance localFiniteMeasureConfigurationSupportLocalInst3 : PolishSpace (LocalConfiguration base) := vaguePolishSpace

/-- The weighted measure uses only occupied sites of the original integer cloud. -/
def SupportedOnConfiguration (config : LocalConfiguration base)
    (μ : LocalFiniteMeasure X) : Prop :=
  (μ : Measure X).support ⊆ Function.support (multiplicity config)

omit [ProperSpace X] [BorelSpace X] in
theorem supportedOnConfiguration_iff_ae_mem (config : LocalConfiguration base)
    (μ : LocalFiniteMeasure X) :
    SupportedOnConfiguration config μ ↔
      ∀ᵐ x ∂(μ : Measure X), x ∈ Function.support (multiplicity config) := by
  constructor
  · intro h
    have hs : ∀ᵐ x ∂(μ : Measure X), x ∈ (μ : Measure X).support :=
      Measure.support_mem_ae
    exact hs.mono h
  · exact Measure.support_subset_of_isClosed (isClosed_multiplicity_support config)

/-- Joint vague convergence retains the original weighted support relation. -/
theorem supportedOnConfiguration_of_tendsto
    {ι : Type*} {l : Filter ι} [NeBot l]
    {config : ι → LocalConfiguration base} {μ : ι → LocalFiniteMeasure X}
    {limit : LocalConfiguration base} {ν : LocalFiniteMeasure X}
    (hc : Tendsto config l (𝓝 limit)) (hμ : Tendsto μ l (𝓝 ν))
    (hs : ∀ᶠ i in l, SupportedOnConfiguration (config i) (μ i)) :
    SupportedOnConfiguration limit ν := by
  intro x hx
  change multiplicity limit x ≠ 0
  intro hxzero
  obtain ⟨r, hr, hno⟩ := eventually_no_atom_near_of_tendsto hc hxzero
  have hnull : ∀ᶠ i in l, (μ i : Measure X) (Metric.ball x r) = 0 := by
    filter_upwards [hs, hno] with i hi hni
    apply measure_mono_null _ (Measure.measure_compl_support (μ := (μ i : Measure X)))
    intro y hy hySupp
    exact (hi hySupp) (hni y hy)
  have hzero : (ν : Measure X) (Metric.ball x r) ≤ 0 :=
    (LocalFiniteMeasure.lowerSemicontinuous_measure_open Metric.isOpen_ball
      |>.isClosed_preimage 0).mem_of_tendsto hμ (hnull.mono fun i hi ↦ hi.le)
  exact (not_lt_of_ge hzero)
    ((Measure.mem_support_iff_forall x).mp hx _ (Metric.ball_mem_nhds x hr))

/-- A closed relation on the actual cloud and diffuse-measure product carrier. -/
theorem isClosed_supportedOnConfiguration :
    IsClosed {p : LocalConfiguration base × LocalFiniteMeasure X |
      SupportedOnConfiguration p.1 p.2} := by
  apply IsSeqClosed.isClosed
  intro p q hp hlim
  exact supportedOnConfiguration_of_tendsto
    (continuous_fst.tendsto q |>.comp hlim)
    (continuous_snd.tendsto q |>.comp hlim) (Eventually.of_forall hp)

omit [ProperSpace X] [BorelSpace X] in
/-- Retaining the original integer cloud supplies an actual countable carrier
for the weighted target, even when the total measure is infinite. -/
theorem SupportedOnConfiguration.countable_carrier
    {config : LocalConfiguration base} {μ : LocalFiniteMeasure X}
    (h : SupportedOnConfiguration config μ) :
    (Function.support (multiplicity config)).Countable ∧
      ∀ᵐ x ∂(μ : Measure X), x ∈ Function.support (multiplicity config) :=
  ⟨countable_multiplicity_support config, (supportedOnConfiguration_iff_ae_mem _ _).mp h⟩

section Laws

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

/-- Every weak limit of the same original joint laws retains weighted support
on its own integer-cloud coordinate. No independent replacement is used. -/
theorem ae_supportedOnConfiguration_of_weak_tendsto
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto Pn atTop (𝓝 P))
    (config : Ω → LocalConfiguration base) (μ : Ω → LocalFiniteMeasure X)
    (hc : Continuous config) (hμ : Continuous μ)
    (hs : ∀ n, ∀ᵐ ω ∂(Pn n : Measure Ω), SupportedOnConfiguration (config ω) (μ ω)) :
    ∀ᵐ ω ∂(P : Measure Ω), SupportedOnConfiguration (config ω) (μ ω) := by
  exact OTSelector.Probability.ae_mem_closed_of_tendsto P Pn hweak _
    (isClosed_supportedOnConfiguration.preimage (hc.prodMk hμ)) hs

end Laws
end OTSelector.Probability

end
end
