import OTSelector.MeasureTheory.FiniteMultisetEncoding
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasurePolish
import OTSelector.PointProcess.LocalConfiguration
import OTSelector.PointProcess.LocalConfiguration.Borel
import OTSelector.PointProcess.LocalConfiguration.Compactness
import OTSelector.PointProcess.LocalConfiguration.Integral
import OTSelector.PointProcess.LocalConfiguration.Tightness
import OTSelector.PointProcess.LocalConfigurationMeasure
import OTSelector.PointProcess.LocalConfigurationTestIntegral

/-!
Conditions: A proper second-countable metric Borel point space and the already established Polish space of locally finite measures, with the actual configuration vague topology.

Objects: The configuration-to-counting-measure injection is continuous and a closed embedding; its source is Polish. A convergent sequence of its measure images lies in one compact configuration set.

Proof detail: Convergent compact-test integrals bound shell counts. The closed-annulus compactness construction supplies compact containment, which gives closedness of the image; transfer Polishness across the closed embedding.

References: D. H. Fremlin: 4A2O(d), 4A2P(a)(i–v), 4A2Q(a–e) and proofs, pp. 23–25; D. H. Fremlin: 4A2L(f), p. 22; 4A2P(a)(ii),(v),(c), p. 24; 4A2G(f), p. 16.
Relation: The closedness of integer configurations is a local proof for the original carrier. The cited Polish-subspace theorem applies after that proof; the Kallenberg chapter opening supplies the vague-measure context only, not an uninspected exact theorem.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.PointProcess.LocalConfigurationPolish.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.PointProcess.LocalConfigurationPolish`; the selected original proof blocks follow. -/
section

/-!
# The actual integer cloud is a closed subspace of locally finite measures

Vague convergence bounds compact test integrals, hence the original shell counts.
The existing annulus compactness construction then retains a limiting integer
configuration. This proves Polishness without replacing the original cloud law.
-/

open Function Filter MeasureTheory Set Topology TopologicalSpace
open scoped Classical CompactlySupported ENNReal

noncomputable section
namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X] {base : X}

local instance localConfigurationPolishLocalInst1 : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance localConfigurationPolishLocalInst2 : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance localConfigurationPolishLocalInst3 : T2Space (LocalConfiguration base) := vagueT2Space

/-- The original counting measure, viewed on the actual compact-test carrier. -/
def toLocalFiniteMeasure (config : LocalConfiguration base) :
    Probability.LocalFiniteMeasure X :=
  ⟨countingMeasure config, inferInstance⟩

@[simp]
theorem testIntegral_toLocalFiniteMeasure (config : LocalConfiguration base)
    (f : C_c(X, ℝ)) :
    Probability.LocalFiniteMeasure.testIntegral (toLocalFiniteMeasure config) f =
      testIntegral config f :=
  integral_countingMeasure config f

theorem continuous_toLocalFiniteMeasure :
    Continuous (toLocalFiniteMeasure : LocalConfiguration base → _) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  simpa only [Function.comp_def, testIntegral_toLocalFiniteMeasure] using
    continuous_testIntegral (base := base) f

theorem toLocalFiniteMeasure_injective :
    Injective (toLocalFiniteMeasure : LocalConfiguration base → _) := by
  intro c d h
  exact countingMeasure_injective (congrArg Subtype.val h)

/-- A convergent sequence of the actual counting measures has uniformly bounded
shell counts and is contained in one compact family of original configurations. -/
theorem exists_isCompact_of_countingMeasure_tendsto
    (config : ℕ → LocalConfiguration base) {μ : Probability.LocalFiniteMeasure X}
    (h : Tendsto (toLocalFiniteMeasure ∘ config) atTop (𝓝 μ)) :
    ∃ K : Set (LocalConfiguration base), IsCompact K ∧ ∀ n, config n ∈ K := by
  have hcounts : ∀ k, ∃ N : ℕ, ∀ n, (config n k).card ≤ N := by
    intro k
    let f := distanceTent base ((k : ℝ) + 2)
    have htest :=
      ((Probability.LocalFiniteMeasure.continuous_testIntegral f).tendsto μ).comp h
    obtain ⟨b, hb⟩ := htest.bddAbove_range
    obtain ⟨N, hN⟩ := exists_nat_gt b
    refine ⟨N, fun n ↦ ?_⟩
    have hmass : countingMeasure (config n) (Metric.ball base ((k : ℝ) + 1)) ≤
        ENNReal.ofReal (testIntegral (config n) f) := by
      rw [← integral_countingMeasure]
      apply f.integrable.measure_le_integral
      · exact Eventually.of_forall (fun x ↦ le_max_left _ _)
      · intro x hx
        change dist x base < (k : ℝ) + 1 at hx
        exact (show (1 : ℝ) ≤ (k : ℝ) + 2 - dist x base by linarith).trans
          (le_max_right _ _)
    have hs := shellCard_le_countingMeasure_ball (config n) k
    have hb' : testIntegral (config n) f ≤ b := by
      simpa only [Function.comp_def, testIntegral_toLocalFiniteMeasure] using
        hb (mem_range_self n)
    have hcast : ((config n k).card : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
      apply hs.trans
      simpa only [Nat.cast_add, Nat.cast_one, ENNReal.ofReal_natCast] using
        hmass.trans (ENNReal.ofReal_le_ofReal (hb'.trans hN.le))
    exact_mod_cast hcast
  choose N hN using hcounts
  obtain ⟨K, hK, hsub⟩ := exists_isCompact_superset_shellCard_le (base := base) N
  exact ⟨K, hK, fun n ↦ hsub (fun k ↦ hN k n)⟩

/-- Closed configuration families remain closed among all locally finite measures. -/
theorem isClosedMap_toLocalFiniteMeasure :
    IsClosedMap (toLocalFiniteMeasure : LocalConfiguration base → _) := by
  intro A hA
  apply IsSeqClosed.isClosed
  intro μ ν hμ hlim
  choose c hc heq using hμ
  have hseq : toLocalFiniteMeasure ∘ c = μ := funext heq
  have hcLim : Tendsto (toLocalFiniteMeasure ∘ c) atTop (𝓝 ν) := by
    rw [hseq]
    exact hlim
  obtain ⟨K, hK, hcK⟩ := exists_isCompact_of_countingMeasure_tendsto c hcLim
  obtain ⟨d, _, φ, hφ, hd⟩ := isSeqCompact_of_isCompact hK hcK
  refine ⟨d, hA.mem_of_tendsto hd (Eventually.of_forall fun n ↦ hc (φ n)), ?_⟩
  exact tendsto_nhds_unique (continuous_toLocalFiniteMeasure.tendsto d |>.comp hd)
    (hcLim.comp hφ.tendsto_atTop)

/-- Integer counting measures form an actual closed subspace of diffuse measures. -/
theorem isClosedEmbedding_toLocalFiniteMeasure :
    IsClosedEmbedding (toLocalFiniteMeasure : LocalConfiguration base → _) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap continuous_toLocalFiniteMeasure
    toLocalFiniteMeasure_injective isClosedMap_toLocalFiniteMeasure

/-- The original configuration topology is Polish, with its existing shell Borel law. -/
theorem vaguePolishSpace : PolishSpace (LocalConfiguration base) :=
  isClosedEmbedding_toLocalFiniteMeasure.polishSpace

end OTSelector.PointProcess.LocalConfiguration

end
end
