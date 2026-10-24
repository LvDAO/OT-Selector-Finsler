import Mathlib.MeasureTheory.Measure.Prokhorov
import OTSelector.PointProcess.LocalConfiguration
import OTSelector.PointProcess.LocalConfigurationMeasure
import OTSelector.PointProcess.LocalConfigurationTestIntegral
import OTSelector.PointProcess.LocalConfigurationWindow

/-!
Conditions: The displayed metric/Borel/standard-Borel configuration context and a natural shell index.

Objects: Only the deterministic inequality: shell cardinality is at most the genuine counting mass of the containing integer-radius open ball.

Proof detail: The actual shell measure is dominated by the complete counting measure and the shell lies in the next open integer ball; compare their masses.

References: Günter Last; Mathew Penrose: Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10; Günter Last; Mathew Penrose: Section 2.4, Definition 2.11 and following integer-ball exhaustion criterion, p. 16.
Relation: Only one selected deterministic counting comparison is included. The original file’s Markov, tightness and weak-subsequence results are outside this core and are not claimed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.PointProcess.LocalConfigurationTightness.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.PointProcess.LocalConfigurationTightness`; the selected original proof blocks follow. -/
section

/-!
# Tightness from local counting estimates

Uniform tails for the actual shell counts give compact containment through closed-annulus
assembly.  Uniform finite first moments of actual counting measures on integer balls imply
these tails by Markov's inequality.  The resulting tightness yields weakly convergent
subsequences of configuration laws in the proved vague topology.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators Classical ENNReal NNReal

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
  [BorelSpace X] [StandardBorelSpace X] {base : X}

noncomputable local instance localConfigurationTightnessTopology :
    TopologicalSpace (LocalConfiguration base) := vagueTopology base





omit [ProperSpace X] [StandardBorelSpace X] in
/-- A shell count is bounded by the count in its enclosing integer-radius open ball. -/
theorem shellCard_le_countingMeasure_ball (config : LocalConfiguration base) (n : ℕ) :
    ((config n).card : ℝ≥0∞) ≤ countingMeasure config (Metric.ball base ((n + 1 : ℕ) : ℝ)) := by
  rw [countingMeasure_ball, card_window]
  exact_mod_cast Finset.single_le_sum (fun i _ ↦ Nat.zero_le (config i).card)
    (Finset.mem_range.mpr (Nat.lt_succ_self n))









end OTSelector.PointProcess.LocalConfiguration

end
