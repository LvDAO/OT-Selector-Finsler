import OTSelector.PointProcess.LocalConfiguration
import OTSelector.PointProcess.LocalConfiguration.CountingSupport
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerOriginalCountingMassBridge.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerOriginalCountingMassBridge`; the selected original proof blocks follow. -/
section

/-!
# PointProcess.LocalConfiguration.MassBridge

Conditions: A multiset or a metric local configuration, a finite observation radius, and the explicit monotonicity/injectivity hypotheses of each cardinality statement.
Objects: Membership-indicator multiset cardinality, occupied finite-window supports and their monotone support counts.
Proof detail: Sum the membership indicator over the actual multiset, use the existing shell/window membership equivalence, then apply finset cardinality monotonicity.

## Mathematical sources

- Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*: Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10. https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22
- Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*: Section 2.4, Definition 2.11 and following integer-ball exhaustion criterion, p. 16. https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=28

Source relation: Elementary finite counting adapters for locally finite counting measures. Cardinality of occupied sites is distinguished from total multiplicity; no unproved scene-to-edge bijection is claimed.
-/

/-!
# Counting total mass and the scene-to-cloud bridge

This module attempts the two sub-gaps of
FinslerOriginalCountingSupportCardinality.

(i) **Total mass identity.**  The counting-measure mass of a window support is
the sum of the shell cardinalities over the shells inside the window,
  countingMeasure config (windowSupport config N) = sum over n < N of (config n).card.
We prove the pure multiset cardinality identity that underlies the shell
computation: summing the indicator of multiset membership over a multiset gives
its cardinality.

(ii) **Scene-to-cloud bridge.**  There is no measurable map from the scene
counting measure on LegalMarkedPhysicalEdge q to the cloud colour labels in the
current library.  The exact missing bridge is a measurable edge-index map whose
image is the scene support (the scene support is the range of a matching
assignment).  We record the finite envelope of that bridge.

1. **multiset_sum_indicator_toFinset**: summing the membership indicator over a
   multiset gives its cardinality (the pure counting identity behind the shell
   mass computation).

2. **shell_mem_windowSupport_iff**: an occupied shell point lies in the window
   support exactly when its shell index is inside the window.

3. **finite_windowSupport**: the window support is a finite set of points.

4. **card_windowSupport_mono_of_le**: the occupied-point count is monotone in
   the window size (the count interface used by the missing-cardinality defect).
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Multiset membership-indicator cardinality identity.**  Summing the
indicator of membership in the multiset's own toFinset over the multiset gives
its cardinality.  This is the pure counting identity behind the shell mass. -/
theorem multiset_sum_indicator_toFinset {X : Type*} [DecidableEq X]
    (m : Multiset X) :
    (m.map (fun x => if x ∈ m.toFinset then (1 : ℝ≥0∞) else 0)).sum =
      (m.card : ℝ≥0∞) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
      rw [Multiset.map_cons, Multiset.sum_cons]
      have hinner : (m.map (fun x => if x ∈ (a ::ₘ m).toFinset then (1 : ℝ≥0∞) else 0)) =
          m.map (fun x => if x ∈ m.toFinset then (1 : ℝ≥0∞) else 0) := by
        apply Multiset.map_congr rfl
        intro x hx
        have hxm : x ∈ m.toFinset := Multiset.mem_toFinset.mpr hx
        have hxa : x ∈ (a ::ₘ m).toFinset :=
          Multiset.mem_toFinset.mpr (Multiset.mem_cons_of_mem hx)
        simp only [hxm, hxa, ite_true]
      rw [hinner, ih]
      have ha : a ∈ (a ::ₘ m).toFinset :=
        Multiset.mem_toFinset.mpr (Multiset.mem_cons_self a m)
      rw [Multiset.card_cons, Nat.cast_add, Nat.cast_one]
      simp only [ha, ite_true]
      exact add_comm _ _

/-- **Shell membership in the window support.**  An occupied point of shell n
lies in the window support of size N exactly when n < N and its multiplicity is
nonzero. -/
theorem shell_mem_windowSupport_iff {X : Type*} [MetricSpace X] {base : X}
    (config : LocalConfiguration base) (N n : ℕ) (x : LocalConfiguration.Shell base n) :
    x.val ∈ LocalConfiguration.windowSupport config N ↔
      n < N ∧ LocalConfiguration.multiplicity config x.val ≠ 0 := by
  simpa only [x.property] using
    LocalConfiguration.mem_windowSupport_iff config N x.val

/-- **Finiteness of the window support.**  The window support of a
configuration is a finite set of points. -/
theorem finite_windowSupport {X : Type*} [MetricSpace X] {base : X}
    (config : LocalConfiguration base) (N : ℕ) :
    (LocalConfiguration.windowSupport config N : Set X).Finite :=
  Finset.finite_toSet _

/-- **Monotone window support count.**  The occupied-point count is monotone in
the window size; this is the count interface used by the missing-cardinality
defect when the window grows. -/
theorem card_windowSupport_mono_of_le {X : Type*} [MetricSpace X] {base : X}
    (config : LocalConfiguration base) {N M : ℕ} (hNM : N ≤ M) :
    (LocalConfiguration.windowSupport config N).card ≤
      (LocalConfiguration.windowSupport config M).card :=
  card_windowSupport_mono config hNM

end OTSelector.Reconstruction

end
end
