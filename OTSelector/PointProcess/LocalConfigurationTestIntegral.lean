import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import OTSelector.MeasureTheory.FiniteMultisetEncoding
import OTSelector.PointProcess.ConfigurationTopology
import OTSelector.PointProcess.LocalConfiguration
import OTSelector.PointProcess.LocalConfigurationWindow

/-!
# PointProcess.LocalConfigurationTestIntegral

Conditions: A metric carrier and a locally finite integer shell configuration; measurable statements require the explicit Borel and standard-Borel hypotheses in their signatures.
Objects: Multiplicity-weighted compactly supported tests, finite observation-window sums, and the initial vague topology.
Proof detail: Compact support meets finitely many occupied sites, so its integral is a finite window sum. Measurability follows from measurable finite sums; continuity follows from the defined initial topology.

## Mathematical sources

- Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*: Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10. https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22
- Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*: Section 2.4, Definition 2.11 and following integer-ball exhaustion criterion, p. 16. https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=28
- Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*: Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117. https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4

Source relation: A concrete encoding and finite-sum implementation of counting integrals and test-generated topology. No equality of shell-code measurability and vague Borel sets is inferred from individual-test measurability.
-/

/-!
# Actual test integrals of shell-coded configurations

Compactly supported test integrals are finite sums of the decoded point multiplicities.  They
agree with finite-window multiset sums and are therefore measurable in the shell code.  On the
existing marked-line carrier they agree exactly with `Configuration.testIntegral`.

The vague topology is the initial topology of these actual test integrals.  Its compatibility
with the shell-code measurable space is not asserted here: measurability of individual tests
alone does not justify the converse Borel-generation statement.
-/

open Function MeasureTheory Set Topology
open scoped BigOperators Classical CompactlySupported

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] {base : X}

/-- The multiplicity-weighted value of a point test. -/
noncomputable def testSummand (config : LocalConfiguration base) (f : C_c(X, ℝ)) (x : X) : ℝ :=
  (multiplicity config x : ℝ) * f x

theorem finite_support_testSummand (config : LocalConfiguration base) (f : C_c(X, ℝ)) :
    (Function.support (testSummand config f)).Finite := by
  have hfinite := (locallyFiniteSupport_multiplicity config).finite_inter_support_of_isCompact
    f.hasCompactSupport
  apply hfinite.subset
  intro x hx
  constructor
  · apply subset_tsupport
    intro hfx
    exact hx (by simp [testSummand, hfx])
  · intro hcx
    exact hx (by simp [testSummand, hcx])

/-- The actual integral against the locally finite integer configuration. -/
noncomputable def testIntegral (config : LocalConfiguration base) (f : C_c(X, ℝ)) : ℝ :=
  ∑ᶠ x, testSummand config f x

/-- A compactly supported test is contained in some integer-radius observation window. -/
theorem exists_testSupport_subset_ball (f : C_c(X, ℝ)) (base : X) :
    ∃ N : ℕ, tsupport f ⊆ Metric.ball base (N : ℝ) := by
  obtain ⟨R, hR⟩ := f.hasCompactSupport.isBounded.subset_ball base
  obtain ⟨N, hN⟩ := exists_nat_gt R
  exact ⟨N, hR.trans (Metric.ball_subset_ball hN.le)⟩

/-- Any finite window containing the test support computes the same integral. -/
theorem testIntegral_eq_sum_map_window (config : LocalConfiguration base)
    (f : C_c(X, ℝ)) {N : ℕ} (hN : tsupport f ⊆ Metric.ball base (N : ℝ)) :
    testIntegral config f = ((window config N).map (fun x ↦ f x)).sum := by
  have hs : Function.support (testSummand config f) ⊆ (window config N).toFinset := by
    intro x hx
    apply Multiset.mem_toFinset.mpr
    apply (mem_window_iff config N x).mpr
    have hf : f x ≠ 0 := by
      intro hfx
      exact hx (by simp [testSummand, hfx])
    have hc : multiplicity config x ≠ 0 := by
      intro hcx
      exact hx (by simp [testSummand, hcx])
    exact ⟨hN (subset_tsupport _ hf), hc⟩
  rw [testIntegral, finsum_eq_sum_of_support_subset _ hs]
  rw [Finset.sum_multiset_map_count]
  apply Finset.sum_congr rfl
  intro x hx
  have hxN := ((mem_window_iff config N x).mp (Multiset.mem_toFinset.mp hx)).1
  simp [testSummand, count_window, hxN, nsmul_eq_mul]

section Measurable

variable [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]

/-- Every actual compactly supported test integral is measurable in the shell encoding. -/
@[fun_prop]
theorem measurable_testIntegral (f : C_c(X, ℝ)) :
    Measurable (fun config : LocalConfiguration base ↦ testIntegral config f) := by
  obtain ⟨N, hN⟩ := exists_testSupport_subset_ball f base
  have h := measurable_sum_map_window (base := base) f.continuous.measurable N
  convert h using 1
  funext config
  exact testIntegral_eq_sum_map_window config f hN

end Measurable

/-- The initial topology of actual compactly supported point integrals.  This definition makes
no assertion that its Borel sets coincide with the shell-code measurable structure. -/
@[instance_reducible]
noncomputable def vagueTopology (base : X) : TopologicalSpace (LocalConfiguration base) :=
  ⨅ f : C_c(X, ℝ), TopologicalSpace.induced (fun config ↦ testIntegral config f) inferInstance

/-- Test integrals are continuous for the vague topology by construction. -/
theorem continuous_testIntegral (f : C_c(X, ℝ)) :
    Continuous[vagueTopology base, inferInstance]
      (fun config : LocalConfiguration base ↦ testIntegral config f) := by
  exact continuous_iInf_dom (i := f) continuous_induced_dom

/-- On marked-line configurations the shell integral equals the pre-existing deterministic
configuration integral, including multiplicities. -/
theorem testIntegral_eq_configuration_testIntegral
    {M : Type*} [MetricSpace M] {base : ℝ × M} (config : LocalConfiguration base)
    (f : C_c(ℝ × M, ℝ)) :
    testIntegral config f = Configuration.testIntegral (toLocallyFinsupp config) f :=
  rfl

end OTSelector.PointProcess.LocalConfiguration
