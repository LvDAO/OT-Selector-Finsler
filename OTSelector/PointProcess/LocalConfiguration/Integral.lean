import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.CompactlySupported
import OTSelector.PointProcess.LocalConfiguration
import OTSelector.PointProcess.LocalConfigurationMeasure
import OTSelector.PointProcess.LocalConfigurationTestIntegral
import OTSelector.PointProcess.LocalConfigurationWindow

/-!
Conditions: A metric Borel point space, finite multisets and their actual Dirac-sum measures; the counting-measure assertions test compactly supported continuous real functions.

Objects: Integrability and exact finite-sum integral identities for shell measures, and equality of the genuine locally finite counting integral with the configuration test sum.

Proof detail: Induct over finite multisets to integrate Dirac sums. Compact support reduces the locally finite counting measure to finitely many shells and then to the already proved finite test sum.

References: Günter Last; Mathew Penrose: Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10; Günter Last; Mathew Penrose: Section 2.4, Definition 2.11 and following integer-ball exhaustion criterion, p. 16.
Relation: These identities connect the existing measurable point code to ordinary Bochner integrals and retain multiplicities; no convergence or tightness theorem is asserted here.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.PointProcess.LocalConfigurationIntegral.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.PointProcess.LocalConfigurationIntegral`; the selected original proof blocks follow. -/
section

/-!
# Counting-measure integrals agree with finite configuration sums

The test integrals defining the vague topology are the ordinary Bochner integrals against the
actual locally finite counting measure.  Thus the measurable code and deterministic test-sum
interface refer to the same point process, including multiplicities.
-/

open MeasureTheory Set Topology
open scoped BigOperators Classical CompactlySupported

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {base : X}

private theorem integrable_sum_dirac (m : Multiset X) (f : X → ℝ) :
    Integrable f (m.map Measure.dirac).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact (integrable_dirac (by simp)).add_measure ih

private theorem integral_sum_dirac (m : Multiset X) (f : X → ℝ) :
    (∫ x, f x ∂(m.map Measure.dirac).sum) = (m.map f).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [integral_add_measure (integrable_dirac (by simp)) (integrable_sum_dirac m f)]
      simp only [integral_dirac, ih]

/-- The integral over one shell is the finite sum of point values, including repetitions. -/
theorem integral_shellMeasure (config : LocalConfiguration base) (n : ℕ) (f : X → ℝ) :
    (∫ x, f x ∂shellMeasure config n) =
      ((config n).map (fun x ↦ f x.val)).sum := by
  have h := integral_sum_dirac ((config n).map Subtype.val) f
  simpa only [shellMeasure, Multiset.map_map, Function.comp_def] using h

/-- Every compactly supported continuous test is integrable against the actual point measure. -/
theorem integrable_countingMeasure (config : LocalConfiguration base) (f : C_c(X, ℝ)) :
    Integrable f (countingMeasure config) :=
  f.integrable

/-- The actual Bochner integral equals the configuration test integral used by the vague topology. -/
theorem integral_countingMeasure (config : LocalConfiguration base) (f : C_c(X, ℝ)) :
    (∫ x, f x ∂countingMeasure config) = testIntegral config f := by
  obtain ⟨N, hN⟩ := exists_testSupport_subset_ball f base
  rw [testIntegral_eq_sum_map_window config f hN, sum_map_window]
  change (∫ x, f x ∂Measure.sum (shellMeasure config)) = _
  rw [integral_sum_measure (integrable_countingMeasure config f)]
  simp_rw [integral_shellMeasure]
  apply tsum_eq_sum
  intro n hn
  have hnot : ¬ n < N := Finset.mem_range.mpr.mt hn
  apply Multiset.sum_eq_zero
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
  by_contra hfx
  have hxN := hN (subset_tsupport (fun x ↦ f x) hfx)
  have hindex := (shellIndex_lt_iff base x.val N).mpr hxN
  exact hnot (x.property ▸ hindex)

end OTSelector.PointProcess.LocalConfiguration

end
