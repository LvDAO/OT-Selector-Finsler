import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import OTSelector.Probability.RowProbabilityFilter

/-!
Conditions: Finite row measures, with no probability normalization needed; real exponent a>0 or q>0 for the stated power specializations.

Objects: Divergence of the row index and of its positive real sample-size powers under the actual row-probability filter.

Proof detail: A deterministic eventually-in-row property has an empty failure event after its row threshold. Compose this index limit with the elementary positive-power divergence.

References: D. H. Fremlin: Section 245, especially 245A–245E, convergence in measure and its topology; Terence Tao: Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test).
Relation: A deterministic normalization adapter for the varying-row filter. The distance-pressure scale name does not add a theorem about pressure or geometry.
-/


/-!
# Deterministic scales under the original row probability filter

The row index tends to infinity regardless of how the finite row measures vary. Consequently
ordinary deterministic limits transfer to that filter. In particular, the positive scale
`(n + 1)^(2/q)` used by the empirical distance pressure diverges for every `q > 0`.
This is only a normalization lemma; it supplies no pressure convergence or dimensional geometry.
-/

open Filter MeasureTheory
open scoped Topology

namespace OTSelector.Probability

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Eventually large row indices hold with zero failure mass, without restrictions on row masses. -/
theorem tendsto_rowIndex_atTop (P : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (P n)] :
    Tendsto (fun z : Σ n, Ω n ↦ z.1) (rowProbabilityFilter P) atTop := by
  rw [Filter.tendsto_atTop]
  intro N
  apply (eventually_rowProbabilityFilter_iff P _).mpr
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  simp only [hn, not_true_eq_false, Set.ofPred_false, measureReal_empty]

/-- Every positive real power of the positive sample size diverges under the row filter. -/
theorem tendsto_sampleSize_rpow_row (P : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (P n)]
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun z : Σ n, Ω n ↦ ((z.1 + 1 : ℕ) : ℝ) ^ a)
      (rowProbabilityFilter P) atTop := by
  exact (tendsto_rpow_atTop ha).comp
    (tendsto_natCast_atTop_atTop.comp
      ((tendsto_add_atTop_nat 1).comp (tendsto_rowIndex_atTop P)))

/-- The manuscript's quadratic pressure scale diverges for every positive effective dimension. -/
theorem tendsto_distancePressureScale_row
    (P : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (P n)] (q : ℝ) (hq : 0 < q) :
    Tendsto (fun z : Σ n, Ω n ↦ ((z.1 + 1 : ℕ) : ℝ) ^ (2 / q))
      (rowProbabilityFilter P) atTop :=
  tendsto_sampleSize_rpow_row P (2 / q) (div_pos (by norm_num) hq)

end OTSelector.Probability
