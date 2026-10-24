import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import OTSelector.Probability.RowProbabilityFilter
import OTSelector.Probability.RowScaling

/-!
Conditions: Probability rows and actual real observations whose centered fluctuations vanish in outer probability; deterministic means converge, or only their positive deficit below the target vanishes.

Objects: Full row-filter convergence to the target, or row-filter convergence of the positive target deficit to zero.

Proof detail: Transfer centered probability convergence to the row filter, add the deterministic mean limit, and use continuity/Lipschitz control of the positive-part map for the one-sided variant.

References: D. H. Fremlin: Section 245, especially 245A–245E, convergence in measure and its topology; Rick Durrett: Section 1.4, Theorem 1.4.7, p. 23; Section 1.6, positive/negative parts p. 28 and Theorem 1.6.1, p. 29.
Relation: An elementary varying-space Slutsky-type filter argument. The type uses the actual totalized integral values and does not add an integrability premise absent from the header.
-/


/-!
# Recovering row probability limits from centered fluctuations and means

This deterministic filter argument combines centered convergence in probability
with convergence of expectations. Its one-sided version needs only the positive
part of the deficit of the mean, as required by the pressure selector.
-/

open Filter MeasureTheory
open scoped Topology

namespace OTSelector.Probability

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Centered fluctuations and mean convergence give convergence in the original row filter. -/
theorem tendsto_row_of_centered_of_mean
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (F : (Σ n, Ω n) → ℝ) (p : ℝ)
    (hcenter : ∀ ε, 0 < ε → Tendsto (fun n ↦ (P n).real
      {ω | ε ≤ |F ⟨n, ω⟩ - ∫ ω', F ⟨n, ω'⟩ ∂P n|}) atTop (𝓝 0))
    (hmean : Tendsto (fun n ↦ ∫ ω, F ⟨n, ω⟩ ∂P n) atTop (𝓝 p)) :
    Tendsto F (rowProbabilityFilter P) (𝓝 p) := by
  have hz : Tendsto (fun z ↦ F z - ∫ ω, F ⟨z.1, ω⟩ ∂P z.1)
      (rowProbabilityFilter P) (𝓝 0) := by
    apply (tendsto_rowProbabilityFilter_real_iff P _ _).mpr
    simpa only [sub_zero] using hcenter
  have hm := hmean.comp (tendsto_rowIndex_atTop P)
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using hz.add hm

/-- The lower pressure condition needs only a vanishing deficit of the expectation. -/
theorem tendsto_row_posPart_of_centered_of_meanLower
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (F : (Σ n, Ω n) → ℝ) (p : ℝ)
    (hcenter : ∀ ε, 0 < ε → Tendsto (fun n ↦ (P n).real
      {ω | ε ≤ |F ⟨n, ω⟩ - ∫ ω', F ⟨n, ω'⟩ ∂P n|}) atTop (𝓝 0))
    (hmean : Tendsto (fun n ↦ max (p - ∫ ω, F ⟨n, ω⟩ ∂P n) 0) atTop (𝓝 0)) :
    Tendsto (fun z ↦ max (p - F z) 0) (rowProbabilityFilter P) (𝓝 0) := by
  have hz : Tendsto (fun z ↦ F z - ∫ ω, F ⟨z.1, ω⟩ ∂P z.1)
      (rowProbabilityFilter P) (𝓝 0) := by
    apply (tendsto_rowProbabilityFilter_real_iff P _ _).mpr
    simpa only [sub_zero] using hcenter
  have hb := (hmean.comp (tendsto_rowIndex_atTop P)).add hz.abs
  simp only [abs_zero, add_zero] at hb
  apply squeeze_zero (fun _ ↦ le_max_right _ _) ?_ hb
  intro z
  dsimp only [Function.comp_apply]
  apply max_le
  · have h₁ := le_max_left (p - ∫ ω, F ⟨z.1, ω⟩ ∂P z.1) 0
    have h₂ := neg_le_abs (F z - ∫ ω, F ⟨z.1, ω⟩ ∂P z.1)
    linarith
  · exact add_nonneg (le_max_right _ _) (abs_nonneg _)

end OTSelector.Probability
