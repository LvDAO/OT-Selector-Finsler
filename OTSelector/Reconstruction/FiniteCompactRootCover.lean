import OTSelector.Reconstruction.FinslerPopulationFiniteSeedCore
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Finite compact subcores of a measurable root cover

A countable full-measure cover whose pieces admit arbitrarily accurate compact
cores has a finite compact subcover up to arbitrarily small original root mass.
Any property constructed on each compact core is retained with its original index.
-/

open Set MeasureTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

/-- Finite compact cores retain the original piecewise property and lose
arbitrarily little of the original finite root measure. -/
theorem exists_finite_compact_root_cores
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    (lambda : Measure Z) [IsFiniteMeasure lambda] (s : ℕ → Set Z)
    (hs : ∀ n, MeasurableSet (s n)) (hcover : ∀ᵐ z ∂lambda, z ∈ ⋃ n, s n)
    (P : ℕ → Set Z → Prop)
    (hcore : ∀ n, ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ K ⊆ s n, IsCompact K ∧ lambda (s n \ K) < ε ∧ P n K)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (N : ℕ) (K : Fin N → Set Z),
      lambda (⋃ n, K n)ᶜ < ε ∧ ∀ n, K n ⊆ s n ∧ IsCompact (K n) ∧ P n (K n) := by
  classical
  obtain ⟨N, hN⟩ := exists_initial_cover_measure_compl_lt lambda s hs hcover
    (ENNReal.half_pos hε).ne'
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' (ENNReal.half_pos hε).ne' ℕ
  choose K hKs hK hsmall hP using fun n ↦ hcore n (δ n) (hδ n).ne'
  have herr : lambda (⋃ n, s n \ K n) < ε / 2 :=
    (measure_iUnion_le _).trans_lt
      ((ENNReal.tsum_le_tsum fun n ↦ (hsmall n).le).trans_lt hsum)
  refine ⟨N, fun n ↦ K n, ?_, fun n ↦ ⟨hKs n, hK n, hP n⟩⟩
  have hsub : (⋃ n : Fin N, K n)ᶜ ⊆ (⋃ n < N, s n)ᶜ ∪ ⋃ n, s n \ K n := by
    intro z hz
    by_cases hzS : z ∈ ⋃ n < N, s n
    · obtain ⟨n, hn, hzn⟩ := mem_iUnion₂.mp hzS
      exact Or.inr (mem_iUnion.mpr ⟨n, hzn, fun hzK ↦
        hz (mem_iUnion.mpr ⟨⟨n, hn⟩, hzK⟩)⟩)
    · exact Or.inl hzS
  calc
    lambda (⋃ n : Fin N, K n)ᶜ ≤
        lambda (⋃ n < N, s n)ᶜ + lambda (⋃ n, s n \ K n) :=
      (measure_mono hsub).trans (measure_union_le _ _)
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hN herr
    _ = ε := ENNReal.add_halves ε

end OTSelector.Reconstruction
