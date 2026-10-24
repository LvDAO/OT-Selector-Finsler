import OTSelector.MeasureTheory.Lp.SummableSeries
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.FinitePrefixTrafficSummation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.FinitePrefixTrafficSummation`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.Lp.FinitePrefixSummation

## Lemma skeleton

* **Conditions:** Every natural-index real level is L2 and norms are summable after a fixed finite prefix.
* **Objects:** L2 of the full pointwise sum, global norm summability and almost-everywhere absolute convergence.
* **Proof detail:** Add the finitely many finite prefix norms to the summable shifted tail and apply the countable L2 series theorem.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=219): Section 7B, Theorem 7.20 and proof, pp. 204–205; Theorem 7.24, p. 205.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=214): Section 7A, Theorem 7.14, p. 199 (Minkowski).

Source relation (composition): Finite-prefix series extension; no common prefix bound is required.
-/

/-! A finite collection of already square-integrable traffic levels can be
adjoined to a tail with summable L2 norms, without a uniform prefix bound. -/
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Probability

/-- Summability of the tail norms suffices for the literal full series when
every omitted prefix level is already L2. The full real norm series and
almost sure absolute convergence are produced at the same time. -/
theorem memLp_tsum_of_summable_tail_norm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (level : ℕ→Ω→ℝ) (hLp : ∀j,MemLp (level j) 2 P)
    (J : ℕ) (htail : Summable (fun j↦(eLpNorm (level (j+J)) 2 P).toReal)) :
    MemLp (fun scene↦∑'j,level j scene) 2 P ∧
      Summable (fun j↦(eLpNorm (level j) 2 P).toReal) ∧
      ∀ᵐscene∂P,Summable (fun j↦‖level j scene‖) := by
  have hnorm : Summable (fun j↦(eLpNorm (level j) 2 P).toReal) :=
    (summable_nat_add_iff J).mp htail
  have hbound (j : ℕ) : eLpNorm (level j) 2 P ≤
      ENNReal.ofReal (eLpNorm (level j) 2 P).toReal := by
    rw [ENNReal.ofReal_toReal (hLp j).2.ne]
  have h := memLp_tsum_of_summable_level_bound P level hLp
    (fun j↦(eLpNorm (level j) 2 P).toReal) hnorm
    (fun _↦ENNReal.toReal_nonneg) hbound
  exact ⟨h.1,hnorm,h.2.2⟩

end OTSelector.Probability

end
end
