import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
## Lemma skeleton

* **Conditions:** Weakly convergent probability laws and an open event or a closed constraint set.
* **Objects:** Preserved upper bounds on open-event mass and almost-sure closed constraints.
* **Proof detail:** Apply Portmanteau to the open event or the complement of the closed constraint.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61

**Relationship to the sources:** The general-space corollaries use the exact separation/regularity hypotheses of mathlib; no finite-dimensional restriction is inserted.
-/

/-!
# Passing constraints through weak convergence of laws

The objects are probability laws on one topological measurable carrier. These lemmas expose the
Portmanteau step separately from the mathematical work of proving that a relation is closed or a
witness event is open. No independence of the coordinates of the carrier is required.

## Lemma skeleton

* **Conditions:** weak convergence of the same joint laws and either an open event with convergent
  upper bounds or a closed event of probability one for every approximating law.
* **Objects:** `P`, `Pn`, the event, and its probability bounds; every probability is in `ℝ≥0∞`.
* **Proof detail:** open-event lower semicontinuity followed by the bound's scalar limit; apply the
  same step to the complement of a closed event to preserve its almost-sure constraint.

These are direct Portmanteau corollaries. The general-space source is Fremlin, *Measure Theory*,
Volume 4, §437J(d): the narrow topology makes open-set mass lower semicontinuous and total mass
continuous. See <https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=60>. The concrete
measurable/topological hypotheses below are those of mathlib's Portmanteau theorem.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

/-- Upper bounds on an open event pass to the weak limit when the bounds converge.

This is an open-set lower-semicontinuity corollary of Fremlin, *Measure Theory*, Vol. 4,
§437J(d), followed by the scalar limit of the bounds.
-/
theorem measure_open_le_of_tendsto_bounds
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto Pn atTop (𝓝 P)) (U : Set Ω) (hU : IsOpen U)
    (B : ℕ → ℝ≥0∞) (b : ℝ≥0∞) (hB : Tendsto B atTop (𝓝 b))
    (hb : ∀ n, (Pn n : Measure Ω) U ≤ B n) : (P : Measure Ω) U ≤ b :=
  (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hU).trans
    ((liminf_le_liminf (Eventually.of_forall hb)).trans_eq hB.liminf_eq)

/-- A closed almost-sure constraint is preserved by weak convergence of the same laws.

This is the complement-of-open-set corollary of Fremlin, *Measure Theory*, Vol. 4, §437J(d).
The total mass is fixed at one; the complement has zero mass in every approximating law.
-/
theorem ae_mem_closed_of_tendsto
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto Pn atTop (𝓝 P)) (K : Set Ω) (hK : IsClosed K)
    (hs : ∀ n, ∀ᵐ ω ∂(Pn n : Measure Ω), ω ∈ K) :
    ∀ᵐ ω ∂(P : Measure Ω), ω ∈ K := by
  have hn : ∀ n, (Pn n : Measure Ω) Kᶜ = 0 := hs
  exact le_antisymm
    (measure_open_le_of_tendsto_bounds P Pn hweak Kᶜ hK.isOpen_compl
      (fun _ ↦ 0) 0 tendsto_const_nhds (fun n ↦ (hn n).le)) bot_le

end OTSelector.Probability
