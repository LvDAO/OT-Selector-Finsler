import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
## Lemma skeleton

* **Conditions:** A finite sample; nonzero sample size only for probability normalization; measurable maps for pushforwards.
* **Objects:** The Dirac sum divided by the sample size.
* **Proof detail:** Integrate or push forward each Dirac summand; reindex a finite sum under a permutation.

## Mathematical sources

* Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*, Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10.
  https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** The normalized probability-valued API and permutation identities are finite-sum consequences of the counting-measure formulas.
-/

/-!
# Generic empirical probability measures

The definition is the normalized finite sum of Dirac measures.  It is deliberately independent of
the transport model so later point-process layers can reuse the same API.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace OTSelector

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {n : ℕ}

/-- The empirical measure `(1/n) • ∑ i, δ_{x i}`. -/
noncomputable def empiricalMeasure (x : Fin n → α) : Measure α :=
  (n : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (x i)

instance empiricalMeasure.instIsProbabilityMeasure [NeZero n] (x : Fin n → α) :
    IsProbabilityMeasure (empiricalMeasure x) := by
  constructor
  rw [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (NeZero.ne n)) (ENNReal.natCast_ne_top n)

/-- The empirical measure bundled as a `ProbabilityMeasure`. -/
noncomputable def empiricalProbabilityMeasure [NeZero n] (x : Fin n → α) :
    ProbabilityMeasure α :=
  ⟨empiricalMeasure x, inferInstance⟩

@[simp]
theorem empiricalProbabilityMeasure_toMeasure [NeZero n] (x : Fin n → α) :
    (empiricalProbabilityMeasure x : Measure α) = empiricalMeasure x :=
  rfl

/-- Integration against an empirical measure is a finite average. -/
theorem integral_empiricalMeasure (x : Fin n → α) {f : α → ℝ}
    (hf : StronglyMeasurable f) :
    ∫ z, f z ∂(empiricalMeasure x) = (n : ℝ)⁻¹ * ∑ i, f (x i) := by
  have hint : ∀ i : Fin n, Integrable f (Measure.dirac (x i)) :=
    fun i ↦ integrable_dirac' hf (by simp)
  rw [empiricalMeasure, integral_smul_measure,
    integral_finsetSum_measure fun i _ ↦ hint i]
  simp only [integral_dirac' _ _ hf, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul]

/-- Empirical measures commute with measurable pushforwards. -/
theorem map_empiricalMeasure (x : Fin n → α) (f : α → β) (hf : Measurable f) :
    Measure.map f (empiricalMeasure x) = empiricalMeasure (f ∘ x) := by
  rw [empiricalMeasure, empiricalMeasure, Measure.map_smul, Measure.map_finset_sum']
  · congr 1
    exact Finset.sum_congr rfl fun i _ ↦ by
      simpa [Function.comp_apply] using Measure.map_dirac' hf (x i)
  · exact hf.aemeasurable

/-- Reindexing a sample by a permutation leaves its empirical measure unchanged. -/
theorem empiricalMeasure_comp_perm (x : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    empiricalMeasure (x ∘ σ) = empiricalMeasure x := by
  rw [empiricalMeasure, empiricalMeasure]
  congr 1
  exact Equiv.sum_comp σ (fun i ↦ Measure.dirac (x i))

end OTSelector
