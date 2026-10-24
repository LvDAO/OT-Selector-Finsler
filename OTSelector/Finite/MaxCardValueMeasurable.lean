import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Tactic
import OTSelector.Finite.PartialMatching

/-!
# Finite.MaxCardValueMeasurable

**Conditions:** Finite rectangular costs depend measurably on an arbitrary measurable parameter.

**Objects:** The finite subtype of full-cardinality matchings and its indexed infimum value.

**Proof detail:** Give the feasible subtype a Fintype instance, identify maxCardValue with its finite iInf, and use measurability of finite sums and countable infima.

**Sources:** [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106), Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Measurability of the maximum-cardinality value

The value is an infimum of the finitely many maximum-cardinality matching costs.
Expressing it as an `iInf` over the finite type of optimal-cardinality partial
matchings makes its measurability immediate from measurability of each edge
cost.  This is the measurability input for integrating finite-volume pressures.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section
namespace OTSelector

namespace PartialMatching

variable {m n : ℕ}

/-- Partial matchings form a finite type: they inject into finite sets of edges. -/
instance : Fintype (PartialMatching m n) :=
  Fintype.ofInjective (fun σ : PartialMatching m n => σ.edges)
    (fun σ τ h => by
      cases σ
      cases τ
      simp only at h
      subst h
      rfl)

/-- The subtype of maximum-cardinality matchings. -/
def maxCardMatching (m n : ℕ) :=
  {σ : PartialMatching m n // σ.card = min m n}

instance maxCardMatchingFintype : Fintype (maxCardMatching m n) := by
  unfold maxCardMatching
  infer_instance

/-- The value is the infimum of the costs over maximum-cardinality matchings. -/
theorem maxCardValue_eq_iInf (c : Fin m → Fin n → ℝ) :
    maxCardValue c = ⨅ σ : maxCardMatching m n, σ.1.cost c := by
  classical
  unfold maxCardValue
  have hset : {v : ℝ | ∃ σ : PartialMatching m n, σ.card = min m n ∧ v = σ.cost c} =
      Set.range (fun σ : maxCardMatching m n => σ.1.cost c) := by
    ext v
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨⟨σ, hσ⟩, rfl⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨σ.1, σ.2, rfl⟩
  rw [hset, sInf_range]

/-- Pointwise measurability of the maximum-cardinality value in a parameter. -/
theorem measurable_maxCardValue {α : Type*} [MeasurableSpace α]
    (c : α → Fin m → Fin n → ℝ) (hc : ∀ i j, Measurable fun a => c a i j) :
    Measurable fun a => maxCardValue (c a) := by
  classical
  have hval : (fun a => maxCardValue (c a)) =
      fun a => ⨅ σ : maxCardMatching m n, σ.1.cost (c a) := by
    funext a
    exact maxCardValue_eq_iInf (c a)
  rw [hval]
  apply Measurable.iInf
  intro σ
  unfold cost
  exact Finset.measurable_sum _ fun e _ => hc e.1 e.2

end PartialMatching

end OTSelector
