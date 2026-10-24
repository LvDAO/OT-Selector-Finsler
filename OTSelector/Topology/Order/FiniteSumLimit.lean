import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Topology.Order.FiniteSumLimit

Conditions: Real functions A, e and a finite family B converge, e tends to zero, and eventually A is bounded by the finite sum B plus e.

Objects: The limiting finite-sum inequality a ≤ sum b.

Proof detail: Take limits of the finite sum and vanishing error, then use closedness of real order.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/realanal.pdf#page=62): Section 2.2, Lemma 2.2.3, p. 62; Section 2.3, Proposition 2.3.5, pp. 76–77.

Source relation: Direct limit/order corollary, generalized from sequences to the explicit filter.
-/

/-!
# Squeezing a limit by a finite tile sum

If a scalar sequence is eventually bounded by a finite sum of tile contributions
plus a vanishing error, then its limit is bounded by the sum of the tile limits.
This is the final order-theoretic step of the finite-tile pressure upper bound.
-/

open Filter
open scoped Topology BigOperators

namespace OTSelector

/-- **Finite-tile squeeze.**  An eventual upper bound by a finite sum of
convergent sequences plus a vanishing error passes to the limit. -/
theorem limit_le_sum_of_eventually_le {ι : Type*} [Fintype ι]
    (A : ℝ → ℝ) (B : ι → ℝ → ℝ) (e : ℝ → ℝ) (a : ℝ) (b : ι → ℝ)
    (hA : Tendsto A atTop (𝓝 a))
    (hB : ∀ i, Tendsto (B i) atTop (𝓝 (b i)))
    (he : Tendsto e atTop (𝓝 0))
    (hle : ∀ᶠ R in atTop, A R ≤ (∑ i, B i R) + e R) :
    a ≤ ∑ i, b i := by
  have hsum : Tendsto (fun R => ∑ i, B i R) atTop (𝓝 (∑ i, b i)) :=
    tendsto_finsetSum _ fun i _ => hB i
  have hlim : Tendsto (fun R => (∑ i, B i R) + e R) atTop (𝓝 ((∑ i, b i) + 0)) :=
    hsum.add he
  have h := le_of_tendsto_of_tendsto hA hlim hle
  simpa using h

end OTSelector
