import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.ENNRealTrafficSumReadout.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.ENNRealTrafficSumReadout`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.Lp.ENNRealSeriesReadout

## Lemma skeleton

* **Conditions:** Each extended nonnegative term is finite and its real readouts are summable, pointwise or almost everywhere; the final transfer supplies Lp for the real series.
* **Objects:** Finiteness of the ENNReal sum, exact toReal commutation and Lp membership of its readout.
* **Proof detail:** Sum finite nonnegative real terms and use their finite tsum to exclude infinity; combine countably many almost-everywhere facts and transfer by almost-everywhere equality.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=219): Section 7B, Theorem 7.20 and proof, pp. 204–205; Theorem 7.24, p. 205.

Source relation (composition): Extended-real/real series adapter; individual finiteness is essential because toReal infinity is zero.
-/

/-! Finiteness and real readout of countable nonnegative traffic. The
individual finiteness condition prevents `toReal ∞ = 0` from hiding traffic. -/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- Finite nonnegative terms and summable real readouts give a finite original
ENNReal sum and its exact real readout. No countability assumption is needed. -/
theorem ennreal_tsum_ne_top_and_toReal_eq_of_summable
    {I : Type*} (f : I → ℝ≥0∞) (hf : ∀ i, f i ≠ ∞)
    (hs : Summable (fun i ↦ (f i).toReal)) :
    (∑' i, f i) ≠ ∞ ∧ (∑' i, f i).toReal = ∑' i, (f i).toReal := by
  have hs' : (∑' i, ((f i).toNNReal : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr hs
  rw [tsum_congr (fun i ↦ ENNReal.coe_toNNReal (hf i))] at hs'
  exact ⟨hs', ENNReal.tsum_toReal_eq hf⟩

/-- Countably many almost everywhere finite traffic terms and almost sure
real summability give the finite original sum and exact readout almost surely. -/
theorem ae_ennreal_tsum_ne_top_and_toReal_eq_of_summable
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I] (P : Measure Ω)
    (f : I → Ω → ℝ≥0∞) (hf : ∀ i, ∀ᵐ x ∂P, f i x ≠ ∞)
    (hs : ∀ᵐ x ∂P, Summable (fun i ↦ (f i x).toReal)) :
    ∀ᵐ x ∂P, (∑' i, f i x) ≠ ∞ ∧
      (∑' i, f i x).toReal = ∑' i, (f i x).toReal := by
  filter_upwards [ae_all_iff.mpr hf, hs] with x hfx hsx
  exact ennreal_tsum_ne_top_and_toReal_eq_of_summable (fun i ↦ f i x) hfx hsx

/-- Membership of the already constructed real series transfers to the real
readout of the finite original nonnegative traffic sum. -/
theorem memLp_ennreal_tsum_toReal_of_summable
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I] (P : Measure Ω)
    (f : I → Ω → ℝ≥0∞) (hf : ∀ i, ∀ᵐ x ∂P, f i x ≠ ∞)
    (hs : ∀ᵐ x ∂P, Summable (fun i ↦ (f i x).toReal)) {p : ℝ≥0∞}
    (hLp : MemLp (fun x ↦ ∑' i, (f i x).toReal) p P) :
    MemLp (fun x ↦ (∑' i, f i x).toReal) p P := by
  apply MemLp.ae_eq _ hLp
  exact (ae_ennreal_tsum_ne_top_and_toReal_eq_of_summable P f hf hs).mono
    (fun _ hx ↦ hx.2.symm)

end OTSelector.Probability

end
end
