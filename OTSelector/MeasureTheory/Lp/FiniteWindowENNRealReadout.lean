import OTSelector.MeasureTheory.Lp.ENNRealSeriesReadout
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.FiniteWindowENNRealTrafficReadout.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.FiniteWindowENNRealTrafficReadout`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.Lp.FiniteWindowENNRealReadout

## Lemma skeleton

* **Conditions:** Finite inner band sets, countably many bands, individually finite ENNReal window terms and supplied real-series L2/absolute-summability bounds.
* **Objects:** Finite original total traffic almost surely and L2 of its literal real readout, also after a finite window sum.
* **Proof detail:** Commute finite toReal sums, use the ENNReal series-finiteness/readout identity bandwise and combine the finite L2 windows by Minkowski.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=93): Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=219): Section 7B, Theorem 7.20 and proof, pp. 204–205; Theorem 7.24, p. 205.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=214): Section 7A, Theorem 7.14, p. 199 (Minkowski).

Source relation (composition): Extended-real readout assembly; individual finiteness is checked before conversion toReal.
-/

/-! The real readout of a finite window family of nonnegative banded traffic
is L2 and the original total traffic is almost surely finite. Each individual
window term is finite before toReal is used, and only the existing countable
ENNReal readout and finite-sum interfaces are invoked. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology BigOperators Classical
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency true

/-- Finite-band real traffic series transfer to their original nonnegative
ENNReal readout, retaining almost sure finiteness of the original series. -/
theorem memLp_banded_ennreal_tsum_readout_of_ae_abs_summable
    {Ω Z I : Type*} [MeasurableSpace Ω] [Countable Z] [Countable I]
    (P : Measure Ω) (bands : Z → Finset I) (window : Z → I → Ω → ℝ≥0∞)
    (hfinite : ∀ z i, ∀ᵐ ω ∂P, window z i ω ≠ ∞)
    (hLp : MemLp (fun ω ↦ ∑' z, ∑ i ∈ bands z, (window z i ω).toReal) 2 P)
    (habs : ∀ᵐ ω ∂P, Summable (fun z ↦ ‖∑ i ∈ bands z, (window z i ω).toReal‖)) :
    MemLp (fun ω ↦ (∑' z, ∑ i ∈ bands z, window z i ω).toReal) 2 P ∧
      ∀ᵐ ω ∂P, (∑' z, ∑ i ∈ bands z, window z i ω) ≠ ∞ := by
  let traffic := fun z ω ↦ ∑ i ∈ bands z, window z i ω
  let level := fun z ω ↦ ∑ i ∈ bands z, (window z i ω).toReal
  have hf : ∀ z, ∀ᵐ ω ∂P, traffic z ω ≠ ∞ := by
    intro z
    filter_upwards [ae_all_iff.mpr (hfinite z)] with ω hω
    exact ENNReal.sum_ne_top.mpr (fun i _ ↦ hω i)
  have hread : ∀ᵐ ω ∂P, ∀ z, (traffic z ω).toReal = level z ω := by
    filter_upwards [ae_all_iff.mpr (fun z ↦ ae_all_iff.mpr (hfinite z))] with ω hω
    intro z
    exact ENNReal.toReal_sum (fun i _ ↦ hω z i)
  have hsreal : ∀ᵐ ω ∂P, Summable (fun z ↦ (traffic z ω).toReal) := by
    filter_upwards [habs,hread] with ω hs hω
    have hlevels : Summable (fun z ↦ level z ω) := Summable.of_norm_bounded hs (fun _ ↦ le_rfl)
    exact hlevels.congr (fun z ↦ (hω z).symm)
  have hsumRead : (fun ω ↦ ∑' z, (traffic z ω).toReal) =ᵐ[P] (fun ω ↦ ∑' z, level z ω) := by
    filter_upwards [hread] with ω hω
    exact tsum_congr hω
  have hreadLp : MemLp (fun ω ↦ ∑' z, (traffic z ω).toReal) 2 P :=
    hLp.ae_eq hsumRead.symm
  exact ⟨memLp_ennreal_tsum_toReal_of_summable P traffic hf hsreal hreadLp,
    (ae_ennreal_tsum_ne_top_and_toReal_eq_of_summable P traffic hf hsreal).mono
      (fun _ hω ↦ hω.1)⟩

/-- Finitely many physical windows preserve L2 and almost sure finiteness
of the literal original ENNReal traffic, on the same arbitrary measure P. -/
theorem memLp_finite_window_ennreal_traffic_readout
    {Ω L Z I : Type*} [MeasurableSpace Ω] [Fintype L] [Countable Z] [Countable I]
    (P : Measure Ω) (bands : Z → Finset I) (window : L → Z → I → Ω → ℝ≥0∞)
    (hfinite : ∀ l z i, ∀ᵐ ω ∂P, window l z i ω ≠ ∞)
    (hLp : ∀ l, MemLp (fun ω ↦ ∑' z, ∑ i ∈ bands z, (window l z i ω).toReal) 2 P)
    (habs : ∀ l, ∀ᵐ ω ∂P,
      Summable (fun z ↦ ‖∑ i ∈ bands z, (window l z i ω).toReal‖)) :
    MemLp (fun ω ↦ (∑ l, ∑' z, ∑ i ∈ bands z, window l z i ω).toReal) 2 P ∧
      ∀ᵐ ω ∂P, (∑ l, ∑' z, ∑ i ∈ bands z, window l z i ω) ≠ ∞ := by
  let windowTotal := fun l ω ↦ ∑' z, ∑ i ∈ bands z, window l z i ω
  have hwindow := fun l ↦ memLp_banded_ennreal_tsum_readout_of_ae_abs_summable
    P bands (window l) (hfinite l) (hLp l) (habs l)
  have hfiniteTotal : ∀ l, ∀ᵐ ω ∂P, windowTotal l ω ≠ ∞ := fun l ↦ (hwindow l).2
  have hsumLp : MemLp (fun ω ↦ ∑ l, (windowTotal l ω).toReal) 2 P :=
    memLp_finsetSum Finset.univ (fun l _ ↦ (hwindow l).1)
  have hae : ∀ᵐ ω ∂P, (∑ l, windowTotal l ω) ≠ ∞ ∧
      (∑ l, windowTotal l ω).toReal = ∑ l, (windowTotal l ω).toReal := by
    filter_upwards [ae_all_iff.mpr hfiniteTotal] with ω hω
    exact ⟨ENNReal.sum_ne_top.mpr (fun l _ ↦ hω l),ENNReal.toReal_sum (fun l _ ↦ hω l)⟩
  exact ⟨hsumLp.ae_eq (hae.mono (fun _ hω ↦ hω.2.symm)),hae.mono (fun _ hω ↦ hω.1)⟩

end OTSelector.Probability

end
end
