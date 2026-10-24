import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
## Lemma skeleton

* **Conditions:** Countably many pairwise disjoint measurable pieces with local real functions; later conclusions separately assume local measurability, local nonnegativity or global integrability.
* **Objects:** The function glued by a countable sum of piece indicators, its exact branch values, and integral equal to the sum of piece integrals.
* **Proof detail:** At most one indicator is nonzero at each point; use countable piecewise measurability and countable disjoint integration.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
  https://measure.axler.net/MIRA.pdf#page=93
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3B, Theorem 3.28, pp. 90–91.
  https://measure.axler.net/MIRA.pdf#page=105
* D. H. Fremlin, *Measure Theory, Volume 4*, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces.
  https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106

**Relationship to the sources:** Countable measurable gluing and integral additivity; global integrability is explicit for the signed integral identity.
-/

/-! A single original root pressure is glued on the actual disjoint measurable
seed pieces. No optimizer or alternative population measure is selected. -/
open Set Function MeasureTheory Filter
open scoped Topology BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1000000

/-- The single original root function, equal to its selected piece pressure
and zero on roots outside the selected union. At most one summand is nonzero. -/
def disjointRootPressure {Z : Type*} (piece : ℕ → Set Z) (p : ℕ → Z → ℝ) (z : Z) : ℝ :=
  ∑' j, (piece j).indicator (p j) z

/-- Disjoint original pieces select exactly their own original pressure. -/
theorem disjointRootPressure_eq_on_piece {Z : Type*} (piece : ℕ → Set Z)
    (hd : Pairwise (Disjoint on piece)) (p : ℕ → Z → ℝ) (j : ℕ) {z : Z}
    (hz : z ∈ piece j) : disjointRootPressure piece p z = p j z := by
  unfold disjointRootPressure
  rw [tsum_eq_single j]
  · exact indicator_of_mem hz _
  · intro k hkj
    exact indicator_of_notMem (fun hk ↦ Set.disjoint_left.mp (hd hkj) hk hz) _

/-- The actual original pressure contributes zero outside the selected roots. -/
theorem disjointRootPressure_eq_zero_of_notMem {Z : Type*} (piece : ℕ → Set Z)
    (p : ℕ → Z → ℝ) {z : Z} (hz : z ∉ ⋃ j, piece j) :
    disjointRootPressure piece p z = 0 := by
  have hterm (j : ℕ) : (piece j).indicator (p j) z = 0 :=
    indicator_of_notMem (fun hj ↦ hz (mem_iUnion.mpr ⟨j,hj⟩)) _
  simp only [disjointRootPressure,hterm,tsum_zero]

/-- Original completed-measure pressure versions glue measurably on their
unchanged original disjoint pieces; no pointwise Borel versions are assumed. -/
theorem aestronglyMeasurable_disjointRootPressure
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (piece : ℕ → Set Z)
    (hm : ∀ j, MeasurableSet (piece j)) (hd : Pairwise (Disjoint on piece))
    (p : ℕ → Z → ℝ) (hp : ∀ j, AEStronglyMeasurable (p j) (μ.restrict (piece j))) :
    AEStronglyMeasurable (disjointRootPressure piece p) μ := by
  let partialSum := fun n z ↦ ∑ j ∈ Finset.range n, (piece j).indicator (p j) z
  have hmeas (n : ℕ) : AEStronglyMeasurable (partialSum n) μ := by
    have hh := Finset.aestronglyMeasurable_sum (Finset.range n)
      (fun j _ ↦ (aestronglyMeasurable_indicator_iff (hm j)).mpr (hp j))
    have heq : (∑ j ∈ Finset.range n, (piece j).indicator (p j)) = partialSum n := by
      funext z
      simp only [partialSum,Finset.sum_apply]
    rw [heq] at hh
    exact hh
  apply aestronglyMeasurable_of_tendsto_ae atTop hmeas
  apply Filter.Eventually.of_forall
  intro z
  by_cases hactive : ∃ j, z ∈ piece j
  · obtain ⟨j,hj⟩ := hactive
    rw [disjointRootPressure_eq_on_piece piece hd p j hj]
    apply (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ p j z) atTop (𝓝 (p j z))).congr'
    filter_upwards [eventually_ge_atTop (j+1)] with n hn
    dsimp only [partialSum]
    rw [Finset.sum_eq_single j]
    · exact (indicator_of_mem hj _).symm
    · intro k _ hkj
      exact indicator_of_notMem (fun hk ↦ Set.disjoint_left.mp (hd hkj) hk hj) _
    · intro hjnot
      exact False.elim (hjnot (Finset.mem_range.mpr (by omega)))
  · have hz : z ∉ ⋃ j, piece j := by simpa only [mem_iUnion,not_exists] using hactive
    rw [disjointRootPressure_eq_zero_of_notMem piece p hz]
    apply (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).congr'
    apply Filter.Eventually.of_forall
    intro n
    dsimp only [partialSum]
    symm
    apply Finset.sum_eq_zero
    intro j _
    exact indicator_of_notMem (fun hj ↦ hactive ⟨j,hj⟩) _

/-- Nonnegative actual original piece pressures give a globally nonnegative
single original root pressure almost everywhere. -/
theorem ae_nonneg_disjointRootPressure
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (piece : ℕ → Set Z)
    (hd : Pairwise (Disjoint on piece)) (p : ℕ → Z → ℝ)
    (hp : ∀ j, ∀ᵐ z ∂μ.restrict (piece j), 0 ≤ p j z) :
    ∀ᵐ z ∂μ, 0 ≤ disjointRootPressure piece p z := by
  filter_upwards [ae_all_iff.mpr (fun j ↦ ae_imp_of_ae_restrict (hp j))] with z hz
  by_cases hactive : ∃ j, z ∈ piece j
  · obtain ⟨j,hj⟩ := hactive
    rw [disjointRootPressure_eq_on_piece piece hd p j hj]
    exact hz j hj
  · rw [disjointRootPressure_eq_zero_of_notMem piece p
      (by simpa only [mem_iUnion,not_exists] using hactive)]

/-- Genuine global integrability identifies the single original root
integral with the countable original piece integrals, without requiring full
coverage or discarding singular energy elsewhere. -/
theorem integral_disjointRootPressure_eq_tsum
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (piece : ℕ → Set Z)
    (hm : ∀ j, MeasurableSet (piece j)) (hd : Pairwise (Disjoint on piece))
    (p : ℕ → Z → ℝ) (hi : Integrable (disjointRootPressure piece p) μ) :
    (∫ z, disjointRootPressure piece p z ∂μ) =
      ∑' j, ∫ z in piece j, p j z ∂μ := by
  have hind : (⋃ j, piece j).indicator (disjointRootPressure piece p) =
      disjointRootPressure piece p := by
    funext z
    by_cases hz : z ∈ ⋃ j, piece j
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz,disjointRootPressure_eq_zero_of_notMem piece p hz]
  rw [← hind,integral_indicator (MeasurableSet.iUnion hm)]
  have hsplit := integral_iUnion hm hd hi.integrableOn
  rw [hsplit]
  apply tsum_congr
  intro j
  apply setIntegral_congr_fun (hm j)
  intro z hz
  exact disjointRootPressure_eq_on_piece piece hd p j hz

end OTSelector.Reconstruction
