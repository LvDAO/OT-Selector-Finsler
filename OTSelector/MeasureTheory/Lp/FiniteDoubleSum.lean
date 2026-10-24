import Mathlib.MeasureTheory.Function.L2Space

/-!
## Lemma skeleton

* **Conditions:** A finite family of L2 functions under an arbitrary measure, with one nonnegative uniform norm bound; the double-sum form bounds each grouped window.
* **Objects:** L2 membership and cardinality times the uniform norm bound for finite or finite double sums.
* **Proof detail:** Iterate Minkowski; commute the two finite sums to apply the window-wise estimate.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 7A, Theorem 7.14, p. 199 (Minkowski).
  https://measure.axler.net/MIRA.pdf#page=214

**Relationship to the sources:** Direct finite-sum corollaries of Minkowski. The theorem itself adds no geometry or band-width relation.
-/

/-! Sum physical subwindows only after the finite birth-band estimate. This
preserves the actual number-of-bands times width relation `N*s=8*t`. -/
open MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- A fixed finite physical clock cover costs its actual number of windows in
L2; band energy budgets remain unchanged inside each window. -/
theorem finiteWindow_traffic_memLp_two_of_uniform_norm
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (windows : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ windows, MemLp (T i) 2 P)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ i ∈ windows, eLpNorm (T i) 2 P ≤ ENNReal.ofReal A) :
    MemLp (fun x ↦ ∑ i ∈ windows, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ windows, T i x) 2 P ≤
        ENNReal.ofReal ((windows.card : ℝ) * A) := by
  refine ⟨memLp_finsetSum windows hT, ?_⟩
  calc
    _ = eLpNorm (∑ i ∈ windows, T i) 2 P := by congr 1; funext x; simp
    _ ≤ ∑ i ∈ windows, eLpNorm (T i) 2 P :=
      eLpNorm_sum_le (fun i hi ↦ (hT i hi).aestronglyMeasurable) (by norm_num)
    _ ≤ ∑ _i ∈ windows, ENNReal.ofReal A := Finset.sum_le_sum hbound
    _ = ENNReal.ofReal (∑ _i ∈ windows, A) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ hA)).symm
    _ = _ := by simp

/-- In the actual literal birth family, fixed-window profiles can be summed
without flattening the window index into the number of original clock bands. -/
theorem finiteWindowBand_traffic_memLp_two_of_uniform_window_norm
    {Ω ι κ : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (bands : Finset ι) (windows : Finset κ) (T : ι → κ → Ω → ℝ)
    (hT : ∀ ell ∈ windows, MemLp (fun x ↦ ∑ i ∈ bands, T i ell x) 2 P)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ ell ∈ windows,
      eLpNorm (fun x ↦ ∑ i ∈ bands, T i ell x) 2 P ≤ ENNReal.ofReal A) :
    MemLp (fun x ↦ ∑ i ∈ bands, ∑ ell ∈ windows, T i ell x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ bands, ∑ ell ∈ windows, T i ell x) 2 P ≤
        ENNReal.ofReal ((windows.card : ℝ) * A) := by
  have h := finiteWindow_traffic_memLp_two_of_uniform_norm P windows
    (fun ell x ↦ ∑ i ∈ bands, T i ell x) hT hA hbound
  have hfun : (fun x ↦ ∑ ell ∈ windows, ∑ i ∈ bands, T i ell x) =
      (fun x ↦ ∑ i ∈ bands, ∑ ell ∈ windows, T i ell x) := by
    funext x
    exact Finset.sum_comm
  rw [hfun] at h
  exact h

end OTSelector.Probability
