import Mathlib.MeasureTheory.Function.L2Space

/-!
## Lemma skeleton

* **Conditions:** A finite index set and arbitrary small/bad events; norm bounds assume each stated good or bad term is L2.
* **Objects:** Exact good/bad finite-sum decomposition and norm bound A+card(s) B for the original finite sum.
* **Proof detail:** Split each indicator by cases, sum the identity, and apply Minkowski to the good sum and each bad term.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 7A, Theorem 7.14, p. 199 (Minkowski).
  https://measure.axler.net/MIRA.pdf#page=214

**Relationship to the sources:** Elementary indicator algebra followed by the finite L2 triangle inequality; no stochastic independence or probability normalization is used.
-/

/-! Literal finite birth-window traffic splits on its own scene-small event
and its own original-count event before combining the two L2 estimates. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- Small traffic splits exactly into the original count-good and count-bad
parts on the same scene; events may differ between finite birth bands. -/
theorem sum_sceneEvent_traffic_eq_good_add_bad
    {Ω ι : Type*} (s : Finset ι) (Small Bad : ι → Set Ω) (T : ι → Ω → ℝ) :
    (fun x ↦ ∑ i ∈ s, (Small i).indicator (T i) x) =
      (fun x ↦ ∑ i ∈ s, ((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i) x) +
      (fun x ↦ ∑ i ∈ s, (Bad i).indicator ((Small i).indicator (T i)) x) := by
  funext x
  simp only [Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hs : x ∈ Small i <;> by_cases hb : x ∈ Bad i <;> simp [hs, hb]

/-- A level estimate on the actual good sum and a common norm bound on each
actual count-bad band yield L2 for the literal full small-event finite sum. -/
theorem finite_sceneEvent_traffic_memLp_two_of_good_bad_norm_bounds
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : Finset ι)
    (Small Bad : ι → Set Ω) (T : ι → Ω → ℝ)
    (hgood : MemLp (fun x ↦ ∑ i ∈ s, ((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i) x) 2 P)
    (hbad : ∀ i ∈ s, MemLp ((Bad i).indicator ((Small i).indicator (T i))) 2 P)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgoodNorm : eLpNorm (fun x ↦ ∑ i ∈ s,
      ((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i) x) 2 P ≤ ENNReal.ofReal A)
    (hbadNorm : ∀ i ∈ s, eLpNorm ((Bad i).indicator ((Small i).indicator (T i))) 2 P ≤
      ENNReal.ofReal B) :
    MemLp (fun x ↦ ∑ i ∈ s, (Small i).indicator (T i) x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ s, (Small i).indicator (T i) x) 2 P ≤
        ENNReal.ofReal (A + (s.card : ℝ) * B) := by
  have hbadSum := memLp_finsetSum s hbad
  have hbadSumNorm : eLpNorm (fun x ↦ ∑ i ∈ s,
      (Bad i).indicator ((Small i).indicator (T i)) x) 2 P ≤
      ENNReal.ofReal ((s.card : ℝ) * B) := by
    calc
      _ = eLpNorm (∑ i ∈ s, (Bad i).indicator ((Small i).indicator (T i))) 2 P := by
        congr 1; funext x; simp
      _ ≤ ∑ i ∈ s, eLpNorm ((Bad i).indicator ((Small i).indicator (T i))) 2 P :=
        eLpNorm_sum_le (fun i hi ↦ (hbad i hi).aestronglyMeasurable) (by norm_num)
      _ ≤ ∑ _i ∈ s, ENNReal.ofReal B := Finset.sum_le_sum hbadNorm
      _ = ENNReal.ofReal (∑ _i ∈ s, B) :=
        (ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ hB)).symm
      _ = _ := by simp
  rw [sum_sceneEvent_traffic_eq_good_add_bad s Small Bad T]
  refine ⟨hgood.add hbadSum, ?_⟩
  calc
    _ ≤ eLpNorm (fun x ↦ ∑ i ∈ s, ((Small i)ᶜ ∪ Bad i)ᶜ.indicator (T i) x) 2 P +
        eLpNorm (fun x ↦ ∑ i ∈ s, (Bad i).indicator ((Small i).indicator (T i)) x) 2 P :=
      eLpNorm_add_le hgood.aestronglyMeasurable hbadSum.aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal ((s.card : ℝ) * B) := add_le_add hgoodNorm hbadSumNorm
    _ = _ := (ENNReal.ofReal_add hA (by positivity)).symm

end OTSelector.Probability
