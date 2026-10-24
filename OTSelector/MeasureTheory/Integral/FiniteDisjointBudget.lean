import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

/-!
## Lemma skeleton

* **Conditions:** A finite pairwise disjoint measurable reference family covering a measurable H; integrable pressure or finite measure as appropriate; positive total tolerance.
* **Objects:** Exact partition of integral/lost mass and aggregate energy/loss budgets, including an empty family.
* **Proof detail:** Partition H by its reference cells, sum by disjoint additivity, and bound each numerical error by tolerance/(N+1) to retain strict slack.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
  https://measure.axler.net/MIRA.pdf#page=93
* Terence Tao, *Analysis I*, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean

**Relationship to the sources:** Finite additivity plus elementary finite-sum arithmetic, not a new limiting theorem. The N+1 denominator handles N=0.
-/

/-! Exact integral and original-mass aggregation for a finite reference family. -/

open Set Function MeasureTheory
open scoped BigOperators

namespace OTSelector.Reconstruction

/-- Integrating over the reference cells intersected with a covered target gives
exactly the original integral over that target. -/
theorem sum_finite_reference_integral_eq
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) (p : Z → ℝ) (hp : IntegrableOn p H μ) :
    ∑ i, ∫ z in H ∩ C i, p z ∂μ = ∫ z in H, p z ∂μ := by
  have hunion : (⋃ i, H ∩ C i) = H := by
    rw [← inter_iUnion, inter_eq_left.mpr hcover]
  have hd : Pairwise (Disjoint on fun i ↦ H ∩ C i) := fun i j hij ↦
    (hdisjoint hij).mono inter_subset_right inter_subset_right
  have hi := integral_iUnion_fintype (fun i ↦ hH.inter (hC i)) hd
    (fun _ ↦ hp.mono_set inter_subset_left)
  rw [hunion] at hi
  exact hi.symm

/-- The loss from the union of retained reference cores is exactly the sum of
their cellwise losses, measured with the same original finite measure. -/
theorem measureReal_finite_reference_loss_eq
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C K : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (hK : ∀ i, MeasurableSet (K i)) (hKsubset : ∀ i, K i ⊆ H ∩ C i)
    (μ : Measure Z) [IsFiniteMeasure μ] :
    μ.real (H \ ⋃ i, K i) = ∑ i, μ.real ((H ∩ C i) \ K i) := by
  have hunion : H \ ⋃ i, K i = ⋃ i, (H ∩ C i) \ K i := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hzi⟩ := mem_iUnion.mp (hcover hz.1)
      exact mem_iUnion.mpr ⟨i, ⟨⟨hz.1, hzi⟩, fun h ↦ hz.2 (mem_iUnion.mpr ⟨i, h⟩)⟩⟩
    · intro hz
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
      refine ⟨hzi.1.1, ?_⟩
      intro hzK
      obtain ⟨j, hzj⟩ := mem_iUnion.mp hzK
      by_cases hij : i = j
      · subst j
        exact hzi.2 hzj
      · exact (disjoint_left.mp (hdisjoint hij)) hzi.1.2 (hKsubset j hzj).2
  rw [hunion]
  apply measureReal_iUnion_fintype
  · intro i j hij
    exact (hdisjoint hij).mono
      (fun _ hz ↦ hz.1.2) (fun _ hz ↦ hz.1.2)
  · exact fun i ↦ (hH.inter (hC i)).diff (hK i)
  · exact fun i ↦ measure_ne_top μ ((H ∩ C i) \ K i)

/-- Allocating at most `tolerance / (N + 1)` to each of `N` errors leaves a
strict total tolerance, also for an empty reference family. -/
theorem sum_finite_reference_budget_lt
    {N : ℕ} (error : Fin N → ℝ) {tolerance : ℝ} (htolerance : 0 < tolerance)
    (herror : ∀ i, error i ≤ tolerance / ((N : ℝ) + 1)) :
    ∑ i, error i < tolerance := by
  have hsum : ∑ i, error i ≤ (N : ℝ) * (tolerance / ((N : ℝ) + 1)) := by
    calc
      ∑ i, error i ≤ ∑ _i : Fin N, tolerance / ((N : ℝ) + 1) :=
        Finset.sum_le_sum (fun i _ ↦ herror i)
      _ = _ := by simp
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hdenom : 0 < (N : ℝ) + 1 := by linarith
  have hbudget : (N : ℝ) * (tolerance / ((N : ℝ) + 1)) < tolerance := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hdenom).mpr
    nlinarith only [htolerance]
  exact hsum.trans_lt hbudget

/-- A common strictly positive cellwise loss budget yields the same strict
budget for the loss from all retained cores, including an empty family. -/
theorem measureReal_finite_reference_loss_lt
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C K : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (hK : ∀ i, MeasurableSet (K i)) (hKsubset : ∀ i, K i ⊆ H ∩ C i)
    (μ : Measure Z) [IsFiniteMeasure μ] {budget : ℝ} (hbudget : 0 < budget)
    (hloss : ∀ i, μ.real ((H ∩ C i) \ K i) < budget / ((N : ℝ) + 1)) :
    μ.real (H \ ⋃ i, K i) < budget := by
  rw [measureReal_finite_reference_loss_eq C K hC hdisjoint hH hcover hK hKsubset μ]
  exact sum_finite_reference_budget_lt _ hbudget (fun i ↦ (hloss i).le)

/-- Cellwise original pressure bounds with the prescribed finite error
allocation aggregate below the original integral plus the full tolerance. -/
theorem sum_finite_reference_energy_lt_integral_add
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) (p : Z → ℝ) (hp : IntegrableOn p H μ)
    (energy : Fin N → ℝ) {tolerance : ℝ} (htolerance : 0 < tolerance)
    (henergy : ∀ i, energy i ≤
      (∫ z in H ∩ C i, p z ∂μ) + tolerance / ((N : ℝ) + 1)) :
    ∑ i, energy i < (∫ z in H, p z ∂μ) + tolerance := by
  have hsum := sum_finite_reference_budget_lt
    (fun i ↦ energy i - ∫ z in H ∩ C i, p z ∂μ) htolerance
    (fun i ↦ by linarith only [henergy i])
  rw [Finset.sum_sub_distrib,
    sum_finite_reference_integral_eq C hC hdisjoint hH hcover μ p hp] at hsum
  linarith only [hsum]

/-- The weak aggregate bound follows from the same prescribed allocation. -/
theorem sum_finite_reference_energy_le_integral_add
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) (p : Z → ℝ) (hp : IntegrableOn p H μ)
    (energy : Fin N → ℝ) {tolerance : ℝ} (htolerance : 0 < tolerance)
    (henergy : ∀ i, energy i ≤
      (∫ z in H ∩ C i, p z ∂μ) + tolerance / ((N : ℝ) + 1)) :
    ∑ i, energy i ≤ (∫ z in H, p z ∂μ) + tolerance :=
  (sum_finite_reference_energy_lt_integral_add
    C hC hdisjoint hH hcover μ p hp energy htolerance henergy).le

end OTSelector.Reconstruction
