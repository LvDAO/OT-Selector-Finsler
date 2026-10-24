import Mathlib.Tactic

/-!
# Finite.ResidualHallStability

## Lemma skeleton

* **Conditions:** Finite nonnegative reference masses, a positive thinning parameter and nonnegative Hall cut slacks; perturbed masses retain their own Hall inequalities.

* **Objects:** One common positive tolerance preserving pointwise residual mass and every residual weighted Hall cut.

* **Proof detail:** Take minima over the finitely many positive reference coordinates/cut slacks. Bound finite-sum perturbations by the number of coordinates. Reference-tight cuts are handled exactly by the perturbed Hall hypothesis, without adding a false strictness premise.

## Mathematical sources

- [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2): Chapter 2 opening matching definition and Section 2.1, first three chapter pages.
- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.3, pp. 15–16, equations (2.10)–(2.11), fixed-marginal polytope and cost pairing.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): Weighted-cut residual stability is proved locally; Diestel supplies the Hall cut framework and the OT reference supplies weighted finite coupling constraints.
-/

/-!
Finite-dimensional pointwise domination and residual Hall stability for an
exact scalar multiple of a deterministic reference population. Reference-tight
cuts require no strict-slack hypothesis.
-/

open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- A fixed finite nonnegative reference vector admits uniform small
perturbations dominating any fixed thinning, including its zero coordinates. -/
theorem exists_tolerance_for_reference_thinning
    {I : Type*} [Fintype I] (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : I → ℝ,
      (∀ i, 0 ≤ a i) → (∀ i, |a i - p i| ≤ δ) → ∀ i, (1 - η) * p i ≤ a i := by
  classical
  let S := Finset.univ.filter fun i : I ↦ 0 < p i
  by_cases hS : S.Nonempty
  · let V := S.image p
    have hV : V.Nonempty := Finset.Nonempty.image hS _
    let m := V.min' hV
    have hm : 0 < m := by
      have hmem : m ∈ V := Finset.min'_mem V hV
      obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
      rw [← heq]
      exact (Finset.mem_filter.mp hi).2
    refine ⟨η * m, mul_pos hη hm, ?_⟩
    intro a ha hclose i
    by_cases hpi : 0 < p i
    · have hmin : m ≤ p i := Finset.min'_le V _
        (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpi⟩, rfl⟩)
      have hlo := (abs_le.mp (hclose i)).1
      have hmul := mul_le_mul_of_nonneg_left hmin hη.le
      nlinarith
    · have hz : p i = 0 := le_antisymm (le_of_not_gt hpi) (hp i)
      simpa only [hz, mul_zero] using ha i
  · refine ⟨1, by norm_num, ?_⟩
    intro a ha hclose i
    have hpi : ¬ 0 < p i := by
      intro hi
      exact hS ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    have hz : p i = 0 := le_antisymm (le_of_not_gt hpi) (hp i)
    simpa only [hz, mul_zero] using ha i

/-- Real Hall slack of one source cut for a finite class graph. -/
def referenceHallSlack {I J : Type*} [Fintype I] [Fintype J]
    (neighbor : Finset I → Finset J) (a : I → ℝ) (b : J → ℝ) (A : Finset I) : ℝ :=
  (∑ j ∈ neighbor A, b j) - ∑ i ∈ A, a i

/-- Subtracting the exact scalar reference population subtracts exactly its
scalar cut slack. Zero reference slack is therefore automatically safe. -/
theorem referenceHallSlack_residual {I J : Type*} [Fintype I] [Fintype J]
    (neighbor : Finset I → Finset J) (a a₀ : I → ℝ) (b b₀ : J → ℝ)
    (θ : ℝ) (A : Finset I) :
    referenceHallSlack neighbor (fun i ↦ a i - θ * a₀ i) (fun j ↦ b j - θ * b₀ j) A =
      referenceHallSlack neighbor a b A - θ * referenceHallSlack neighbor a₀ b₀ A := by
  simp only [referenceHallSlack, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

private theorem abs_sum_sub_le_card_mul
    {I : Type*} [Fintype I] (S : Finset I) (a p : I → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hclose : ∀ i, |a i - p i| ≤ δ) :
    |(∑ i ∈ S, a i) - ∑ i ∈ S, p i| ≤ (Fintype.card I : ℝ) * δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, |a i - p i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, δ := Finset.sum_le_sum fun i _ ↦ hclose i
    _ = (S.card : ℝ) * δ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ S) hδ

/-- Pointwise perturbations of finite class masses control every Hall cut at
once, without positivity of the reference cut slacks. -/
theorem abs_referenceHallSlack_sub_le
    {I J : Type*} [Fintype I] [Fintype J]
    (neighbor : Finset I → Finset J) (a a₀ : I → ℝ) (b b₀ : J → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ i, |a i - a₀ i| ≤ δ) (hb : ∀ j, |b j - b₀ j| ≤ δ) (A : Finset I) :
    |referenceHallSlack neighbor a b A - referenceHallSlack neighbor a₀ b₀ A| ≤
      ((Fintype.card I : ℝ) + Fintype.card J) * δ := by
  have hs := abs_sum_sub_le_card_mul A a a₀ hδ ha
  have ht := abs_sum_sub_le_card_mul (neighbor A) b b₀ hδ hb
  unfold referenceHallSlack
  calc
    _ = |((∑ j ∈ neighbor A, b j) - ∑ j ∈ neighbor A, b₀ j) -
        ((∑ i ∈ A, a i) - ∑ i ∈ A, a₀ i)| := by congr 1; ring
    _ ≤ |(∑ j ∈ neighbor A, b j) - ∑ j ∈ neighbor A, b₀ j| +
        |(∑ i ∈ A, a i) - ∑ i ∈ A, a₀ i| := abs_sub _ _
    _ ≤ (Fintype.card J : ℝ) * δ + (Fintype.card I : ℝ) * δ := add_le_add ht hs
    _ = _ := by ring

/-- Small supnorm perturbations of a feasible finite reference population
leave the residual after uniform reference thinning nonnegative and Hall
feasible. Tight reference cuts are included. This is a finite feasibility
statement; it does not yet choose a measurable residual population coupling. -/
theorem exists_tolerance_reference_residual_hall
    {I J : Type*} [Fintype I] [Fintype J]
    (neighbor : Finset I → Finset J) (a₀ : I → ℝ) (b₀ : J → ℝ)
    (ha₀ : ∀ i, 0 ≤ a₀ i) (hb₀ : ∀ j, 0 ≤ b₀ j)
    (hhall₀ : ∀ A, 0 ≤ referenceHallSlack neighbor a₀ b₀ A)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (a : I → ℝ) (b : J → ℝ),
      (∀ i, 0 ≤ a i) → (∀ j, 0 ≤ b j) →
      (∀ A, 0 ≤ referenceHallSlack neighbor a b A) →
      (∀ i, |a i - a₀ i| ≤ δ) → (∀ j, |b j - b₀ j| ≤ δ) →
      (∀ i, 0 ≤ a i - (1 - η) * a₀ i) ∧
      (∀ j, 0 ≤ b j - (1 - η) * b₀ j) ∧
      ∀ A, 0 ≤ referenceHallSlack neighbor
        (fun i ↦ a i - (1 - η) * a₀ i) (fun j ↦ b j - (1 - η) * b₀ j) A := by
  obtain ⟨δs, hδs, hs⟩ := exists_tolerance_for_reference_thinning a₀ ha₀ hη
  obtain ⟨δt, hδt, ht⟩ := exists_tolerance_for_reference_thinning b₀ hb₀ hη
  obtain ⟨δc, hδc, hcuts⟩ := exists_tolerance_for_reference_thinning
    (referenceHallSlack neighbor a₀ b₀) hhall₀ hη
  let C : ℝ := (Fintype.card I : ℝ) + Fintype.card J
  have hC : 0 ≤ C := by positivity
  let δ := min δs (min δt (δc / (C + 1)))
  have hδ : 0 < δ := lt_min hδs (lt_min hδt (by positivity))
  refine ⟨δ, hδ, ?_⟩
  intro a b ha hb hhall hsa htb
  have hs' := hs a ha (fun i ↦ (hsa i).trans (min_le_left _ _))
  have ht' := ht b hb (fun j ↦ (htb j).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  refine ⟨fun i ↦ sub_nonneg.mpr (hs' i), fun j ↦ sub_nonneg.mpr (ht' j), ?_⟩
  have hcutClose (A : Finset I) :
      |referenceHallSlack neighbor a b A - referenceHallSlack neighbor a₀ b₀ A| ≤ δc := by
    apply (abs_referenceHallSlack_sub_le neighbor a a₀ b b₀ hδ.le hsa htb A).trans
    have hbound : δ ≤ δc / (C + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hmul := (le_div_iff₀ (by positivity : 0 < C + 1)).mp hbound
    change C * δ ≤ δc
    nlinarith
  have hcut := hcuts (referenceHallSlack neighbor a b) hhall hcutClose
  intro A
  rw [referenceHallSlack_residual]
  exact sub_nonneg.mpr (hcut A)

end OTSelector.Reconstruction
