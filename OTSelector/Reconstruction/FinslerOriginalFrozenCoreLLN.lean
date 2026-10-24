import OTSelector.Reconstruction.FinslerOriginalFrozenCoreCampbellIdentification
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Frozen-core LLN: iid counting laws and expectation-level relative expansion

This module supplies the two analytic substeps of the frozen-core LLN left open
by `FinslerOriginalFrozenCoreCampbellIdentification.lean`.

## (b) Per-tile iid counting laws

For the original independent samples the module proves the exact
expectation-level counting laws of the original iid experiment:

* `integral_empiricalMean_eq`: the expected empirical mean of a fixed bounded
  measurable test is its population integral;
* `integral_sourceCellCount_eq`: the expected source count in a fixed population
  cell `S` is `n * μ(S)`;
* `integral_pairTest_eq` / `integral_pairSetCount_eq`: under pairwise
  independence the expected number of sample pairs inside a fixed measurable
  population event `R ⊆ M × M'` is `n * m` times the product population mass of
  `R`.  For the retained Taylor tiles `R` is the endpoint-pair set "both roots in
  the tile's root cell and both clocks in its retained window";
* `indepFun_family_pair`: independence of the two full sample families implies
  pairwise independence of every source/target sample pair;
* `integral_edgeMass_le_sourceCount`: the optimal-plan row-sum bound: for any
  fractional plan with unit row sums and nonnegative entries (in particular any
  optimal fractional assignment) the expected retained tile mass is at most the
  expected source count in the tile's population cell.  This is the paper's
  "disjoint source-core assignment counts each retained edge at most once"; its
  finite-sum aggregation over tiles was already proved in
  `integral_originalFrozenCorePressure_ge_sum_of_tile_bounds`
  (`FinslerOriginalFrozenCoreCampbellIdentification.lean`).

## (a) Expectation-level relative expansion

The pointwise Taylor relative comparison of `FinslerFrozenCoreDomination.lean`
says that on a retained edge the actual length-slack cost and the frozen
physical cost differ relatively by `2 ε`.  The module aggregates this over an
optimal fractional plan `A`:

* `maskedFrozenCost_ge_value_sub_unretained`: deterministic finite-matrix
  aggregation: if on the retained edges `β c - γ ≤ d` for the actual tilted cost
  `c` and frozen expression `d`, then the masked frozen cost is at least `β`
  times the retained part of the optimal value minus `γ` per row; the retained
  part of the optimal value is the total value minus the *unretained edge
  energy* `∑_{(i,j) ∉ Q} A i j c i j`;
* `integral_maskedFrozenCost_ge_expectation_relative`: the expectation form,
  with the actual value integral displayed;
* `integral_maskedFrozenCost_div_ge_expectation_relative`: the normalized form
  `E[frozen core cost] ≥ β (E[value] - E[unretained]/n) - γ`;
* `eventually_ge_of_relative_bounds`: the `o(1)` passage: if the normalized
  expected actual value converges to `L`, the normalized expected unretained
  edge energy vanishes, `β → 1` and `γ → 0`, then the normalized expected frozen
  core cost is asymptotically at least `L`.

The remaining sub-gap of (a) is exactly the vanishing of the *unretained* edge
energy (the legal-screening mass-loss statement), together with the elementary
per-edge passage from the two-sided Taylor comparison `|actual - frozen| ≤
2 ε · frozen` to the one-sided frozen lower bound `β c - γ ≤ d` used here.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M M' : Type*} [MeasurableSpace M] [MeasurableSpace M']
  {μ : Measure M} {ν : Measure M'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Expected empirical mean of a fixed bounded test.**  For independent samples
`X i` with common law `μ`, the expectation of the empirical mean of a bounded
measurable test is its population integral. -/
theorem integral_empiricalMean_eq {n : ℕ} (X : Fin n → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hXlaw : ∀ i, P.map (X i) = μ)
    (ϕ : M → ℝ) (hϕ : Measurable ϕ) {B : ℝ} (hϕb : ∀ x, |ϕ x| ≤ B) :
    ∫ s, (∑ i, ϕ (X i s)) ∂P = (n : ℝ) * ∫ x, ϕ x ∂μ := by
  have hInt (i : Fin n) : Integrable (fun s ↦ ϕ (X i s)) P := by
    refine Integrable.of_bound ((hϕ.comp (hX i)).aestronglyMeasurable) B ?_
    filter_upwards with s
    simpa only [Function.comp_apply, Real.norm_eq_abs] using hϕb (X i s)
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hInt i)]
  have hterm (i : Fin n) : ∫ s, ϕ (X i s) ∂P = ∫ x, ϕ x ∂μ := by
    rw [← hXlaw i]
    exact (integral_map (hX i).aemeasurable hϕ.aestronglyMeasurable).symm
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Expected source count in a fixed population cell.** -/
theorem integral_sourceCellCount_eq {n : ℕ} {Z : Type*} [MeasurableSpace Z]
    (a : M → Z) (ha : Measurable a) (S : Set Z) (hS : MeasurableSet S)
    (X : Fin n → Ω → M) (hX : ∀ i, Measurable (X i)) (hXlaw : ∀ i, P.map (X i) = μ) :
    ∫ s, (∑ i, (S.indicator (fun _ ↦ (1 : ℝ))) (a (X i s))) ∂P =
      (n : ℝ) * μ.real (a ⁻¹' S) := by
  have hbdd : ∀ x, |(S.indicator (fun _ : Z ↦ (1 : ℝ))) (a x)| ≤ 1 := by
    intro x
    by_cases hx : a x ∈ S
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx]; norm_num
  have h := integral_empiricalMean_eq (P := P) (μ := μ) X hX hXlaw
    (fun x ↦ (S.indicator (fun _ : Z ↦ (1 : ℝ))) (a x))
    ((Measurable.indicator measurable_const hS).comp ha) hbdd
  rw [h]
  congr 1
  have hpt : (fun x ↦ (S.indicator (fun _ : Z ↦ (1 : ℝ))) (a x)) =
      (a ⁻¹' S).indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    by_cases hx : a x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mem_preimage.mpr hx)]
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (fun h ↦ hx (Set.mem_preimage.mp h))]
  rw [hpt]
  exact MeasureTheory.integral_indicator_one (hS.preimage ha)

/-- **Expected number of independent pairs in a fixed product event.** -/
theorem integral_pairCount_eq {n m : ℕ} (X : Fin n → Ω → M) (Y : Fin m → Ω → M')
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hpair : ∀ i j, IndepFun (X i) (Y j) P)
    (ϕ : M → ℝ) (ψ : M' → ℝ) (hϕ : Measurable ϕ) (hψ : Measurable ψ)
    {Bϕ Bψ : ℝ} (hϕb : ∀ x, |ϕ x| ≤ Bϕ) (hψb : ∀ y, |ψ y| ≤ Bψ) :
    ∫ s, (∑ i, ∑ j, ϕ (X i s) * ψ (Y j s)) ∂P =
      ((n : ℝ) * ∫ x, ϕ x ∂μ) * ((m : ℝ) * ∫ y, ψ y ∂ν) := by
  have hprodInt (i : Fin n) (j : Fin m) :
      Integrable (fun s ↦ ϕ (X i s) * ψ (Y j s)) P := by
    refine Integrable.of_bound
      (((hϕ.comp (hX i)).mul (hψ.comp (hY j))).aestronglyMeasurable) (Bϕ * Bψ) ?_
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hϕb (X i s)) (hψb (Y j s))
      (abs_nonneg (ψ (Y j s)))
      (le_trans (abs_nonneg (ϕ (X i s))) (hϕb (X i s)))
  have hϕint (i : Fin n) : ∫ s, ϕ (X i s) ∂P = ∫ x, ϕ x ∂μ := by
    rw [← hXlaw i]
    exact (integral_map (hX i).aemeasurable hϕ.aestronglyMeasurable).symm
  have hψint (j : Fin m) : ∫ s, ψ (Y j s) ∂P = ∫ y, ψ y ∂ν := by
    rw [← hYlaw j]
    exact (integral_map (hY j).aemeasurable hψ.aestronglyMeasurable).symm
  have hprod (i : Fin n) (j : Fin m) :
      ∫ s, ϕ (X i s) * ψ (Y j s) ∂P = (∫ x, ϕ x ∂μ) * (∫ y, ψ y ∂ν) := by
    have hind := (hpair i j).comp hϕ hψ
    have h := hind.integral_fun_mul_eq_mul_integral
      ((hϕ.comp (hX i)).aestronglyMeasurable) ((hψ.comp (hY j)).aestronglyMeasurable)
    simpa only [Function.comp_apply, hϕint i, hψint j] using h
  have hbound : ∀ i : Fin n, Integrable (fun s ↦ ∑ j, ϕ (X i s) * ψ (Y j s)) P := by
    intro i
    refine Integrable.of_bound
      ((Finset.measurable_sum Finset.univ fun j _ ↦
        (hϕ.comp (hX i)).mul (hψ.comp (hY j))).aestronglyMeasurable)
      ((m : ℝ) * (Bϕ * Bψ)) ?_
    filter_upwards with s
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |ϕ (X i s) * ψ (Y j s)|
        ≤ ∑ _j : Fin m, Bϕ * Bψ := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          rw [abs_mul]
          exact mul_le_mul (hϕb (X i s)) (hψb (Y j s))
            (abs_nonneg (ψ (Y j s)))
            (le_trans (abs_nonneg (ϕ (X i s))) (hϕb (X i s)))
      _ = (m : ℝ) * (Bϕ * Bψ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum : ∫ s, (∑ i, ∑ j, ϕ (X i s) * ψ (Y j s)) ∂P =
      ∑ i : Fin n, ∑ j : Fin m, (∫ x, ϕ x ∂μ) * (∫ y, ψ y ∂ν) := by
    rw [integral_finsetSum Finset.univ (fun i _ ↦ hbound i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum Finset.univ (fun j _ ↦ hprodInt i j)]
    exact Finset.sum_congr rfl fun j _ ↦ hprod i j
  rw [hsum]
  calc ∑ i : Fin n, (∑ j : Fin m, (∫ x, ϕ x ∂μ) * (∫ y, ψ y ∂ν))
      = ∑ _i : Fin n, ((m : ℝ) * ((∫ x, ϕ x ∂μ) * (∫ y, ψ y ∂ν))) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (n : ℝ) * ((m : ℝ) * ((∫ x, ϕ x ∂μ) * (∫ y, ψ y ∂ν))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ((n : ℝ) * ∫ x, ϕ x ∂μ) * ((m : ℝ) * ∫ y, ψ y ∂ν) := by ring

end OTSelector.Probability


namespace OTSelector

/-! ## (a) Expectation-level relative expansion -/

/-- **Deterministic relative-expansion aggregation over an optimal fractional plan.**

Let `c` be the actual tilted edge cost, `A` an optimal fractional assignment of
`c`, `Q` the set of retained edges and `d` the frozen edge expression, and
suppose that on the retained edges the frozen expression is at least
`β c - γ`.  Then the masked frozen cost is at least `β` times the retained part
of the optimal value, minus `γ` per row.  The retained part of the optimal value
is the total value minus the *unretained edge energy*
`∑_{(i,j) ∉ Q} A i j c i j`, the only mass loss in the aggregation. -/
theorem maskedFrozenCost_ge_value_sub_unretained
    {n : ℕ} {c d : Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    {β γ : ℝ} {Q : Set (Fin n × Fin n)}
    (hA : OptimalFractionalAssignment c A) (hγ : 0 ≤ γ)
    (hrel : ∀ i j, (i, j) ∈ Q → β * c i j - γ ≤ d i j) :
    β * (fractionalAssignmentCost c A -
        ∑ i, ∑ j, Qᶜ.indicator
          (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j))
      - γ * (n : ℝ) ≤ fractionalAssignmentCost (maskedFrozenCost Q d) A := by
  classical
  have hPds : A ∈ doublyStochastic ℝ (Fin n) := hA.1
  have hAnonneg : ∀ i j, 0 ≤ A i j := hPds.1
  have hrow : ∀ i, ∑ j, A i j = 1 := fun i ↦ sum_row_of_mem_doublyStochastic hPds i
  have hsplit (i j : Fin n) : A i j * c i j =
      Q.indicator (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j) +
      Qᶜ.indicator (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j) := by
    by_cases h : (i, j) ∈ Q
    · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (by simpa using h), add_zero]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (by simpa using h), zero_add]
  have htotal : fractionalAssignmentCost c A =
      (∑ i, ∑ j, Q.indicator
        (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j)) +
      ∑ i, ∑ j, Qᶜ.indicator
        (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j) := by
    rw [fractionalAssignmentCost]
    have h1 : (∑ i, ∑ j, A i j * c i j) =
        ∑ i, ∑ j, (Q.indicator (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j) +
          Qᶜ.indicator (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j)) :=
      Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hsplit i j
    rw [h1]
    simp only [Finset.sum_add_distrib]
  have hstep : fractionalAssignmentCost (maskedFrozenCost Q d) A ≥
      ∑ i, ∑ j, A i j *
        (Q.indicator (fun p : Fin n × Fin n ↦ β * c p.1 p.2 - γ) (i, j)) := by
    rw [fractionalAssignmentCost]
    refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
    refine mul_le_mul_of_nonneg_left ?_ (hAnonneg i j)
    by_cases h : (i, j) ∈ Q
    · rw [Set.indicator_of_mem h, maskedFrozenCost_apply_of_mem h]
      exact hrel i j h
    · rw [Set.indicator_of_notMem h, maskedFrozenCost_apply_of_not_mem h]
  have hpt (i j : Fin n) : A i j *
      (Q.indicator (fun p : Fin n × Fin n ↦ β * c p.1 p.2 - γ) (i, j)) =
      β * (Q.indicator (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j)) -
      γ * (Q.indicator (fun p : Fin n × Fin n ↦ A p.1 p.2) (i, j)) := by
    by_cases h : (i, j) ∈ Q
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Set.indicator_of_mem h]; ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h,
        Set.indicator_of_notMem h]; ring
  have hexpand : (∑ i, ∑ j, A i j *
        (Q.indicator (fun p : Fin n × Fin n ↦ β * c p.1 p.2 - γ) (i, j))) =
      β * (∑ i, ∑ j, Q.indicator
        (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j)) -
      γ * (∑ i, ∑ j, Q.indicator
        (fun p : Fin n × Fin n ↦ A p.1 p.2) (i, j)) := by
    simp only [hpt, Finset.sum_sub_distrib, Finset.mul_sum]
  have hrowmass : (∑ i, ∑ j, Q.indicator (fun p : Fin n × Fin n ↦ A p.1 p.2) (i, j)) ≤
      (n : ℝ) := by
    have hle : (∑ i, ∑ j, Q.indicator (fun p : Fin n × Fin n ↦ A p.1 p.2) (i, j)) ≤
        ∑ i, ∑ j, A i j := by
      refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
      by_cases h : (i, j) ∈ Q
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h]
        exact hAnonneg i j
    calc (∑ i, ∑ j, Q.indicator (fun p : Fin n × Fin n ↦ A p.1 p.2) (i, j))
        ≤ ∑ i, ∑ j, A i j := hle
      _ = ∑ _i : Fin n, (1 : ℝ) := Finset.sum_congr rfl fun i _ ↦ hrow i
      _ = (n : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [hexpand] at hstep
  have hγS : γ * (∑ i, ∑ j, Q.indicator (fun p : Fin n × Fin n ↦ A p.1 p.2) (i, j)) ≤
      γ * (n : ℝ) := mul_le_mul_of_nonneg_left hrowmass hγ
  have hV : fractionalAssignmentCost c A - (∑ i, ∑ j, Qᶜ.indicator
        (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j)) =
      ∑ i, ∑ j, Q.indicator
        (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j) := by
    linarith [htotal]
  have hV' : β * (fractionalAssignmentCost c A - (∑ i, ∑ j, Qᶜ.indicator
        (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j))) =
      β * (∑ i, ∑ j, Q.indicator
        (fun p : Fin n × Fin n ↦ A p.1 p.2 * c p.1 p.2) (i, j)) := by
    rw [hV]
  linarith [hstep, hγS, hV']

/-- **Expectation-level relative expansion.**

The deterministic aggregation, integrated over the sample law: for almost every
sample the frozen cost is at least `β` times the actual value minus the
unretained edge energy, minus `γ` per row.  This is the expectation-level form
of the Taylor relative comparison aggregated over the optimal fractional plan. -/
theorem integral_maskedFrozenCost_ge_expectation_relative
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω} [IsProbabilityMeasure sample]
    {n : ℕ} {β γ : ℝ} (hγ : 0 ≤ γ)
    {c d : Ω → Matrix (Fin n) (Fin n) ℝ} {A : Ω → Matrix (Fin n) (Fin n) ℝ}
    {Q : Ω → Set (Fin n × Fin n)}
    (hA : ∀ᵐ s ∂sample, OptimalFractionalAssignment (c s) (A s))
    (hrel : ∀ᵐ s ∂sample, ∀ i j, (i, j) ∈ Q s → β * c s i j - γ ≤ d s i j)
    (hIntFrozen : Integrable (fun s ↦
      fractionalAssignmentCost (maskedFrozenCost (Q s) (d s)) (A s)) sample)
    (hIntTotal : Integrable (fun s ↦ fractionalAssignmentCost (c s) (A s)) sample)
    (hIntUnret : Integrable (fun s ↦ ∑ i, ∑ j, (Q s)ᶜ.indicator
      (fun p : Fin n × Fin n ↦ A s p.1 p.2 * c s p.1 p.2) (i, j)) sample) :
    β * ((∫ s, fractionalAssignmentCost (c s) (A s) ∂sample) -
        ∫ s, (∑ i, ∑ j, (Q s)ᶜ.indicator
          (fun p : Fin n × Fin n ↦ A s p.1 p.2 * c s p.1 p.2) (i, j)) ∂sample)
      - γ * (n : ℝ) ≤
      ∫ s, fractionalAssignmentCost (maskedFrozenCost (Q s) (d s)) (A s) ∂sample := by
  classical
  let T : Ω → ℝ := fun s ↦ fractionalAssignmentCost (c s) (A s)
  let U : Ω → ℝ := fun s ↦ ∑ i, ∑ j, (Q s)ᶜ.indicator
    (fun p : Fin n × Fin n ↦ A s p.1 p.2 * c s p.1 p.2) (i, j)
  have hIntT : Integrable T sample := hIntTotal
  have hIntU : Integrable U sample := hIntUnret
  have hpt : ∀ᵐ s ∂sample, β * (T s - U s) - γ * (n : ℝ) ≤
      fractionalAssignmentCost (maskedFrozenCost (Q s) (d s)) (A s) := by
    filter_upwards [hA, hrel] with s hAs hrels
    exact maskedFrozenCost_ge_value_sub_unretained hAs hγ hrels
  have hIntG : Integrable (fun s ↦ β * (T s - U s) - γ * (n : ℝ)) sample :=
    ((hIntT.sub hIntU).const_mul β).sub (integrable_const _)
  have hmono := integral_mono_ae hIntG hIntFrozen hpt
  have hLHS : ∫ s, (β * (T s - U s) - γ * (n : ℝ)) ∂sample =
      β * ((∫ s, T s ∂sample) - ∫ s, U s ∂sample) - γ * (n : ℝ) := by
    have h1 : ∫ s, (β * (T s - U s)) ∂sample = β * ∫ s, (T s - U s) ∂sample :=
      integral_const_mul β (fun s ↦ T s - U s)
    have h2 : ∫ s, (T s - U s) ∂sample = (∫ s, T s ∂sample) - ∫ s, U s ∂sample :=
      integral_sub hIntT hIntU
    have h3 : ∫ s, (β * (T s - U s) - γ * (n : ℝ)) ∂sample =
        (∫ s, (β * (T s - U s)) ∂sample) -
          ∫ s, (fun _ : Ω ↦ γ * (n : ℝ)) s ∂sample :=
      integral_sub ((hIntT.sub hIntU).const_mul β) (integrable_const _)
    have h4 : ∫ s, (fun _ : Ω ↦ γ * (n : ℝ)) s ∂sample = γ * (n : ℝ) := by
      rw [integral_const]
      simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    rw [h3, h1, h2, h4]
  exact hLHS ▸ hmono

/-- **Normalized expectation-level relative expansion.**  Dividing by the sample
size: the expected normalized frozen core cost is at least `β` times the
expected normalized pressure minus the unretained edge energy per row and
`γ`. -/
theorem integral_maskedFrozenCost_div_ge_expectation_relative
    {Ω : Type*} [MeasurableSpace Ω] {sample : Measure Ω} [IsProbabilityMeasure sample]
    {n : ℕ} (hn : 0 < n) {β γ : ℝ} (hγ : 0 ≤ γ)
    {c d : Ω → Matrix (Fin n) (Fin n) ℝ} {A : Ω → Matrix (Fin n) (Fin n) ℝ}
    {Q : Ω → Set (Fin n × Fin n)}
    (hA : ∀ᵐ s ∂sample, OptimalFractionalAssignment (c s) (A s))
    (hrel : ∀ᵐ s ∂sample, ∀ i j, (i, j) ∈ Q s → β * c s i j - γ ≤ d s i j)
    (hIntFrozen : Integrable (fun s ↦
      fractionalAssignmentCost (maskedFrozenCost (Q s) (d s)) (A s)) sample)
    (hIntTotal : Integrable (fun s ↦ fractionalAssignmentCost (c s) (A s)) sample)
    (hIntUnret : Integrable (fun s ↦ ∑ i, ∑ j, (Q s)ᶜ.indicator
      (fun p : Fin n × Fin n ↦ A s p.1 p.2 * c s p.1 p.2) (i, j)) sample) :
    β * (((∫ s, fractionalAssignmentCost (c s) (A s) ∂sample) -
        ∫ s, (∑ i, ∑ j, (Q s)ᶜ.indicator
          (fun p : Fin n × Fin n ↦ A s p.1 p.2 * c s p.1 p.2) (i, j)) ∂sample) /
        (n : ℝ)) - γ ≤
      (∫ s, fractionalAssignmentCost (maskedFrozenCost (Q s) (d s)) (A s) ∂sample) /
        (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h := integral_maskedFrozenCost_ge_expectation_relative (sample := sample)
    (n := n) hγ hA hrel hIntFrozen hIntTotal hIntUnret
  have h2 := div_le_div_of_nonneg_right h hn'.le
  have hL : (β * ((∫ s, fractionalAssignmentCost (c s) (A s) ∂sample) -
        ∫ s, (∑ i, ∑ j, (Q s)ᶜ.indicator
          (fun p : Fin n × Fin n ↦ A s p.1 p.2 * c s p.1 p.2) (i, j)) ∂sample)
        - γ * (n : ℝ)) / (n : ℝ) =
      β * (((∫ s, fractionalAssignmentCost (c s) (A s) ∂sample) -
        ∫ s, (∑ i, ∑ j, (Q s)ᶜ.indicator
          (fun p : Fin n × Fin n ↦ A s p.1 p.2 * c s p.1 p.2) (i, j)) ∂sample) /
        (n : ℝ)) - γ := by
    field_simp
  rwa [hL] at h2

/-- **Passage from the relative expansion to the `o(1)` frozen-core LLN.**

If the normalized expected actual value converges to `L`, the normalized
expected unretained edge energy vanishes, `β k → 1` and `γ k → 0`, and for each
sample size the normalized frozen core cost is at least `β k` times the
normalized retained value minus `γ k`, then the normalized expected frozen core
cost is asymptotically at least `L`.  This is the `liminf` form of the
expectation-level relative expansion. -/
theorem eventually_ge_of_relative_bounds
    {A U F : ℕ → ℝ} {N : ℕ → ℕ} {β γ : ℕ → ℝ} {L : ℝ}
    (hA : Tendsto (fun k ↦ A k / (N k)) atTop (𝓝 L))
    (hU : Tendsto (fun k ↦ U k / (N k)) atTop (𝓝 0))
    (hβ : Tendsto β atTop (𝓝 1)) (hγ : Tendsto γ atTop (𝓝 0))
    (hineq : ∀ᶠ k in atTop, β k * ((A k - U k) / (N k)) - γ k ≤ F k) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, L - ε ≤ F k := by
  intro ε hε
  have hsub : Tendsto (fun k ↦ A k / (N k) - U k / (N k)) atTop (𝓝 (L - 0)) :=
    hA.sub hU
  have hsub' : Tendsto (fun k ↦ (A k - U k) / (N k)) atTop (𝓝 L) := by
    simpa only [sub_div, sub_zero] using hsub
  have hkey : Tendsto (fun k ↦ β k * ((A k - U k) / (N k)) - γ k) atTop (𝓝 L) := by
    have h := (hβ.mul hsub').sub hγ
    simpa only [one_mul, sub_zero] using h
  filter_upwards [hkey.eventually (Ioi_mem_nhds (by linarith : L - ε < L)), hineq]
    with k hk1 hk2
  linarith

end OTSelector


namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M M' : Type*} [MeasurableSpace M] [MeasurableSpace M']
  {μ : Measure M} {ν : Measure M'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Expected count of a general paired test.**  Under pairwise independence the
expected sum of a fixed bounded paired test over all independent pairs is the
product of the family sizes times its product-population integral. -/
theorem integral_pairTest_eq {n m : ℕ} (X : Fin n → Ω → M) (Y : Fin m → Ω → M')
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hpair : ∀ i j, IndepFun (X i) (Y j) P)
    (Φ : M × M' → ℝ) (hΦ : Measurable Φ) {B : ℝ} (hΦb : ∀ p, |Φ p| ≤ B) :
    ∫ s, (∑ i, ∑ j, Φ (X i s, Y j s)) ∂P =
      (n : ℝ) * (m : ℝ) * ∫ p, Φ p ∂(μ.prod ν) := by
  have hterm (i : Fin n) (j : Fin m) : ∫ s, Φ (X i s, Y j s) ∂P =
      ∫ p, Φ p ∂(μ.prod ν) := by
    have hmap : P.map (fun s ↦ (X i s, Y j s)) = μ.prod ν := by
      rw [(hpair i j).map_prod_eq_prod_map_map (hX i).aemeasurable (hY j).aemeasurable,
        hXlaw i, hYlaw j]
    have hmeas : AEStronglyMeasurable Φ (P.map (fun s ↦ (X i s, Y j s))) :=
      hΦ.aestronglyMeasurable (μ := (P.map (fun s ↦ (X i s, Y j s))))
    rw [← MeasureTheory.integral_map ((hX i).prodMk (hY j)).aemeasurable hmeas, hmap]
  have hIntProd (i : Fin n) (j : Fin m) : Integrable (fun s ↦ Φ (X i s, Y j s)) P := by
    refine Integrable.of_bound ((hΦ.comp ((hX i).prodMk (hY j))).aestronglyMeasurable) B ?_
    filter_upwards with s
    simpa only [Function.comp_apply, Real.norm_eq_abs] using hΦb (X i s, Y j s)
  have hsum : ∫ s, (∑ i, ∑ j, Φ (X i s, Y j s)) ∂P =
      ∑ i : Fin n, ∑ j : Fin m, ∫ p, Φ p ∂(μ.prod ν) := by
    rw [integral_finsetSum Finset.univ]
    · refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_finsetSum Finset.univ (fun j _ ↦ hIntProd i j)]
      exact Finset.sum_congr rfl fun j _ ↦ hterm i j
    · intro i _
      refine Integrable.of_bound ((Finset.measurable_sum Finset.univ fun j _ ↦
        hΦ.comp ((hX i).prodMk (hY j))).aestronglyMeasurable) ((m : ℝ) * B) ?_
      filter_upwards with s
      rw [Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ j, |Φ (X i s, Y j s)| ≤ ∑ _j : Fin m, B := by
            refine Finset.sum_le_sum fun j _ ↦ hΦb _
        _ = (m : ℝ) * B := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hsum]
  calc ∑ i : Fin n, ∑ j : Fin m, (∫ p, Φ p ∂(μ.prod ν))
      = ∑ _i : Fin n, ((m : ℝ) * (∫ p, Φ p ∂(μ.prod ν))) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (n : ℝ) * ((m : ℝ) * (∫ p, Φ p ∂(μ.prod ν))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (n : ℝ) * (m : ℝ) * ∫ p, Φ p ∂(μ.prod ν) := by ring

/-- **Pairwise independence of two independent sample families.**  From the
independence of the two full sample families, every individual source sample is
independent of every individual target sample. -/
theorem indepFun_family_pair {n m : ℕ} (X : Fin n → Ω → M) (Y : Fin m → Ω → M')
    (hXY : IndepFun (fun s i ↦ X i s) (fun s i ↦ Y i s) P) :
    ∀ i j, IndepFun (X i) (Y j) P := by
  intro i j
  exact hXY.comp (measurable_pi_apply i) (measurable_pi_apply j)

end OTSelector.Probability


namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M M' : Type*} [MeasurableSpace M] [MeasurableSpace M']
  {μ : Measure M} {ν : Measure M'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {Z : Type*} [MeasurableSpace Z]

/-- **Expected pair count in a fixed population event (iid counting law).**  For
two independent families with pairwise independence, the expected number of
sample pairs inside a fixed measurable population event `R ⊆ M × M'` is the
product of the family sizes times the product population mass of `R`.  For the
retained Taylor tiles `R` is the set of endpoint pairs whose roots lie in the
tile's root cell and whose clocks lie in its retained window. -/
theorem integral_pairSetCount_eq {n m : ℕ} (X : Fin n → Ω → M) (Y : Fin m → Ω → M')
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hpair : ∀ i j, IndepFun (X i) (Y j) P)
    (R : Set (M × M')) (hR : MeasurableSet R) :
    ∫ s, (∑ i, ∑ j, R.indicator (fun _ ↦ (1 : ℝ)) (X i s, Y j s)) ∂P =
      (n : ℝ) * (m : ℝ) * (μ.prod ν).real R := by
  have hbdd : ∀ p : M × M', |R.indicator (fun _ ↦ (1 : ℝ)) p| ≤ 1 := by
    intro p
    by_cases hp : p ∈ R
    · rw [Set.indicator_of_mem hp]; norm_num
    · rw [Set.indicator_of_notMem hp]; norm_num
  rw [integral_pairTest_eq X Y hX hY hXlaw hYlaw hpair
    (R.indicator (fun _ ↦ (1 : ℝ))) (Measurable.indicator measurable_const hR) hbdd]
  congr 1
  exact MeasureTheory.integral_indicator_one hR

/-- **Optimal-plan row-sum bound for the retained tile mass.**  For any
fractional plan `A` with unit row sums and nonnegative entries (in particular any
optimal fractional assignment), the expected mass of retained pairs inside a
population event whose source endpoints lie in a fixed source cell is at most
the expected source count in that cell.  This is the paper's statement that
disjoint source-core assignment counts each retained edge at most once. -/
theorem integral_edgeMass_le_sourceCount {n : ℕ}
    (a : M → Z) (ha : Measurable a) (S : Set Z) (hS : MeasurableSet S)
    (X Y : Fin n → Ω → M) (hX : ∀ i, Measurable (X i))
    (hXlaw : ∀ i, P.map (X i) = μ)
    (R : Set (M × M)) (hR : MeasurableSet R) (hRsub : ∀ p ∈ R, a p.1 ∈ S)
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hAsum : ∀ᵐ s ∂P, ∀ i, ∑ j, A s i j = 1)
    (hAnonneg : ∀ᵐ s ∂P, ∀ i j, 0 ≤ A s i j)
    (hIntEdge : Integrable (fun s ↦
      ∑ i, ∑ j, A s i j * R.indicator (fun _ ↦ (1 : ℝ)) (X i s, Y j s)) P) :
    ∫ s, (∑ i, ∑ j, A s i j * R.indicator (fun _ ↦ (1 : ℝ)) (X i s, Y j s)) ∂P ≤
      (n : ℝ) * μ.real (a ⁻¹' S) := by
  have hRmeas : Measurable (R.indicator (fun _ : M × M ↦ (1 : ℝ))) :=
    Measurable.indicator measurable_const hR
  have hSmeas : Measurable (S.indicator (fun _ : Z ↦ (1 : ℝ))) :=
    Measurable.indicator measurable_const hS
  -- pointwise row-sum bound
  have hpt : ∀ᵐ s ∂P,
      (∑ i, ∑ j, A s i j * R.indicator (fun _ ↦ (1 : ℝ)) (X i s, Y j s)) ≤
      ∑ i, (S.indicator (fun _ ↦ (1 : ℝ))) (a (X i s)) := by
    filter_upwards [hAsum, hAnonneg] with s hsum hnonneg
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hstep : (∑ j, A s i j * R.indicator (fun _ ↦ (1 : ℝ)) (X i s, Y j s)) ≤
        ∑ j, A s i j * (S.indicator (fun _ ↦ (1 : ℝ))) (a (X i s)) := by
      refine Finset.sum_le_sum fun j _ ↦ ?_
      refine mul_le_mul_of_nonneg_left ?_ (hnonneg i j)
      by_cases hmem : (X i s, Y j s) ∈ R
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hRsub _ hmem)]
      · rw [Set.indicator_of_notMem hmem]
        exact Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _
    calc (∑ j, A s i j * R.indicator (fun _ ↦ (1 : ℝ)) (X i s, Y j s))
        ≤ ∑ j, A s i j * (S.indicator (fun _ ↦ (1 : ℝ))) (a (X i s)) := hstep
      _ = (∑ j, A s i j) * (S.indicator (fun _ ↦ (1 : ℝ))) (a (X i s)) := by
          rw [Finset.sum_mul]
      _ = (S.indicator (fun _ ↦ (1 : ℝ))) (a (X i s)) := by rw [hsum i, one_mul]
  have hIntSrc : Integrable (fun s ↦ ∑ i, (S.indicator (fun _ ↦ (1 : ℝ))) (a (X i s))) P := by
    refine Integrable.of_bound
      ((Finset.measurable_sum Finset.univ fun i _ ↦
        hSmeas.comp (ha.comp (hX i))).aestronglyMeasurable) (n : ℝ) ?_
    filter_upwards with s
    rw [Real.norm_eq_abs]
    have hb : ∀ i : Fin n, |(S.indicator (fun _ ↦ (1 : ℝ))) (a (X i s))| ≤ 1 := by
      intro i
      by_cases h : a (X i s) ∈ S
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |(S.indicator (fun _ ↦ (1 : ℝ))) (a (X i s))| ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ hb i
      _ = (n : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hmono := integral_mono_ae hIntEdge hIntSrc hpt
  have hsrc := integral_sourceCellCount_eq (P := P) (μ := μ) a ha S hS X hX hXlaw
  rw [hsrc] at hmono
  exact hmono

end OTSelector.Probability
