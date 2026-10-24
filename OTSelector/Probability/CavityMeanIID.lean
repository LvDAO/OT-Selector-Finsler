import OTSelector.Probability.CavityMeanPlan
import OTSelector.MeasureTheory.FinitePiCoordinate

/-!
# Exact cavity mean identity for the original finite iid source cloud

The retained matrix is built by deleting an actual coordinate of the original cloud.
Finite-product measure preservation supplies its independence from the inserted coordinate.
The mean-plan identity therefore needs only the original cost difference atomlessness and
integrable endpoint tests, not separate law, independence, or matrix reconstruction inputs.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {n : ℕ} {S : Type*} [MeasurableSpace S]

/-- The actual retained cost matrix; the deleted row is an unused zero placeholder. -/
def cavityRetainedCost (c : S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (w : {k : Fin (n + 1) // k ≠ i} → S) (k j : Fin (n + 1)) : ℝ :=
  if hk : k ≠ i then c (w ⟨k, hk⟩) j else 0

omit [MeasurableSpace S] in
/-- Reinsertion recovers the entire original iid assignment cost, entry for entry. -/
theorem cavityRetainedCost_update (c : S → Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → S) :
    Function.update (cavityRetainedCost c i (fun k ↦ x k)) i (c (x i)) =
      fun k j ↦ c (x k) j := by
  classical
  funext k j
  by_cases hk : k = i
  · subst k
    simp
  · simp [cavityRetainedCost, hk]

/-- The cavity expectation for one actual coordinate of the original finite iid law.
The same formula applies to every optimal fractional assignment and arbitrary integrable
tests of the source and fixed target label. -/
theorem integral_iid_optimalFractional_row_eq_cavity
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : S → Fin (n + 1) → ℝ) (hc : ∀ j, Measurable (fun x ↦ c x j))
    (hatom : ∀ j k, j ≠ k → NullSingletonClass (μ.map (fun x ↦ c x j - c x k)))
    (i : Fin (n + 1))
    (A : (Fin (n + 1) → S) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : ∀ᵐ x ∂Measure.pi (fun _ : Fin (n + 1) ↦ μ),
      OptimalFractionalAssignment (fun k j ↦ c (x k) j) (A x))
    (g : S → Fin (n + 1) → ℝ) (hg : ∀ j, Integrable (fun x ↦ g x j) μ) :
    Integrable (fun x ↦ ∑ j, A x i j * g (x i) j)
      (Measure.pi (fun _ : Fin (n + 1) ↦ μ)) ∧
      (∫ x, ∑ j, A x i j * g (x i) j ∂Measure.pi (fun _ : Fin (n + 1) ↦ μ)) =
        ∫ w, cavityMeanReadout μ (cavityRetainedCost c i) (fun z j ↦ c z.2 j) i
          (fun z j ↦ g z.2 j) w
          ∂Measure.pi (fun _ : {k : Fin (n + 1) // k ≠ i} ↦ μ) := by
  classical
  let P := Measure.pi (fun _ : Fin (n + 1) ↦ μ)
  let ν := Measure.pi (fun _ : {k : Fin (n + 1) // k ≠ i} ↦ μ)
  let W₀ : (Fin (n + 1) → S) → ({k : Fin (n + 1) // k ≠ i} → S) :=
    fun x k ↦ x k
  let X : (Fin (n + 1) → S) → S := fun x ↦ x i
  have hW : Measurable W₀ :=
    measurable_pi_iff.mpr fun k ↦ measurable_pi_apply (k : Fin (n + 1))
  have hX : Measurable X := measurable_pi_apply i
  have hpair : MeasurePreserving (fun x ↦ (W₀ x, X x)) P (ν.prod μ) :=
    Measure.measurePreserving_swap.comp (measurePreserving_piSplitAt μ i)
  have hWlaw : P.map W₀ = ν := (measurePreserving_fst.comp hpair).map_eq
  have hXlaw : P.map X = μ := (measurePreserving_snd.comp hpair).map_eq
  have hindep : IndepFun W₀ X P := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hX.aemeasurable).mpr
    rw [hWlaw, hXlaw]
    exact hpair.map_eq
  have hret k j : Measurable (fun w ↦ cavityRetainedCost c i w k j) := by
    by_cases hk : k ≠ i
    · simpa [cavityRetainedCost, hk, Function.comp_def] using
        (hc j).comp (measurable_pi_apply (⟨k, hk⟩ : {k : Fin (n + 1) // k ≠ i}))
    · simp [cavityRetainedCost, hk, measurable_const]
  have hA' : ∀ᵐ x ∂P, OptimalFractionalAssignment
      (Function.update (cavityRetainedCost c i (W₀ x)) i (c (X x))) (A x) := by
    filter_upwards [hA] with x hx
    simpa only [W₀, X, cavityRetainedCost_update] using hx
  have hmean := integral_optimalFractional_row_eq_cavityMeanReadout P μ W₀ X hW hX
    hindep hXlaw (cavityRetainedCost c i) (fun z j ↦ c z.2 j) hret
    (fun j ↦ (hc j).comp measurable_snd) i
    (Eventually.of_forall fun _ ↦ hatom) A hA' (fun z j ↦ g z.2 j)
    (fun j ↦ by rw [hWlaw]; exact (hg j).comp_snd ν)
  simpa only [hWlaw] using hmean

end OTSelector.Probability
