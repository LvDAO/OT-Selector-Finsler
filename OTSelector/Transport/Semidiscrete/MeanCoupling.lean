import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Kernel.CondDistrib
import OTSelector.Finite.AssignmentCavity
import OTSelector.Finite.FractionalOptimal
import OTSelector.Finite.PerturbedValue
import OTSelector.Probability.Dirichlet.CavitySuccess
import OTSelector.Transport.Semidiscrete.CavityCells
import OTSelector.Transport.Semidiscrete.MeanPlan
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteMean.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteMean`; the selected original proof blocks follow. -/
section

/-!
Conditions: Finite iid rows with the stated measurable atomless pairwise cost differences, actual optimal fractional assignments and integrable observables.

Objects: The same canonical cavity mean for every row and for the mean of the full optimal plan.

Proof detail: Delete the selected row, reindex the remaining iid product, apply the independent-row cavity readout identity and sum the equal row expectations.

Sources: Rick Durrett, Section 2.1.2, Theorems 2.1.11–2.1.13, pp. 48–49 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56); D. H. Fremlin, Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19); Gabriel Peyré, Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31); Project manuscript, Section “Exact iid cavity disintegration”, Theorem thm:iid-cavity-dirichlet and Proposition prop:iid-cavity-mean, equation eq:iid-cavity-mean-plan (main.tex).
Relation: Exchangeability/product-law row-deletion identity. Its project assembly is main.tex prop:iid-cavity-mean, with arbitrary actual optimal fractional choices retained.
-/

/-!
# The exact iid empirical mean as a Dirichlet semidiscrete readout

Every deleted source coordinate produces the same ordinary iid cavity law after its
actual order-preserving enumeration. The row identity therefore averages over the
entire optimal fractional face, and the constructed mass-indexed readout transfers
that mean to the actual Dirichlet law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- The actual retained iid matrix with its unused placeholder in any deleted row. -/
def iidCavityInputCostAt (c : Fin (m + 1) → S → ℝ) (i : Fin (m + 1))
    (w : Fin m → S) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  i.insertNth (fun _ ↦ 0) (fun k j ↦ c j (w k))

omit [MeasurableSpace S] in
/-- Deleting the placeholder leaves the same actual ordered matrix for every row index. -/
theorem iidCavityInputCostAt_price (c : Fin (m + 1) → S → ℝ)
    (i j : Fin (m + 1)) (w : Fin m → S) :
    assignmentCavityValue (iidCavityInputCostAt c i w) i j =
      assignmentCavityValue (iidCapacityInputCost c (fun k w ↦ w k) w) 0 j := by
  unfold assignmentCavityValue
  congr 1
  funext k l
  simp [assignmentCavityCost, iidCavityInputCostAt, iidCapacityInputCost]

omit [MeasurableSpace S] in
/-- Actual reinsertion recovers every original source cost exactly. -/
theorem iidCavityInputCostAt_update (c : Fin (m + 1) → S → ℝ)
    (i : Fin (m + 1)) (x : Fin (m + 1) → S) :
    Function.update (iidCavityInputCostAt c i (fun k ↦ x (i.succAbove k))) i
      (fun j ↦ c j (x i)) = fun k j ↦ c j (x k) := by
  classical
  funext k j
  refine Fin.succAboveCases i ?_ (fun l ↦ ?_) k
  · simp
  · simp [iidCavityInputCostAt, i.succAbove_ne l]

/-- Every actual source row of every optimal fractional plan has the same canonical
cavity expectation against arbitrary integrable paired tests. -/
theorem integral_iid_optimalFractional_row_eq_canonical_cavity
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (i : Fin (m + 1))
    (A : (Fin (m + 1) → S) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hA : ∀ᵐ x ∂Measure.pi (fun _ : Fin (m + 1) ↦ μ),
      OptimalFractionalAssignment (fun k j ↦ c j (x k)) (A x))
    (g : S → Fin (m + 1) → ℝ) (hg : ∀ j, Integrable (fun s ↦ g s j) μ) :
    Integrable (fun x ↦ ∑ j, A x i j * g (x i) j)
      (Measure.pi (fun _ : Fin (m + 1) ↦ μ)) ∧
      (∫ x, ∑ j, A x i j * g (x i) j ∂Measure.pi (fun _ : Fin (m + 1) ↦ μ)) =
        ∫ w, cavityMeanReadout μ (iidCapacityInputCost c (fun k w ↦ w k))
          (fun z j ↦ c j z.2) 0 (fun z ↦ g z.2) w ∂Measure.pi (fun _ : Fin m ↦ μ) := by
  classical
  let P := Measure.pi (fun _ : Fin (m + 1) ↦ μ)
  let ν := Measure.pi (fun _ : Fin m ↦ μ)
  let W₀ : (Fin (m + 1) → S) → (Fin m → S) := fun x k ↦ x (i.succAbove k)
  let X : (Fin (m + 1) → S) → S := fun x ↦ x i
  have hW : Measurable W₀ := measurable_pi_iff.mpr fun _ ↦ measurable_pi_apply _
  have hX : Measurable X := measurable_pi_apply i
  have hpair : MeasurePreserving (fun x ↦ (W₀ x, X x)) P (ν.prod μ) :=
    Measure.measurePreserving_swap.comp (measurePreserving_piFinSuccAbove (fun _ ↦ μ) i)
  have hWlaw : P.map W₀ = ν := (measurePreserving_fst.comp hpair).map_eq
  have hXlaw : P.map X = μ := (measurePreserving_snd.comp hpair).map_eq
  have hindep : IndepFun W₀ X P := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hX.aemeasurable).mpr
    rw [hWlaw, hXlaw]
    exact hpair.map_eq
  have hret (k j : Fin (m + 1)) : Measurable (fun w ↦ iidCavityInputCostAt c i w k j) := by
    refine Fin.succAboveCases i ?_ (fun l ↦ ?_) k
    · simp only [iidCavityInputCostAt, Fin.insertNth_apply_same]
      exact measurable_const
    · simpa only [iidCavityInputCostAt, Fin.insertNth_apply_succAbove, Function.comp_def] using
        (hc j).comp (measurable_pi_apply l)
  have hA' : ∀ᵐ x ∂P, OptimalFractionalAssignment
      (Function.update (iidCavityInputCostAt c i (W₀ x)) i (fun j ↦ c j (X x))) (A x) := by
    simpa only [W₀, X, iidCavityInputCostAt_update] using hA
  have hmean := integral_optimalFractional_row_eq_cavityMeanReadout P μ W₀ X hW hX
    hindep hXlaw (iidCavityInputCostAt c i) (fun z j ↦ c j z.2) hret
    (fun j ↦ (hc j).comp measurable_snd) i
    (Eventually.of_forall fun _ ↦ hatom) A hA' (fun z ↦ g z.2)
    (fun j ↦ by rw [hWlaw]; exact (hg j).comp_snd ν)
  refine ⟨hmean.1, ?_⟩
  rw [hmean.2, hWlaw]
  apply integral_congr_ae
  filter_upwards with w
  unfold cavityMeanReadout
  apply Finset.sum_congr rfl
  intro j _
  have heq : {s | (w, s) ∈ cavityCell (iidCavityInputCostAt c i) (fun z j ↦ c j z.2) i j} =
      {s | (w, s) ∈ cavityCell (iidCapacityInputCost c (fun k w ↦ w k))
        (fun z j ↦ c j z.2) 0 j} := by
    ext s
    simp only [cavityCell, cavityScore, mem_ofPred_eq, iidCavityInputCostAt_price]
  rw [heq]

/-- The complete optimal fractional face has the same normalized empirical mean. -/
theorem integral_iid_optimalFractional_mean_eq_canonical_cavity
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (A : (Fin (m + 1) → S) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hA : ∀ᵐ x ∂Measure.pi (fun _ : Fin (m + 1) ↦ μ),
      OptimalFractionalAssignment (fun k j ↦ c j (x k)) (A x))
    (g : S → Fin (m + 1) → ℝ) (hg : ∀ j, Integrable (fun s ↦ g s j) μ) :
    Integrable (fun x ↦ (∑ i, ∑ j, A x i j * g (x i) j) / (m + 1 : ℕ))
      (Measure.pi (fun _ : Fin (m + 1) ↦ μ)) ∧
      (∫ x, (∑ i, ∑ j, A x i j * g (x i) j) / (m + 1 : ℕ)
        ∂Measure.pi (fun _ : Fin (m + 1) ↦ μ)) =
        ∫ w, cavityMeanReadout μ (iidCapacityInputCost c (fun k w ↦ w k))
          (fun z j ↦ c j z.2) 0 (fun z ↦ g z.2) w ∂Measure.pi (fun _ : Fin m ↦ μ) := by
  have hrow i := integral_iid_optimalFractional_row_eq_canonical_cavity μ c hc hatom i A hA g hg
  refine ⟨(integrable_finsetSum _ (fun i _ ↦ (hrow i).1)).div_const _, ?_⟩
  rw [integral_div, integral_finsetSum _ (fun i _ ↦ (hrow i).1)]
  simp_rw [fun i ↦ (hrow i).2]
  simp [mul_div_cancel_left₀, show (m : ℝ) + 1 ≠ 0 by positivity]

end OTSelector.Probability

end
end
