import OTSelector.Reconstruction.FinslerOriginalTileDualStability

/-!
# Dual certificate and plan-free average-cost control

This module closes the formalizable part of task 132 and packages the reduction of
`TilePlanResidualVanishing` to a single named analytic input.

**Dual weak duality (proved).**  For every dual-feasible pair `(f,g)`
(`f_i + g_j ≤ E_ij`) and every nonnegative doubly stochastic plan `A` (row and column
sums one),

  `∑ i, f i + ∑ j, g j ≤ fac(E,A).`

**Dual certificate bound (proved).**  If `A` is optimal for the frozen cost `E` over
the doubly stochastic polytope and `U` is the uniform plan, then

  `0 ≤ fac(E,U) - fac(E,A) ≤ (1/(m+1)) ∑ i ∑ j (E_ij - f_i - g_j).`

The right-hand side is the average dual slack: the *magnitude* of the plan residual
is bounded by it.  This is the dual-optimality estimate.

**Plan-free average-cost control (packaged).**  Combining this with the absolute
weighted bound of `FinslerOriginalTileDualStability.lean`, `TilePlanResidualVanishing`
reduces to the single named input `PlanFreeAverageCostControl`:

  `|plan residual| ≤ 2 fac(E,U)  and  fac(E,U) / (n+1) → 0,`

equivalently, by the dual certificate, to the vanishing of the average dual slack.
The implication `PlanFreeAverageCostControl ⇒ normalized plan residual → 0` is proved
below (`tendsto_normalized_residual_zero_of_planFreeControl`).

The remaining analytic input is exactly `PlanFreeAverageCostControl` for the frozen
core cost (dual potentials near-tight on average); it is not derivable from the
Taylor expansion alone.

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

namespace OTSelector.Reconstruction

/-- **Dual weak duality for the frozen cost over the doubly stochastic polytope.**
Every nonnegative doubly stochastic plan pays at least the dual value of every
dual-feasible pair. -/
theorem sum_dualPotentials_le_fractionalAssignmentCost (m : ℕ)
    (E A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hAnonneg : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1)
    (f g : Fin (m + 1) → ℝ) (hdual : ∀ i j, f i + g j ≤ E i j) :
    (∑ i, f i) + (∑ j, g j) ≤ fractionalAssignmentCost E A := by
  have hdual' : ∀ i j, A i j * (f i + g j) ≤ A i j * E i j :=
    fun i j ↦ mul_le_mul_of_nonneg_left (hdual i j) (hAnonneg i j)
  have hAdual : (∑ i, f i) + (∑ j, g j) = ∑ i, ∑ j, A i j * (f i + g j) := by
    have hterm : ∀ i : Fin (m + 1), ∑ j : Fin (m + 1), A i j * (f i + g j) =
        (∑ j, A i j) * f i + ∑ j, A i j * g j := by
      intro i
      calc ∑ j : Fin (m + 1), A i j * (f i + g j)
          = ∑ j : Fin (m + 1), (A i j * f i + A i j * g j) :=
            Finset.sum_congr rfl fun j _ ↦ by ring
        _ = (∑ j : Fin (m + 1), A i j * f i) + ∑ j : Fin (m + 1), A i j * g j :=
            Finset.sum_add_distrib
        _ = (∑ j : Fin (m + 1), A i j) * f i + ∑ j : Fin (m + 1), A i j * g j := by
            rw [(Finset.sum_mul Finset.univ (fun j ↦ A i j) (f i)).symm]
    have hfirst : ∑ i : Fin (m + 1), (∑ j : Fin (m + 1), A i j) * f i = ∑ i, f i := by
      calc ∑ i : Fin (m + 1), (∑ j : Fin (m + 1), A i j) * f i
          = ∑ i : Fin (m + 1), 1 * f i := by
            refine Finset.sum_congr rfl fun i _ ↦ by rw [hrow i]
        _ = ∑ i, f i := by simp
    have hsecond : ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), A i j * g j = ∑ j, g j := by
      calc ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), A i j * g j
          = ∑ j : Fin (m + 1), ∑ i : Fin (m + 1), A i j * g j := Finset.sum_comm
        _ = ∑ j : Fin (m + 1), (∑ i : Fin (m + 1), A i j) * g j := by
            refine Finset.sum_congr rfl fun j _ ↦
              (Finset.sum_mul Finset.univ (fun i ↦ A i j) (g j)).symm
        _ = ∑ j : Fin (m + 1), 1 * g j := by
            refine Finset.sum_congr rfl fun j _ ↦ by rw [hcol j]
        _ = ∑ j, g j := by simp
    calc (∑ i, f i) + (∑ j, g j)
        = ∑ i : Fin (m + 1), ((∑ j : Fin (m + 1), A i j) * f i +
            ∑ j : Fin (m + 1), A i j * g j) := by
          rw [Finset.sum_add_distrib, hfirst, hsecond]
      _ = ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), A i j * (f i + g j) := by
          refine Finset.sum_congr rfl fun i _ ↦ (hterm i).symm
  calc (∑ i, f i) + (∑ j, g j)
      = ∑ i, ∑ j, A i j * (f i + g j) := hAdual
    _ ≤ ∑ i, ∑ j, A i j * E i j :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hdual' i j
    _ = fractionalAssignmentCost E A := rfl

/-- **Dual certificate bound on the optimality advantage.**  For an optimal plan `A`
and a dual-feasible pair `(f,g)`, the magnitude of the plan residual is at most the
average dual slack `(1/(m+1)) ∑ i ∑ j (E_ij - f_i - g_j)`. -/
theorem optimalityAdvantage_le_averageDualSlack (m : ℕ)
    (E A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hAnonneg : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j = 1) (hcol : ∀ j, ∑ i, A i j = 1)
    (hopt : fractionalAssignmentCost E A ≤
      fractionalAssignmentCost E (fun _ _ ↦ 1 / ((m + 1 : ℕ) : ℝ)))
    (f g : Fin (m + 1) → ℝ) (hdual : ∀ i j, f i + g j ≤ E i j) :
    fractionalAssignmentCost E (fun _ _ ↦ 1 / ((m + 1 : ℕ) : ℝ)) -
        fractionalAssignmentCost E A ≤
      (1 / ((m + 1 : ℕ) : ℝ)) * ∑ i, ∑ j, (E i j - (f i + g j)) := by
  have hm : (((m + 1 : ℕ)) : ℝ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hweak :=
    sum_dualPotentials_le_fractionalAssignmentCost m E A hAnonneg hrow hcol f g hdual
  have huniform := fractionalAssignmentCost_uniformPlan m E
  have hfg : ∑ i, ∑ j, (E i j - (f i + g j)) =
      (∑ i, ∑ j, E i j) - (((m + 1 : ℕ) : ℝ) * ((∑ i, f i) + (∑ j, g j))) := by
    have hsplit : ∑ i, ∑ j, (E i j - (f i + g j)) =
        (∑ i, ∑ j, E i j) - ∑ i, ∑ j, (f i + g j) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_sub_distrib]
    have hrowfg : ∀ i : Fin (m + 1), ∑ j : Fin (m + 1), (f i + g j) =
        ((m + 1 : ℕ) : ℝ) * f i + (∑ j, g j) := by
      intro i
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have hsumfg : ∑ i : Fin (m + 1), (((m + 1 : ℕ) : ℝ) * f i + (∑ j, g j)) =
        ((m + 1 : ℕ) : ℝ) * (∑ i, f i) + ((m + 1 : ℕ) : ℝ) * (∑ j, g j) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
      · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsplit, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) ↦ hrowfg i), hsumfg]
    ring
  rw [huniform, hfg]
  have hkey : (1 / (((m + 1 : ℕ)) : ℝ)) * ((∑ i, ∑ j, E i j) -
      (((m + 1 : ℕ)) : ℝ) * ((∑ i, f i) + (∑ j, g j))) =
      (1 / (((m + 1 : ℕ)) : ℝ)) * (∑ i, ∑ j, E i j) -
        ((∑ i, f i) + (∑ j, g j)) := by
    field_simp
  rw [hkey]
  linarith

/-- **The single remaining analytic input of `TilePlanResidualVanishing`: plan-free
average-cost control.**  The plan residual is bounded by twice the plan-free
uniform cost `fac n` and that cost normalized by `n+1` vanishes. -/
def PlanFreeAverageCostControl (R fac : ℕ → ℝ) : Prop :=
  (∀ n, |R n| ≤ 2 * fac n) ∧
    Tendsto (fun n ↦ fac n / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0)

/-- **Plan-free average-cost control implies vanishing of the normalized plan
residual.**  This is the exact reduction of `TilePlanResidualVanishing`. -/
theorem tendsto_normalized_residual_zero_of_planFreeControl
    (R fac : ℕ → ℝ) (h : PlanFreeAverageCostControl R fac) :
    Tendsto (fun n ↦ R n / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  obtain ⟨hbound, hlim⟩ := h
  refine tendsto_normalized_residual_zero_of_weighted R (fun n ↦ 2 * fac n) ?_ ?_
  · intro n
    simpa using hbound n
  · have h2 : Tendsto (fun n ↦ 2 * (fac n / ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
      simpa using hlim.const_mul 2
    refine h2.congr' ?_
    filter_upwards with n
    ring

end OTSelector.Reconstruction
