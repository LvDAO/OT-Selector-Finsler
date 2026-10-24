import OTSelector.Finite.PerturbedValue
import OTSelector.Finite.EmpiricalFractional
import OTSelector.Finite.FractionalGauge
import OTSelector.PointProcess.StationaryForwardMatching

/-!
# Deterministic core of the finite-domination inequality

The paper's finite-domination step (`general-gluing-finite-domination`) bounds the
frozen core cost `Γ_n(F_{R,N})` of an actual empirical optimizer by the normalized
empirical pressure `V_n(t)` plus the probe constant `B_t`, up to `o_ℙ(1)`.  This
module isolates and proves its deterministic matrix core.

Let `c`, `g`, `P` be `n × n` real matrices, with `P` a fractional coupling (unit
row and column sums, hence total mass `n`) that is optimal for the tilted
assignment problem `c + t g`, and let `E` be a frozen per-edge cost with

`E i j ≤ c i j + t * g i j + B` for all `i, j`.

Then

`(∑ i j, P i j * E i j) / n ≤ perturbedAssignmentValue c g t / n + B`.

No probability, measurability, or selection assumption enters this inequality:
it is pure finite linear algebra (nonnegativity of `P` and the row-sum identity
`∑ j, P i j = 1`).  In particular the nonnegativity of `E` is *not* needed for
the inequality; it is recorded in the masked version for the frozen-cost
interpretation.

The file then specializes:

* to a masked frozen cost `E i j = d i j` on a set `Q` of edges and `0` outside,
  where the bound `d i j ≤ c i j + t * g i j + B` is known only on `Q`; the
  complement requires `0 ≤ c i j + t * g i j + B`, which is discharged from
  `c ≥ 0`, `|g| ≤ Bg` and `B = |t| * Bg`;
* to the actual scaled distance slack `c i j = k * distanceSlackEdgeCost X Y φ i j`
  and a physical probe `g i j = f (X i, Y j)`, giving the deterministic
  frozen-core bound for every realization of an optimal fractional assignment;
* to the interface `OTSelector.PointProcess.FiniteDominationInequality`, from
  which the existing `empiricalPressureLowerComparison_of_finiteDomination` and
  `empiricalPressureProbabilityLower_of_finiteDomination` produce the paper's
  probability lower bound.

The remaining geometric input is the identification of the frozen matrix `E`
with the compact frozen core functional of the limiting rooted scene; the
deterministic comparison itself is unconditional.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 4096

namespace OTSelector

variable {n : ℕ}

/-! ## The deterministic core -/

/-- **Deterministic finite-domination core, unnormalized form.**  If `P` is an
optimal fractional coupling for the tilted matrix `c + t g` and the frozen edge
cost `E` is pointwise at most `c + t g + B`, then the total frozen cost is at most
the perturbed value plus `n * B`.

The only properties of `P` used are entrywise nonnegativity and unit row sums;
`E` need not be nonnegative. -/
theorem fractionalAssignmentCost_le_perturbedAssignmentValue_add
    {c g E P : Matrix (Fin n) (Fin n) ℝ} {t B : ℝ}
    (hP : OptimalFractionalAssignment (perturbedEdgeCost c g t) P)
    (hE : ∀ i j, E i j ≤ perturbedEdgeCost c g t i j + B) :
    fractionalAssignmentCost E P ≤ perturbedAssignmentValue c g t + (n : ℝ) * B := by
  have hPds : P ∈ doublyStochastic ℝ (Fin n) := hP.1
  have hvalue : fractionalAssignmentCost (perturbedEdgeCost c g t) P =
      perturbedAssignmentValue c g t :=
    (perturbedAssignmentValue_eq_of_optimalFractional c g P t hP).symm
  have hmono : fractionalAssignmentCost E P ≤
      fractionalAssignmentCost (perturbedEdgeCost c g t) P + (n : ℝ) * B := by
    calc fractionalAssignmentCost E P
        = ∑ i, ∑ j, P i j * E i j := rfl
      _ ≤ ∑ i, ∑ j, P i j * (perturbedEdgeCost c g t i j + B) := by
          refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
          exact mul_le_mul_of_nonneg_left (hE i j) (hPds.1 i j)
      _ = ∑ i, ∑ j, P i j * perturbedEdgeCost c g t i j +
            ∑ i, ∑ j, P i j * B := by
          simp only [mul_add, Finset.sum_add_distrib]
      _ = fractionalAssignmentCost (perturbedEdgeCost c g t) P + (n : ℝ) * B := by
          congr 1
          calc ∑ i, ∑ j, P i j * B
              = ∑ i, (∑ j, P i j) * B := by
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [Finset.sum_mul]
            _ = ∑ i, (1 : ℝ) * B := by
                  apply Finset.sum_congr rfl
                  intro i _
                  rw [sum_row_of_mem_doublyStochastic hPds]
            _ = (n : ℝ) * B := by
                  rw [Finset.sum_const, nsmul_eq_mul]
                  simp
  simpa only [hvalue] using hmono

/-- **Deterministic finite-domination core, normalized form.**  Dividing the
unnormalized inequality by the total mass `n` gives
`Γ_n ≤ V_n(t) + B`. -/
theorem fractionalAssignmentCost_div_le_perturbedAssignmentValue_div_add
    {c g E P : Matrix (Fin n) (Fin n) ℝ} {t B : ℝ} (hn : 0 < n)
    (hP : OptimalFractionalAssignment (perturbedEdgeCost c g t) P)
    (hE : ∀ i j, E i j ≤ perturbedEdgeCost c g t i j + B) :
    fractionalAssignmentCost E P / (n : ℝ) ≤
      perturbedAssignmentValue c g t / (n : ℝ) + B := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h := fractionalAssignmentCost_le_perturbedAssignmentValue_add hP hE
  have hdiv := div_le_div_of_nonneg_right h hn'.le
  have hrewrite : (perturbedAssignmentValue c g t + (n : ℝ) * B) / (n : ℝ) =
      perturbedAssignmentValue c g t / (n : ℝ) + B := by
    field_simp [hn'.ne']
  rwa [hrewrite] at hdiv

/-! ## Masked frozen costs -/

/-- The frozen per-edge cost supported on a set `Q` of edges: it equals `d` on
`Q` and vanishes outside. -/
noncomputable def maskedFrozenCost (Q : Set (Fin n × Fin n))
    (d : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ Q.indicator (fun p : Fin n × Fin n ↦ d p.1 p.2) (i, j)

@[simp]
theorem maskedFrozenCost_apply_of_mem {Q : Set (Fin n × Fin n)}
    {d : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (h : (i, j) ∈ Q) :
    maskedFrozenCost Q d i j = d i j := by
  simp only [maskedFrozenCost, Set.indicator_of_mem h]

@[simp]
theorem maskedFrozenCost_apply_of_not_mem {Q : Set (Fin n × Fin n)}
    {d : Matrix (Fin n) (Fin n) ℝ} {i j : Fin n} (h : (i, j) ∉ Q) :
    maskedFrozenCost Q d i j = 0 := by
  simp only [maskedFrozenCost, Set.indicator_of_notMem h]

/-- A masked frozen cost with nonnegative edge values is nonnegative. -/
theorem maskedFrozenCost_nonneg {Q : Set (Fin n × Fin n)}
    {d : Matrix (Fin n) (Fin n) ℝ} (hd : ∀ i j, 0 ≤ d i j) :
    ∀ i j, 0 ≤ maskedFrozenCost Q d i j := by
  intro i j
  by_cases h : (i, j) ∈ Q
  · rw [maskedFrozenCost_apply_of_mem h]
    exact hd i j
  · rw [maskedFrozenCost_apply_of_not_mem h]

/-- **Masked finite-domination core.**  The frozen cost acts on a set `Q` of
edges, with the pointwise bound known only on `Q`.  Outside `Q` the frozen cost
is zero, so the complement needs `0 ≤ c + t g + B`.  Nonnegativity of the edge
values `d` is recorded but not used by the algebraic inequality. -/
theorem maskedFrozenCost_div_le_perturbedAssignmentValue_div_add
    {c g d P : Matrix (Fin n) (Fin n) ℝ} {t B : ℝ}
    {Q : Set (Fin n × Fin n)} (hn : 0 < n)
    (_hd_nonneg : ∀ i j, 0 ≤ d i j)
    (hP : OptimalFractionalAssignment (perturbedEdgeCost c g t) P)
    (hd_bound : ∀ i j, (i, j) ∈ Q →
      d i j ≤ perturbedEdgeCost c g t i j + B)
    (hR_nonneg : ∀ i j, 0 ≤ perturbedEdgeCost c g t i j + B) :
    fractionalAssignmentCost (maskedFrozenCost Q d) P / (n : ℝ) ≤
      perturbedAssignmentValue c g t / (n : ℝ) + B := by
  refine fractionalAssignmentCost_div_le_perturbedAssignmentValue_div_add hn hP ?_
  intro i j
  by_cases h : (i, j) ∈ Q
  · rw [maskedFrozenCost_apply_of_mem h]
    exact hd_bound i j h
  · rw [maskedFrozenCost_apply_of_not_mem h]
    exact hR_nonneg i j

/-- The complement nonnegativity in the masked version is automatic when the
base cost is nonnegative, the probe is bounded by `Bg`, and `B = |t| * Bg`. -/
theorem maskedFrozenCost_div_le_perturbedAssignmentValue_div_add_of_nonneg
    {c g d P : Matrix (Fin n) (Fin n) ℝ} {t B Bg : ℝ}
    {Q : Set (Fin n × Fin n)} (hn : 0 < n)
    (_hd_nonneg : ∀ i j, 0 ≤ d i j)
    (hc_nonneg : ∀ i j, 0 ≤ c i j)
    (hg_bound : ∀ i j, |g i j| ≤ Bg)
    (hB : B = |t| * Bg)
    (hP : OptimalFractionalAssignment (perturbedEdgeCost c g t) P)
    (hd_bound : ∀ i j, (i, j) ∈ Q →
      d i j ≤ perturbedEdgeCost c g t i j + B) :
    fractionalAssignmentCost (maskedFrozenCost Q d) P / (n : ℝ) ≤
      perturbedAssignmentValue c g t / (n : ℝ) + B := by
  refine maskedFrozenCost_div_le_perturbedAssignmentValue_div_add hn _hd_nonneg hP
    hd_bound ?_
  intro i j
  have hc : 0 ≤ c i j := hc_nonneg i j
  have htg : 0 ≤ t * g i j + B := by
    have habs : |t * g i j| ≤ |t| * Bg := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hg_bound i j) (abs_nonneg t)
    have hlow : -(|t| * Bg) ≤ t * g i j := by
      have h := neg_abs_le (t * g i j)
      linarith
    rw [hB]
    linarith
  change 0 ≤ c i j + t * g i j + B
  linarith

/-! ## The scaled distance-slack specialization -/

/-- **Frozen-core bound for the actual supported pressure, deterministic form.**

For points `X`, `Y` of a pseudometric space, a one-Lipschitz potential `φ`, a
scaled distance-slack base cost `k * distanceSlackEdgeCost X Y φ` and any physical
probe matrix with `|probe i j| ≤ Bprobe`, every optimal fractional assignment
`P` of the tilted problem satisfies

`Γ_n / n ≤ V_n(t) / n + B`,

where `Γ_n = ∑ i j, P i j * maskedFrozenCost Q d i j` is the frozen core cost and
`V_n(t) = perturbedAssignmentValue (k * slack) probe t` is the unnormalized
empirical pressure.  This is a deterministic statement for every realization of
an optimal fractional assignment. -/
theorem empiricalFrozenCore_div_le_pressure_add
    {M : Type*} [PseudoMetricSpace M]
    (X Y : Fin n → M) (φ : M → ℝ) (hφ : LipschitzWith 1 φ)
    (probe : Matrix (Fin n) (Fin n) ℝ) {Bprobe k t B : ℝ}
    (hn : 0 < n) (hk : 0 ≤ k)
    (hprobe : ∀ i j, |probe i j| ≤ Bprobe) (hB : B = |t| * Bprobe)
    {Q : Set (Fin n × Fin n)} {d : Matrix (Fin n) (Fin n) ℝ}
    (hd_nonneg : ∀ i j, 0 ≤ d i j)
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : OptimalFractionalAssignment
      (perturbedEdgeCost (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) probe t) P)
    (hd_bound : ∀ i j, (i, j) ∈ Q →
      d i j ≤ perturbedEdgeCost
        (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) probe t i j + B) :
    fractionalAssignmentCost (maskedFrozenCost Q d) P / (n : ℝ) ≤
      perturbedAssignmentValue
        (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j) probe t / (n : ℝ) + B := by
  refine maskedFrozenCost_div_le_perturbedAssignmentValue_div_add_of_nonneg hn
    hd_nonneg ?_ hprobe hB hP hd_bound
  intro i j
  exact mul_nonneg hk (distanceSlackEdgeCost_nonneg X Y φ hφ i j)

/-- The physical probe specialization: the probe matrix is `f (X i, Y j)` for a
bounded continuous probe `f`, and `B = |t| * ‖f‖∞`. -/
theorem empiricalFrozenCore_div_le_probePressure_add
    {M : Type*} [PseudoMetricSpace M]
    (X Y : Fin n → M) (φ : M → ℝ) (hφ : LipschitzWith 1 φ)
    (f : BoundedContinuousFunction (M × M) ℝ) {k t B : ℝ}
    (hn : 0 < n) (hk : 0 ≤ k)
    (hB : B = |t| * (‖f‖₊ : ℝ))
    {Q : Set (Fin n × Fin n)} {d : Matrix (Fin n) (Fin n) ℝ}
    (hd_nonneg : ∀ i j, 0 ≤ d i j)
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : OptimalFractionalAssignment
      (perturbedEdgeCost (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j)
        (fun i j ↦ f (X i, Y j)) t) P)
    (hd_bound : ∀ i j, (i, j) ∈ Q →
      d i j ≤ perturbedEdgeCost
        (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j)
        (fun i j ↦ f (X i, Y j)) t i j + B) :
    fractionalAssignmentCost (maskedFrozenCost Q d) P / (n : ℝ) ≤
      perturbedAssignmentValue
        (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j)
        (fun i j ↦ f (X i, Y j)) t / (n : ℝ) + B := by
  refine empiricalFrozenCore_div_le_pressure_add X Y φ hφ
    (fun i j ↦ f (X i, Y j)) hn hk ?_ hB hd_nonneg hP hd_bound
  intro i j
  simpa only [coe_nnnorm, Real.norm_eq_abs] using f.norm_coe_le_norm (X i, Y j)

end OTSelector

/-! ## Interface with the finite-domination and probability layers -/

namespace OTSelector.PointProcess

/-- A pointwise almost-sure bound `Γ n ω ≤ V n ω + B` implies the
finite-domination inequality `∀ ε > 0, ∀ᶠ n, ∀ᵐ ω, Γ n ω ≤ V n ω + B + ε`. -/
theorem finiteDominationInequality_of_ae_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Γ Vn : ℕ → Ω → ℝ} {B : ℝ}
    (h : ∀ n, ∀ᵐ ω ∂μ, Γ n ω ≤ Vn n ω + B) :
    FiniteDominationInequality μ Γ Vn B := by
  intro ε hε
  filter_upwards with n
  filter_upwards [h n] with ω hω
  linarith

/-- **From optimal fractional assignments to the finite-domination interface.**

For every sample size `n`, if almost surely `P n ω` is an optimal fractional
assignment of the tilted matrix `c n ω + t g n ω` and the frozen matrix
`E n ω` is pointwise bounded by that tilted matrix plus `B`, then the normalized
frozen costs `Γ n ω = fractionalAssignmentCost (E n ω) (P n ω) / (N n)` and the
normalized perturbed values `V n ω` satisfy `FiniteDominationInequality μ Γ V B`.

No measurability of the optimizer selection is required for this interface: the
optimality and domination assumptions are already almost-sure statements.  The
measurability of `Vn` is required only when passing to the probability lower
bound below. -/
theorem finiteDominationInequality_of_optimalFractional
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n)
    (c g E P : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ) {t B : ℝ}
    (hP : ∀ n, ∀ᵐ ω ∂μ,
      OptimalFractionalAssignment (perturbedEdgeCost (c n ω) (g n ω) t) (P n ω))
    (hE : ∀ n, ∀ᵐ ω ∂μ, ∀ i j,
      E n ω i j ≤ perturbedEdgeCost (c n ω) (g n ω) t i j + B) :
    FiniteDominationInequality μ
      (fun n ω ↦ fractionalAssignmentCost (E n ω) (P n ω) / (N n : ℝ))
      (fun n ω ↦ perturbedAssignmentValue (c n ω) (g n ω) t / (N n : ℝ)) B := by
  refine finiteDominationInequality_of_ae_bound ?_
  intro n
  filter_upwards [hP n, hE n] with ω hPω hEω
  exact fractionalAssignmentCost_div_le_perturbedAssignmentValue_div_add (hN n) hPω hEω

/-- The pointwise finite-domination bound and the Campbell lower comparison give
the almost-sure asymptotic lower comparison for the normalized pressure. -/
theorem empiricalPressureLowerComparison_of_ae_finiteDomination
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {Γ Vn : ℕ → Ω → ℝ} {Pw B : ℝ}
    (hΓ : ∀ n, ∀ᵐ ω ∂μ, Γ n ω ≤ Vn n ω + B)
    (hcamp : CampbellLowerComparison μ Γ Pw B) :
    EmpiricalPressureLowerComparison μ Vn Pw :=
  empiricalPressureLowerComparison_of_finiteDomination
    (finiteDominationInequality_of_ae_bound hΓ) hcamp

/-- The pointwise finite-domination bound, the Campbell lower comparison, and
measurability of the normalized pressures give the paper's probability lower
bound. -/
theorem empiricalPressureProbabilityLower_of_ae_finiteDomination
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Γ Vn : ℕ → Ω → ℝ} {Pw B : ℝ}
    (hmeas : ∀ n, Measurable (Vn n))
    (hΓ : ∀ n, ∀ᵐ ω ∂μ, Γ n ω ≤ Vn n ω + B)
    (hcamp : CampbellLowerComparison μ Γ Pw B) :
    EmpiricalPressureProbabilityLower μ Vn Pw :=
  empiricalPressureProbabilityLower_of_finiteDomination hmeas
    (finiteDominationInequality_of_ae_bound hΓ) hcamp

/-- **End-to-end finite-domination bridge.**  Optimal fractional assignments
with a pointwise frozen bound and the Campbell lower comparison imply the
paper's probability lower bound, with the normalized pressure as the comparison
process. -/
theorem empiricalPressureProbabilityLower_of_optimalFractional
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {N : ℕ → ℕ} (hN : ∀ n, 0 < N n)
    (c g E P : ∀ n, Ω → Matrix (Fin (N n)) (Fin (N n)) ℝ) {t B Pw : ℝ}
    (hmeas : ∀ n, Measurable
      (fun ω ↦ perturbedAssignmentValue (c n ω) (g n ω) t / (N n : ℝ)))
    (hP : ∀ n, ∀ᵐ ω ∂μ,
      OptimalFractionalAssignment (perturbedEdgeCost (c n ω) (g n ω) t) (P n ω))
    (hE : ∀ n, ∀ᵐ ω ∂μ, ∀ i j,
      E n ω i j ≤ perturbedEdgeCost (c n ω) (g n ω) t i j + B)
    (hcamp : CampbellLowerComparison μ
      (fun n ω ↦ fractionalAssignmentCost (E n ω) (P n ω) / (N n : ℝ)) Pw B) :
    EmpiricalPressureProbabilityLower μ
      (fun n ω ↦ perturbedAssignmentValue (c n ω) (g n ω) t / (N n : ℝ)) Pw :=
  empiricalPressureProbabilityLower_of_finiteDomination hmeas
    (finiteDominationInequality_of_optimalFractional hN c g E P hP hE) hcamp

end OTSelector.PointProcess
