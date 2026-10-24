import OTSelector.Reconstruction.FinslerOriginalFrozenTrafficBridge
import OTSelector.Reconstruction.FiniteDominationCore

/-!
# Off-bad domination of the finite-domination frozen core cost

The last bridge of FinslerOriginalFrozenTrafficBridge.lean asks for an off-bad
pointwise domination of the frozen-core cost by the whole-path traffic plus a
constant.  This file proves the strongest true form of that bridge for the
finite-domination frozen core:

* the frozen-core matrix is a bounded kernel on the good event: the finite
  weighted kinetic class gives a per-edge bound E i j <= K there (K is the
  kinetic-class constant at the bounded amplitude of the good event);
* consequently the frozen-core cost of any fractional assignment is bounded by
  K times the plan mass carried by the tile, i.e. the frozen core enters as a
  per-tile contribution multiplied by the empirical whole-path count;
* for the whole plan the normalized frozen-core cost is at most K, because the
  plan mass of the full edge set is the number of source rows;
* in particular the off-bad domination holds with traffic coefficient zero:
  |frozenCost| <= K + 0 * traffic off the bad event.  Hence no comparison of
  the frozen core with the traffic energy is needed for the finite-domination
  frozen core; the traffic domination is only required if the per-edge frozen
  cost is unbounded, which is exactly what the phase-bad event encodes.
-/
open Set Filter MeasureTheory
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

namespace OTSelector.Reconstruction

variable {n : ℕ}

/-- The empirical whole-path plan mass carried by a set of edges: the sum of the
fractional assignment weights on the tile.  This is the per-tile count readout of
the plan, i.e. the whole-path traffic restricted to the tile. -/
noncomputable def tilePlanMass (Q : Set (Fin n × Fin n))
    (P : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, Q.indicator (fun p : Fin n × Fin n => P p.1 p.2) (i, j)

/-- **Per-tile domination: the frozen core enters as a per-tile contribution.**

On a tile Q the frozen matrix is bounded by the kinetic-class constant K, so the
frozen-core cost on the tile is at most K times the plan mass on the tile.  Only
nonnegativity of the plan enters; the frozen entries need not be nonnegative
outside Q. -/
theorem maskedFrozenCost_le_mul_tilePlanMass
    {Q : Set (Fin n × Fin n)} {d P : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (hP : P ∈ doublyStochastic ℝ (Fin n))
    (hd : ∀ i j, (i, j) ∈ Q → d i j ≤ K) :
    fractionalAssignmentCost (maskedFrozenCost Q d) P ≤ K * tilePlanMass Q P := by
  have hterm : ∀ i j, P i j * maskedFrozenCost Q d i j ≤
      K * (Q.indicator (fun p : Fin n × Fin n => P p.1 p.2) (i, j)) := by
    intro i j
    have hPij : 0 ≤ P i j := nonneg_of_mem_doublyStochastic hP
    by_cases hQ : (i, j) ∈ Q
    · rw [maskedFrozenCost_apply_of_mem hQ, Set.indicator_of_mem hQ]
      have hle := mul_le_mul_of_nonneg_left (hd i j hQ) hPij
      linarith
    · rw [maskedFrozenCost_apply_of_not_mem hQ, Set.indicator_of_notMem hQ,
        mul_zero, mul_zero]
  unfold fractionalAssignmentCost tilePlanMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => hterm i j

/-- **The normalized frozen-core cost is bounded by the kinetic-class constant.**

For a fractional assignment (unit row sums) and a frozen matrix bounded
entrywise by K, the normalized frozen-core cost is at most K.  This is the global
form of the per-tile domination, with the full plan mass equal to the number of
source rows. -/
theorem fractionalAssignmentCost_div_le_of_entryBound
    {E P : Matrix (Fin n) (Fin n) ℝ} {K : ℝ} (hn : 0 < n)
    (hP : P ∈ doublyStochastic ℝ (Fin n))
    (hE : ∀ i j, E i j ≤ K) :
    fractionalAssignmentCost E P / (n : ℝ) ≤ K := by
  have hstep : fractionalAssignmentCost E P ≤ ∑ i, K * (∑ j, P i j) := by
    unfold fractionalAssignmentCost
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hPij : 0 ≤ P i j := nonneg_of_mem_doublyStochastic hP
    have hle := mul_le_mul_of_nonneg_left (hE i j) hPij
    linarith
  have hmain : fractionalAssignmentCost E P ≤ K * (n : ℝ) := by
    calc fractionalAssignmentCost E P ≤ ∑ i, K * (∑ j, P i j) := hstep
      _ = ∑ _i : Fin n, K * 1 :=
          Finset.sum_congr rfl fun i _ => by
            rw [sum_row_of_mem_doublyStochastic hP i]
      _ = K * (n : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [div_le_iff₀ hn']
  exact hmain

/-- **Absolute form on nonnegative frozen matrices.**

The frozen core matrices are entrywise nonnegative, so the normalized frozen-core
cost is nonnegative and the entrywise kinetic-class bound gives an absolute
bound. -/
theorem abs_fractionalAssignmentCost_div_le_of_entryBound
    {E P : Matrix (Fin n) (Fin n) ℝ} {K : ℝ} (hn : 0 < n)
    (hP : P ∈ doublyStochastic ℝ (Fin n))
    (hE : ∀ i j, E i j ≤ K) (_hK : 0 ≤ K) (hE0 : ∀ i j, 0 ≤ E i j) :
    |fractionalAssignmentCost E P / (n : ℝ)| ≤ max K 0 := by
  have hcost : 0 ≤ fractionalAssignmentCost E P :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (nonneg_of_mem_doublyStochastic hP) (hE0 i j)
  have hnonneg : 0 ≤ fractionalAssignmentCost E P / (n : ℝ) :=
    div_nonneg hcost (Nat.cast_nonneg n)
  rw [abs_of_nonneg hnonneg]
  exact (fractionalAssignmentCost_div_le_of_entryBound hn hP hE).trans (le_max_left _ _)

/-- **Off-bad domination of any bounded frozen-core cost, with traffic
coefficient zero.**

This is the exact bridge hypothesis of FinslerOriginalFrozenTrafficBridge.lean,
specialized to the case in which the frozen-core cost is uniformly bounded on the
good event by the kinetic-class constant.  No comparison with the traffic energy
is needed: the traffic term enters with coefficient zero. -/
theorem offBad_domination_of_entryBound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {traffic : Ω → ℝ} {Bad : Set Ω} {T : Ω → ℝ} {K : ℝ}
    (hbound : ∀ s, s ∉ Bad → |T s| ≤ K) :
    ∀ᵐ s ∂μ, s ∉ Bad → |T s| ≤ K + 0 * traffic s := by
  filter_upwards with s hs
  simpa only [zero_mul, add_zero] using hbound s hs

/-- **Integrability of a uniformly bounded frozen-core cost.**

A frozen-core cost that is bounded by the kinetic-class constant everywhere is
integrable on any finite measure: the traffic and the phase-bad event are not
involved at all.  Combined with offBad_domination_of_entryBound this closes the
off-bad bridge for the finite-domination frozen core. -/
theorem integrable_of_entryBound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {T : Ω → ℝ} (hT : Measurable T) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ s, |T s| ≤ K) :
    Integrable T μ := by
  refine (integrable_const K).mono hT.aestronglyMeasurable ?_
  filter_upwards with s
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hK]
  exact hbound s

/-- **The bridge of FinslerOriginalFrozenTrafficBridge is closed off the bad
event for a bounded frozen-core cost.**

Composing the off-bad domination with traffic coefficient zero with the
bad-event integrability bridge of FinslerOriginalFrozenTrafficBridge.lean: a
frozen-core cost that is bounded by K off the bad event, bounded on it, and
measurable is integrable.  No integrability of the traffic and no comparison of
the frozen core with the traffic energy are needed. -/
theorem integrable_of_entryBound_of_onBadBound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {traffic : Ω → ℝ} {Bad : Set Ω} {CB CL B0 : ℝ}
    (hdata : CommonScaleWholePathPressureData μ traffic Bad CB CL B0)
    (hBad : MeasurableSet Bad) (htraf : Measurable traffic)
    {T : Ω → ℝ} (hT : Measurable T) {K Ab : ℝ}
    (hgood : ∀ s, s ∉ Bad → |T s| ≤ K)
    (hbad : ∀ s, s ∈ Bad → |T s| ≤ Ab) :
    Integrable T μ :=
  integrable_of_dominated_on_compl_and_bounded_on (A := K) (C := 0) (Ab := Ab)
    hdata hBad htraf hT
    (Eventually.of_forall fun s hs => by
      simpa only [zero_mul, add_zero] using hgood s hs)
    (Eventually.of_forall hbad)

end OTSelector.Reconstruction
