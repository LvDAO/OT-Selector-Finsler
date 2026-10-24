import OTSelector.Reconstruction.FinslerOriginalFiniteReferenceValue

/-!
# Finite-reference model pressure convergence

The finite-reference value comparison controls one-sided signed pressure
aggregates. This file turns it into an actual two-sided pressure convergence
statement for a finite reference family whose cellwise model pressures
approximate the original cell pressure-readout integrals.

We introduce the original pressure-readout integral
`originalPressureReadout μ p H` and the aggregated finite-reference model
pressure `finiteReferenceAggregatedPressure cellPressure`, then prove:

* cellwise absolute errors inside a per-cell budget `tolerance/(N+1)`
  aggregate to an absolute aggregate error below `tolerance` (this uses the
  strict `N/(N+1)` assembly budget in both directions, the negative direction
  being applied to the negated density);
* exact cellwise original readouts aggregate exactly to the original
  pressure-readout integral;
* for every positive accuracy `ε` and cap, an internally chosen density
  tolerance `δ < cap` produces, for every admissible model and root
  oscillation tolerance, a positive finite tolerance budget not exceeding `ε`
  (the density-accuracy slack), so that any finite-reference model with
  cellwise signed pressure errors inside the budget has its aggregated model
  pressure within `ε` of the original pressure-readout integral;
* the same conclusion for arbitrary real mass, pressure and density constants,
  with the per-cell budget taken as the smaller of `ε` and the
  density-accuracy slack.

All results hold for every finite cell count, including the empty family.
-/

open Set Function MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section

namespace OTSelector.Reconstruction

/-- The original pressure-readout integral over the covered target set. -/
def originalPressureReadout {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (p : Z → ℝ) (H : Set Z) : ℝ :=
  ∫ z in H, p z ∂μ

/-- The aggregated finite-reference model pressure: the sum of the cellwise
model pressures of the finite reference family. -/
def finiteReferenceAggregatedPressure {N : ℕ} (cellPressure : Fin N → ℝ) : ℝ :=
  ∑ i, cellPressure i

/-- Cellwise model pressures equal to the exact original cell readouts
aggregate exactly to the original pressure-readout integral. -/
theorem finiteReferenceAggregatedPressure_cellIntegral
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) (p : Z → ℝ) (hp : IntegrableOn p H μ) :
    finiteReferenceAggregatedPressure (fun i ↦ ∫ z in H ∩ C i, p z ∂μ) =
      originalPressureReadout μ p H := by
  rw [finiteReferenceAggregatedPressure, originalPressureReadout]
  exact sum_finite_reference_integral_eq C hC hdisjoint hH hcover μ p hp

/-- Cellwise absolute signed pressure errors inside the prescribed per-cell
budget aggregate to an absolute error of the aggregated finite-reference model
pressure below the whole budget. -/
theorem abs_finiteReferenceAggregatedPressure_sub_originalPressureReadout_lt
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) [IsFiniteMeasure μ] (p : Z → ℝ) (hp : IntegrableOn p H μ)
    (cellPressure : Fin N → ℝ) {tolerance : ℝ} (htolerance : 0 < tolerance)
    (hcell : ∀ i, |cellPressure i - (∫ z in H ∩ C i, p z ∂μ)| <
      tolerance / ((N : ℝ) + 1)) :
    |finiteReferenceAggregatedPressure cellPressure - originalPressureReadout μ p H| <
      tolerance := by
  have hupper : finiteReferenceAggregatedPressure cellPressure <
      originalPressureReadout μ p H + tolerance := by
    rw [finiteReferenceAggregatedPressure, originalPressureReadout]
    exact sum_finite_reference_energy_lt_integral_add C hC hdisjoint hH hcover μ p hp
      cellPressure htolerance (fun i ↦ by linarith [(abs_lt.mp (hcell i)).2])
  have hlower : originalPressureReadout μ p H - tolerance <
      finiteReferenceAggregatedPressure cellPressure := by
    have hneg : (∑ i, -cellPressure i) <
        (∫ z in H, -p z ∂μ) + tolerance := by
      apply sum_finite_reference_energy_lt_integral_add C hC hdisjoint hH hcover μ
        (fun z ↦ -p z) hp.neg (fun i ↦ -cellPressure i) htolerance
      intro i
      have h := abs_lt.mp (hcell i)
      rw [integral_neg]
      linarith [h.1]
    rw [finiteReferenceAggregatedPressure, originalPressureReadout]
    simp only [Finset.sum_neg_distrib, integral_neg] at hneg
    linarith
  rw [finiteReferenceAggregatedPressure, originalPressureReadout] at hupper hlower ⊢
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Actual finite-reference pressure convergence. For a finite measure, an
integrable original density on a measurable target covered by a finite disjoint
measurable reference family, arbitrary real density constant and nonnegative
original mass and pressure, every positive accuracy and cap yield an internally
chosen density tolerance `δ` below the cap such that, for every model and root
oscillation tolerance bounded by `δ`, the density-accuracy slack
`P + ε - V` is a positive finite tolerance budget not exceeding `ε`. Any
finite-reference model whose cellwise signed pressures are within
`budget/(N+1)` of the original cell pressure readouts then has its aggregated
model pressure within `ε` of the original pressure-readout integral. -/
theorem exists_finite_reference_pressure_convergence
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) [IsFiniteMeasure μ] (p : Z → ℝ) (hp : IntegrableOn p H μ)
    (mass C₀ : ℝ) (hmass : 0 ≤ mass) (hC₀ : 0 ≤ C₀)
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (hpressure : 0 ≤ originalPressureReadout μ p H) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < cap ∧
      ∀ modelTolerance oscillation : ℝ,
        0 ≤ modelTolerance → modelTolerance ≤ δ →
        0 ≤ oscillation → oscillation ≤ δ →
        let budget := originalPressureReadout μ p H + ε -
          finiteReferenceSignedPressureValue (originalPressureReadout μ p H)
            mass C₀ δ modelTolerance oscillation
        0 < budget ∧ budget ≤ ε ∧
          ∀ cellPressure : Fin N → ℝ,
            (∀ i, |cellPressure i - (∫ z in H ∩ C i, p z ∂μ)| <
              budget / ((N : ℝ) + 1)) →
            |finiteReferenceAggregatedPressure cellPressure -
              originalPressureReadout μ p H| < ε := by
  obtain ⟨δ, hδ0, hδ1, hδcap, hvalue⟩ :=
    exists_finiteReferenceSignedPressureValue_lt
      (originalPressureReadout μ p H) mass C₀ hε hcap
  refine ⟨δ, hδ0, hδ1, hδcap, fun modelTolerance oscillation hm0 hmδ ho0 hoδ ↦ ?_⟩
  have hVlt := hvalue modelTolerance oscillation hm0 hmδ ho0 hoδ
  have hVge := le_finiteReferenceSignedPressureValue_of_nonneg hpressure hmass hC₀
    hδ0.le hδ1 hm0 ho0
  have hbudget_pos : 0 < originalPressureReadout μ p H + ε -
      finiteReferenceSignedPressureValue (originalPressureReadout μ p H)
        mass C₀ δ modelTolerance oscillation := by
    linarith
  have hbudget_le : originalPressureReadout μ p H + ε -
      finiteReferenceSignedPressureValue (originalPressureReadout μ p H)
        mass C₀ δ modelTolerance oscillation ≤ ε := by
    linarith
  exact ⟨hbudget_pos, hbudget_le, fun cellPressure hcell ↦
    lt_of_lt_of_le
      (abs_finiteReferenceAggregatedPressure_sub_originalPressureReadout_lt
        C hC hdisjoint hH hcover μ p hp cellPressure hbudget_pos hcell) hbudget_le⟩

/-- Finite-reference pressure convergence for arbitrary real pressure, mass and
density constants. Without sign hypotheses the per-cell tolerance budget is the
smaller of the accuracy `ε` and the density-accuracy slack, which is still
positive and finite. -/
theorem exists_finite_reference_pressure_convergence_of_arbitrary_constants
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) [IsFiniteMeasure μ] (p : Z → ℝ) (hp : IntegrableOn p H μ)
    (mass C₀ : ℝ) {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < cap ∧
      ∀ modelTolerance oscillation : ℝ,
        0 ≤ modelTolerance → modelTolerance ≤ δ →
        0 ≤ oscillation → oscillation ≤ δ →
        let budget := min ε (originalPressureReadout μ p H + ε -
          finiteReferenceSignedPressureValue (originalPressureReadout μ p H)
            mass C₀ δ modelTolerance oscillation)
        0 < budget ∧ budget ≤ ε ∧
          ∀ cellPressure : Fin N → ℝ,
            (∀ i, |cellPressure i - (∫ z in H ∩ C i, p z ∂μ)| <
              budget / ((N : ℝ) + 1)) →
            |finiteReferenceAggregatedPressure cellPressure -
              originalPressureReadout μ p H| < ε := by
  obtain ⟨δ, hδ0, hδ1, hδcap, hvalue⟩ :=
    exists_finiteReferenceSignedPressureValue_lt
      (originalPressureReadout μ p H) mass C₀ hε hcap
  refine ⟨δ, hδ0, hδ1, hδcap, fun modelTolerance oscillation hm0 hmδ ho0 hoδ ↦ ?_⟩
  have hVlt := hvalue modelTolerance oscillation hm0 hmδ ho0 hoδ
  have hslack : 0 < originalPressureReadout μ p H + ε -
      finiteReferenceSignedPressureValue (originalPressureReadout μ p H)
        mass C₀ δ modelTolerance oscillation := by
    linarith
  have hbudget_pos : 0 < min ε (originalPressureReadout μ p H + ε -
      finiteReferenceSignedPressureValue (originalPressureReadout μ p H)
        mass C₀ δ modelTolerance oscillation) :=
    lt_min hε hslack
  have hbudget_le : min ε (originalPressureReadout μ p H + ε -
      finiteReferenceSignedPressureValue (originalPressureReadout μ p H)
        mass C₀ δ modelTolerance oscillation) ≤ ε :=
    min_le_left _ _
  exact ⟨hbudget_pos, hbudget_le, fun cellPressure hcell ↦
    lt_of_lt_of_le
      (abs_finiteReferenceAggregatedPressure_sub_originalPressureReadout_lt
        C hC hdisjoint hH hcover μ p hp cellPressure hbudget_pos hcell) hbudget_le⟩

/-- Filter form of the finite-reference pressure convergence: a sequence of
finite-reference models whose cellwise signed pressure errors are bounded by
`1/(n+1)` per cell has aggregated model pressures tending to the original
pressure-readout integral. -/
theorem tendsto_finiteReferenceAggregatedPressure
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) [IsFiniteMeasure μ] (p : Z → ℝ) (hp : IntegrableOn p H μ)
    (cellPressure : ℕ → Fin N → ℝ)
    (hcell : ∀ n i, |cellPressure n i - (∫ z in H ∩ C i, p z ∂μ)| <
      (1 / ((n : ℝ) + 1)) / ((N : ℝ) + 1)) :
    Tendsto (fun n ↦ finiteReferenceAggregatedPressure (cellPressure n)) atTop
      (𝓝 (originalPressureReadout μ p H)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  rw [div_lt_iff₀ hε] at hn
  refine ⟨n, fun m hm ↦ ?_⟩
  rw [Real.dist_eq]
  have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hbound := abs_finiteReferenceAggregatedPressure_sub_originalPressureReadout_lt
    C hC hdisjoint hH hcover μ p hp (cellPressure m)
    (div_pos (one_pos : (0 : ℝ) < 1) hmpos) (hcell m)
  refine lt_of_lt_of_le hbound ?_
  rw [div_le_iff₀ hmpos]
  have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hstep : (n : ℝ) * ε ≤ ((m : ℝ) + 1) * ε := by
    apply mul_le_mul_of_nonneg_right _ hε.le
    linarith
  nlinarith [hn, hstep]

end OTSelector.Reconstruction
