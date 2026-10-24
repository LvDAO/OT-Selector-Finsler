import OTSelector.Reconstruction.OriginalReferenceDensityAccuracy
import OTSelector.MeasureTheory.Integral.FiniteDisjointBudget
import Mathlib.Algebra.BigOperators.Field

/-!
# Finite-reference signed pressure value comparison

The finite-reference approximation of the original Finsler pressure perturbs the
original density on a finite disjoint reference family. Two promoted packets
supply the ingredients.

* `OriginalReferenceDensityAccuracy`: for pressure `P`, mass `mass` and
  lower-bound constant `C` the closed-form signed pressure value
  `(P + (C + modelTolerance + oscillation) * mass) / (1 - δ) - C * mass / (1 + δ)`
  is continuous at zero density tolerance, and for every positive accuracy
  `ε` and cap there is an internally chosen density tolerance `δ < cap` such
  that the value at the model and root oscillation tolerances `δ, δ` stays
  below `P + ε`; only nonnegative mass is used in that monotone form.
* `OriginalFiniteReferenceAssemblyBudget`: exact aggregation of cell integrals
  over a finite disjoint family covering the target, and the strict
  `N/(N+1)` budget turning cellwise signed pressure bounds into a strict bound
  below the original integral plus the full tolerance, including the empty
  family.

This file composes them. A single internally chosen density tolerance
simultaneously controls

* the closed-form finite-reference signed pressure value for every model and
  root oscillation tolerance bounded by it, and
* the aggregation of cellwise signed pressure energies, each within
  `ε/(N+1)` of the original cell integral, into a strict bound below the
  original pressure integral plus `ε`.

It also shows that the closed-form value is additive over the reference cells,
so the aggregated cellwise values with the exact original cell pressure
integrals are strictly below the original pressure integral plus `ε`. The
signed constants `P`, `mass` and `C` are arbitrary real numbers; the
negative-mass case is handled by continuity at zero oscillation tolerance
because the value is then antitone in the tolerances.
-/

open Set Function MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section

namespace OTSelector.Reconstruction

/-- The closed-form finite-reference signed pressure value after the density
tolerance `δ` and the model and root oscillation tolerances have been applied
to the signed original pressure `P`, the original mass `mass` and the density
lower-bound constant `C`. -/
def finiteReferenceSignedPressureValue
    (P mass C δ modelTolerance oscillation : ℝ) : ℝ :=
  (P + (C + modelTolerance + oscillation) * mass) / (1 - δ) - C * mass / (1 + δ)

/-- The finite-reference signed pressure value is monotone in the model and
root oscillation tolerances when the original mass is nonnegative. -/
theorem finiteReferenceSignedPressureValue_le_symmetric
    {P mass C δ modelTolerance oscillation : ℝ} (hmass : 0 ≤ mass) (hδ : δ < 1)
    (hmodel : modelTolerance ≤ δ) (hosc : oscillation ≤ δ) :
    finiteReferenceSignedPressureValue P mass C δ modelTolerance oscillation ≤
      finiteReferenceSignedPressureValue P mass C δ δ δ := by
  have hden : (0 : ℝ) < 1 - δ := by linarith
  have hcoef : C + modelTolerance + oscillation ≤ C + δ + δ := by linarith
  have hnum : P + (C + modelTolerance + oscillation) * mass ≤ P + (C + δ + δ) * mass := by
    have hmul := mul_le_mul_of_nonneg_right hcoef hmass
    linarith
  simp only [finiteReferenceSignedPressureValue]
  exact sub_le_sub_right (div_le_div_of_nonneg_right hnum hden.le) _

/-- For nonpositive mass the finite-reference signed pressure value is
antitone in the model and root oscillation tolerances, so its maximum on
nonnegative tolerances is attained at zero tolerances. -/
theorem finiteReferenceSignedPressureValue_le_zero_of_nonpos_mass
    {P mass C δ modelTolerance oscillation : ℝ} (hmass : mass ≤ 0) (hδ : δ < 1)
    (hmodel : 0 ≤ modelTolerance) (hosc : 0 ≤ oscillation) :
    finiteReferenceSignedPressureValue P mass C δ modelTolerance oscillation ≤
      finiteReferenceSignedPressureValue P mass C δ 0 0 := by
  have hden : (0 : ℝ) < 1 - δ := by linarith
  have hcoef : C ≤ C + modelTolerance + oscillation := by linarith
  have hprod : (C + modelTolerance + oscillation) * mass ≤ C * mass :=
    mul_le_mul_of_nonpos_right hcoef hmass
  have hnum : P + (C + modelTolerance + oscillation) * mass ≤ P + C * mass := by
    linarith
  simp only [finiteReferenceSignedPressureValue, add_zero]
  exact sub_le_sub_right (div_le_div_of_nonneg_right hnum hden.le) _

/-- The zero-tolerance finite-reference signed pressure value is continuous at
zero density tolerance for arbitrary real pressure, mass and lower-bound
constant. -/
theorem continuousAt_finiteReferenceSignedPressureValue_zero_tolerances
    (P mass C : ℝ) :
    ContinuousAt (fun δ : ℝ ↦ finiteReferenceSignedPressureValue P mass C δ 0 0) 0 := by
  simp only [finiteReferenceSignedPressureValue, add_zero]
  apply ContinuousAt.sub
  · exact continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
  · exact continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num)

/-- An internally chosen density tolerance below the prescribed cap keeps the
finite-reference signed pressure value strictly below `P + ε` for every model
and root oscillation tolerance bounded by it. The constants `P`, `mass` and
`C` are arbitrary real numbers. -/
theorem exists_finiteReferenceSignedPressureValue_lt
    (P mass C : ℝ) {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < cap ∧
      ∀ modelTolerance oscillation : ℝ,
        0 ≤ modelTolerance → modelTolerance ≤ δ →
        0 ≤ oscillation → oscillation ≤ δ →
        finiteReferenceSignedPressureValue P mass C δ modelTolerance oscillation < P + ε := by
  rcases le_or_gt 0 mass with hmass | hneg
  · obtain ⟨δ, hδ0, hδ1, hδcap, hδ⟩ :=
      exists_reference_density_pressure_accuracy P mass C hmass hε hcap
    refine ⟨δ, hδ0, hδ1, hδcap, fun modelTolerance oscillation hm0 hmδ ho0 hoδ ↦ ?_⟩
    have hsymmetric :
        finiteReferenceSignedPressureValue P mass C δ δ δ < P + ε := by
      simpa only [finiteReferenceSignedPressureValue] using
        hδ δ δ hδ0.le (le_refl δ) hδ0.le (le_refl δ)
    exact lt_of_le_of_lt
      (finiteReferenceSignedPressureValue_le_symmetric hmass hδ1 hmδ hoδ) hsymmetric
  · have hzeroValue : finiteReferenceSignedPressureValue P mass C 0 0 0 = P := by
      simp only [finiteReferenceSignedPressureValue, add_zero, sub_zero, div_one]
      ring
    have hevent : ∀ᶠ δ : ℝ in 𝓝 0,
        finiteReferenceSignedPressureValue P mass C δ 0 0 < P + ε :=
      (continuousAt_finiteReferenceSignedPressureValue_zero_tolerances P mass C).eventually_lt
        continuousAt_const (by rw [hzeroValue]; simpa using hε)
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hevent
    let δ : ℝ := min (min r cap) 1 / 2
    have hmin : 0 < min (min r cap) 1 := lt_min (lt_min hr hcap) zero_lt_one
    have hδ0 : 0 < δ := half_pos hmin
    have hδr : δ < r := by
      have h1 := min_le_left r cap
      have h2 := min_le_left (min r cap) 1
      dsimp only [δ]
      linarith
    have hδcap : δ < cap := by
      have h1 := min_le_right r cap
      have h2 := min_le_left (min r cap) 1
      dsimp only [δ]
      linarith
    have hδ1 : δ < 1 := by
      have h1 := min_le_right (min r cap) 1
      dsimp only [δ]
      linarith
    have hzero : finiteReferenceSignedPressureValue P mass C δ 0 0 < P + ε :=
      hball (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ0] using hδr)
    refine ⟨δ, hδ0, hδ1, hδcap, fun modelTolerance oscillation hm0 _ ho0 _ ↦ ?_⟩
    exact lt_of_le_of_lt
      (finiteReferenceSignedPressureValue_le_zero_of_nonpos_mass hneg.le hδ1 hm0 ho0) hzero

/-- Cellwise signed pressure energies within the prescribed `ε/(N+1)` of the
original cell integrals aggregate strictly below the original pressure integral
plus the full tolerance `ε`, for every finite cell count including `N = 0`. -/
theorem finite_reference_cellwise_energy_aggregate_lt
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) [IsFiniteMeasure μ] (p : Z → ℝ) (hp : IntegrableOn p H μ)
    (energy : Fin N → ℝ) {ε : ℝ} (hε : 0 < ε)
    (henergy : ∀ i, energy i ≤ (∫ z in H ∩ C i, p z ∂μ) + ε / ((N : ℝ) + 1)) :
    ∑ i, energy i < (∫ z in H, p z ∂μ) + ε :=
  sum_finite_reference_energy_lt_integral_add
    C hC hdisjoint hH hcover μ p hp energy hε henergy

/-- Finite-reference signed pressure value comparison. For a finite measure,
an integrable density on a measurable set covered by a finite disjoint family of
measurable reference cells, arbitrary real signed pressure, mass and
lower-bound constants, every positive accuracy and cap, one internally chosen
density tolerance `δ` below the cap simultaneously

* keeps the finite-reference signed pressure value strictly below the signed
  original pressure `P` plus `ε` for all model and root oscillation
  tolerances bounded by `δ`, and
* makes every finite family of cellwise signed pressure energies, each within
  `ε/(N+1)` of the original cell integral, aggregate strictly below the
  original pressure integral plus `ε` (including the empty family). -/
theorem exists_finite_reference_pressure_value_comparison
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) [IsFiniteMeasure μ] (p : Z → ℝ) (hp : IntegrableOn p H μ)
    (P mass C₀ : ℝ) {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < cap ∧
      (∀ modelTolerance oscillation : ℝ,
        0 ≤ modelTolerance → modelTolerance ≤ δ →
        0 ≤ oscillation → oscillation ≤ δ →
        finiteReferenceSignedPressureValue P mass C₀ δ modelTolerance oscillation < P + ε) ∧
      (∀ energy : Fin N → ℝ,
        (∀ i, energy i ≤ (∫ z in H ∩ C i, p z ∂μ) + ε / ((N : ℝ) + 1)) →
        ∑ i, energy i < (∫ z in H, p z ∂μ) + ε) := by
  obtain ⟨δ, hδ0, hδ1, hδcap, hvalue⟩ :=
    exists_finiteReferenceSignedPressureValue_lt P mass C₀ hε hcap
  exact ⟨δ, hδ0, hδ1, hδcap, hvalue, fun energy henergy ↦
    finite_reference_cellwise_energy_aggregate_lt C hC hdisjoint hH hcover μ p hp
      energy hε henergy⟩

/-- The finite-reference signed pressure value is additive over the reference
cells when the signed pressure and mass constants are summed cellwise. -/
theorem sum_finiteReferenceSignedPressureValue_eq
    {N : ℕ} (pressure mass : Fin N → ℝ) (C δ modelTolerance oscillation : ℝ) :
    ∑ i, finiteReferenceSignedPressureValue
        (pressure i) (mass i) C δ modelTolerance oscillation =
      finiteReferenceSignedPressureValue
        (∑ i, pressure i) (∑ i, mass i) C δ modelTolerance oscillation := by
  simp only [finiteReferenceSignedPressureValue, div_eq_mul_inv]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Aggregated finite-reference signed pressure value. For a finite measure and
an integrable original density on a set covered by a finite disjoint reference
family, take the cellwise signed pressure constants to be the exact original
cell pressure integrals and cellwise masses to be arbitrary real constants.
Then there is an internally chosen density tolerance below the cap such that,
for every model and root oscillation tolerance bounded by it, the closed-form
value aggregated over the reference cells is strictly below the original
pressure integral plus the prescribed accuracy. The cellwise values are added
exactly, the cell pressure integrals aggregate to the original integral, and
the total signed value is controlled by the density accuracy selection. -/
theorem exists_finite_reference_pressure_value_lt_integral
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) [IsFiniteMeasure μ] (p : Z → ℝ) (hp : IntegrableOn p H μ)
    (mass : Fin N → ℝ) (C₀ : ℝ) {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < cap ∧
      ∀ modelTolerance oscillation : ℝ,
        0 ≤ modelTolerance → modelTolerance ≤ δ →
        0 ≤ oscillation → oscillation ≤ δ →
        ∑ i, finiteReferenceSignedPressureValue
            (∫ z in H ∩ C i, p z ∂μ) (mass i) C₀ δ modelTolerance oscillation <
          (∫ z in H, p z ∂μ) + ε := by
  obtain ⟨δ, hδ0, hδ1, hδcap, hvalue⟩ :=
    exists_finiteReferenceSignedPressureValue_lt
      (∫ z in H, p z ∂μ) (∑ i, mass i) C₀ hε hcap
  refine ⟨δ, hδ0, hδ1, hδcap, fun modelTolerance oscillation hm0 hmδ ho0 hoδ ↦ ?_⟩
  rw [sum_finiteReferenceSignedPressureValue_eq]
  rw [sum_finite_reference_integral_eq C hC hdisjoint hH hcover μ p hp]
  exact hvalue modelTolerance oscillation hm0 hmδ ho0 hoδ

/-- The same finite-reference value comparison with the signed original pressure
constant instantiated at the original pressure integral. -/
theorem exists_finite_reference_pressure_value_comparison_original
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) [IsFiniteMeasure μ] (p : Z → ℝ) (hp : IntegrableOn p H μ)
    (mass C₀ : ℝ) {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < cap ∧
      (∀ modelTolerance oscillation : ℝ,
        0 ≤ modelTolerance → modelTolerance ≤ δ →
        0 ≤ oscillation → oscillation ≤ δ →
        finiteReferenceSignedPressureValue
          (∫ z in H, p z ∂μ) mass C₀ δ modelTolerance oscillation <
          (∫ z in H, p z ∂μ) + ε) ∧
      (∀ energy : Fin N → ℝ,
        (∀ i, energy i ≤ (∫ z in H ∩ C i, p z ∂μ) + ε / ((N : ℝ) + 1)) →
        ∑ i, energy i < (∫ z in H, p z ∂μ) + ε) :=
  exists_finite_reference_pressure_value_comparison
    C hC hdisjoint hH hcover μ p hp (∫ z in H, p z ∂μ) mass C₀ hε hcap

/-- Under nonnegative original pressure, mass and density lower bound, the
finite-reference signed pressure value is at least the signed original
pressure. -/
theorem le_finiteReferenceSignedPressureValue_of_nonneg
    {P mass C δ modelTolerance oscillation : ℝ} (hP : 0 ≤ P) (hmass : 0 ≤ mass)
    (hC : 0 ≤ C) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hmodel : 0 ≤ modelTolerance) (hosc : 0 ≤ oscillation) :
    P ≤ finiteReferenceSignedPressureValue P mass C δ modelTolerance oscillation := by
  have hden1 : (0 : ℝ) < 1 - δ := by linarith
  have hden2 : (0 : ℝ) < 1 + δ := by linarith
  have hcoef : C ≤ C + modelTolerance + oscillation := by linarith
  have hprod : C * mass ≤ (C + modelTolerance + oscillation) * mass :=
    mul_le_mul_of_nonneg_right hcoef hmass
  have hprod0 : 0 ≤ (C + modelTolerance + oscillation) * mass :=
    mul_nonneg (by linarith) hmass
  have hcell : C * mass / (1 + δ) ≤
      (C + modelTolerance + oscillation) * mass / (1 - δ) := by
    calc C * mass / (1 + δ) ≤
          (C + modelTolerance + oscillation) * mass / (1 + δ) :=
          div_le_div_of_nonneg_right hprod hden2.le
      _ ≤ (C + modelTolerance + oscillation) * mass / (1 - δ) :=
          div_le_div_of_nonneg_left hprod0 hden1 (by linarith)
  have hPle : P ≤ P / (1 - δ) := by
    rw [le_div_iff₀ hden1]
    nlinarith [mul_nonneg hP hδ0]
  have hsplit : (P + (C + modelTolerance + oscillation) * mass) / (1 - δ) =
      P / (1 - δ) + (C + modelTolerance + oscillation) * mass / (1 - δ) := by
    ring
  simp only [finiteReferenceSignedPressureValue]
  rw [hsplit]
  linarith

/-- Density-slack cellwise budget for the finite-reference signed pressure.
When the original pressure, mass and lower bound are nonnegative, the internally
chosen density tolerance yields, for every admissible model and root
oscillation tolerance, a positive slack between the finite-reference signed
pressure value and the accuracy target. Any cellwise signed pressure energies
within that slack divided by `N + 1` of the original cell integrals aggregate
strictly below the original pressure integral plus the accuracy. -/
theorem exists_finite_reference_energy_lt_integral_of_density_slack
    {Z : Type*} [MeasurableSpace Z] {N : ℕ} (C : Fin N → Set Z) {H : Set Z}
    (hC : ∀ i, MeasurableSet (C i)) (hdisjoint : Pairwise (Disjoint on C))
    (hH : MeasurableSet H) (hcover : H ⊆ ⋃ i, C i)
    (μ : Measure Z) [IsFiniteMeasure μ] (p : Z → ℝ) (hp : IntegrableOn p H μ)
    (mass C₀ : ℝ) (hmass : 0 ≤ mass) (hC₀ : 0 ≤ C₀)
    {ε cap : ℝ} (hε : 0 < ε) (hcap : 0 < cap)
    (hpressure : 0 ≤ ∫ z in H, p z ∂μ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < cap ∧
      ∀ modelTolerance oscillation : ℝ,
        0 ≤ modelTolerance → modelTolerance ≤ δ →
        0 ≤ oscillation → oscillation ≤ δ →
        ∀ tolerance : ℝ, 0 < tolerance →
          tolerance ≤ ε - (finiteReferenceSignedPressureValue
            (∫ z in H, p z ∂μ) mass C₀ δ modelTolerance oscillation -
            ∫ z in H, p z ∂μ) →
          ∀ energy : Fin N → ℝ,
            (∀ i, energy i ≤ (∫ z in H ∩ C i, p z ∂μ) + tolerance / ((N : ℝ) + 1)) →
            ∑ i, energy i < (∫ z in H, p z ∂μ) + ε := by
  obtain ⟨δ, hδ0, hδ1, hδcap, hvalue⟩ :=
    exists_finiteReferenceSignedPressureValue_lt
      (∫ z in H, p z ∂μ) mass C₀ hε hcap
  refine ⟨δ, hδ0, hδ1, hδcap, fun modelTolerance oscillation hm0 hmδ ho0 hoδ ↦ ?_⟩
  have hVlt := hvalue modelTolerance oscillation hm0 hmδ ho0 hoδ
  have hVge := le_finiteReferenceSignedPressureValue_of_nonneg hpressure hmass hC₀
    hδ0.le hδ1 hm0 ho0
  intro tolerance htolerance htolerance_le energy henergy
  have haggregate := finite_reference_cellwise_energy_aggregate_lt
    C hC hdisjoint hH hcover μ p hp energy htolerance henergy
  linarith

end OTSelector.Reconstruction
