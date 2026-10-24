import OTSelector.Probability.FiniteClassThinning
import OTSelector.Probability.NormalizedBinMarginal
import OTSelector.Transport.Calibration.FiniteClassPopulation
import OTSelector.Transport.Coupling.FiniteClockMixture

/-!
Conditions: Actual probability populations on a standard-Borel metric carrier, a measurable injective common label-clock parametrization on a full carrier with the displayed calibrated order equivalence, and a measurable nonnegative finite bin flow with the original conditional row/column masses.

Objects: A constructed measurable inverse and a genuine calibrated physical population coupling with exactly the original marginals; dominated bin submeasures keep domination and total mass after reconstruction.

Proof detail: Normalize the actual conditional laws inside disjoint covering clock bins, combine them by the supplied flow, then push the common-label pair law through the measurable inverse on the full carrier. Ordered allowed bins and the geometric order identity give calibration.

References: D. H. Fremlin: 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary; D. H. Fremlin: Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
Relation: A local finite-bin/disintegration reconstruction with explicit geometric inputs. The finite transport polytope is only one ingredient; no arbitrary flow or standalone density statement implies calibrated original marginals.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOriginalBinPopulation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOriginalBinPopulation`; the selected original proof blocks follow. -/
section

/-!
Rebuild a calibrated original physical population coupling directly from its literal conditional clock-bin masses, with exact original marginals.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- An actual measurable class flow reconstructs the original physical
population using the original conditional clocks normalized inside their bins.
All marginal identities and zero-bin fallbacks are discharged. -/
theorem exists_original_calibrated_coupling_of_clockBinFlow
    {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] [StandardBorelSpace M] [Nonempty M]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
    {I J : Type*} [Fintype I] [Fintype J]
    {N : Set M} (hN : MeasurableSet N)
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (hinj : Function.Injective (fun x : N ↦ (a x.val, u x.val)))
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
    (hbalance : μ.map a = ν.map a)
    (S : I → Set ℝ) (T : J → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (Disjoint on S)) (hdT : Pairwise (Disjoint on T))
    (hcoverS : ∀ᵐ z ∂μ.map a, ∀ᵐ s ∂condDistrib u a μ z, s ∈ ⋃ i, S i)
    (hcoverT : ∀ᵐ z ∂μ.map a, ∀ᵐ t ∂condDistrib u a ν z, t ∈ ⋃ j, T j)
    (fallbackS : I → ℝ) (fallbackT : J → ℝ)
    (P : Z → I → J → ℝ) (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hP : ∀ᵐ z ∂μ.map a, ∀ i j, 0 ≤ P z i j)
    (hrow : ∀ᵐ z ∂μ.map a, ∀ i, ∑ j, P z i j = (condDistrib u a μ z).real (S i))
    (hcol : ∀ᵐ z ∂μ.map a, ∀ j, ∑ i, P z i j = (condDistrib u a ν z).real (T j))
    (allowed : I → J → Prop)
    (hzero : ∀ᵐ z ∂μ.map a, ∀ i j, ¬ allowed i j → P z i j = 0)
    (hbins : ∀ i j, allowed i j → ∀ s ∈ S i, ∀ t ∈ T j, s ≤ t) :
    let α := fun i ↦ normalizedActualBinKernel (condDistrib u a μ) (S i) (hS i) (fallbackS i)
    let β := fun j ↦ normalizedActualBinKernel (condDistrib u a ν) (T j) (hT j) (fallbackT j)
    ∃ b : Z × ℝ → M, Measurable b ∧
      Vlasov.IsCoupling ((sameLabelPopulationCoupling (μ.map a) P α β).map (Prod.map b b)) μ ν ∧
      (∀ᵐ p ∂(sameLabelPopulationCoupling (μ.map a) P α β).map (Prod.map b b),
        u p.2 - u p.1 = dist p.1 p.2) ∧
      ∀ ξ : Measure ((Z × ℝ) × (Z × ℝ)), ξ ≤ sameLabelPopulationCoupling (μ.map a) P α β →
        ξ.map (Prod.map b b) ≤ (sameLabelPopulationCoupling (μ.map a) P α β).map (Prod.map b b) ∧
        ξ.map (Prod.map b b) univ = ξ univ := by
  let κ₀ := condDistrib u a μ
  let κ₁ := condDistrib u a ν
  let α := fun i ↦ normalizedActualBinKernel κ₀ (S i) (hS i) (fallbackS i)
  let β := fun j ↦ normalizedActualBinKernel κ₁ (T j) (hT j) (fallbackT j)
  let asrc := fun z i ↦ (κ₀ z).real (S i)
  let btgt := fun z j ↦ (κ₁ z).real (T j)
  have hma (i : I) : Measurable (fun z ↦ asrc z i) := (κ₀.measurable_coe (hS i)).ennreal_toReal
  have hmb (j : J) : Measurable (fun z ↦ btgt z j) := (κ₁.measurable_coe (hT j)).ennreal_toReal
  have hsourceKernel : finiteClassMarginalKernel asrc α =ᵐ[μ.map a] κ₀ :=
    finiteClassMarginalKernel_normalized_bins_eq_original_ae (μ.map a) κ₀ S hS hdS hcoverS fallbackS
  have htargetKernel : finiteClassMarginalKernel btgt β =ᵐ[μ.map a] κ₁ :=
    finiteClassMarginalKernel_normalized_bins_eq_original_ae (μ.map a) κ₁ T hT hdT hcoverT fallbackT
  have hsource : μ.map a ⊗ₘ finiteClassMarginalKernel asrc α = μ.map (fun x ↦ (a x, u x)) := by
    rw [Measure.compProd_congr (η := κ₀) hsourceKernel]
    exact compProd_map_condDistrib hu.aemeasurable
  have htarget : μ.map a ⊗ₘ finiteClassMarginalKernel btgt β = ν.map (fun x ↦ (a x, u x)) := by
    rw [Measure.compProd_congr (η := κ₁) htargetKernel, hbalance]
    exact compProd_map_condDistrib hu.aemeasurable
  have hbinlegal : ∀ᵐ z ∂μ.map a, ∀ i j, 0 < P z i j →
      ∀ᵐ p ∂(α i z).prod (β j z), p.1 ≤ p.2 := by
    filter_upwards [hP, hrow, hcol, hzero] with z hz hr hc hzeroz
    refine positive_classFlow_bin_legal (P z) (asrc z) (btgt z) hz hr hc
      (fun i ↦ α i z) (fun j ↦ β j z) S T ?_ ?_ allowed hzeroz hbins
    · intro i hi
      apply normalizedActualBinKernel_supported_of_mass_ne_zero κ₀ (S i) (hS i) (fallbackS i) z
      intro heq
      have hz : asrc z i = 0 := by simp only [asrc, measureReal_def, heq, ENNReal.toReal_zero]
      exact (ne_of_gt hi) hz
    · intro j hj
      apply normalizedActualBinKernel_supported_of_mass_ne_zero κ₁ (T j) (hT j) (fallbackT j) z
      intro heq
      have hz : btgt z j = 0 := by simp only [btgt, measureReal_def, heq, ENNReal.toReal_zero]
      exact (ne_of_gt hj) hz
  exact exists_original_calibrated_coupling_of_positive_classFlow hN ha hu hinj horder
    μ ν hμN hνN (μ.map a) P asrc btgt hmP hma hmb α β hP hrow hcol
    hsource htarget hbinlegal

end OTSelector.Reconstruction

end
end
