import OTSelector.Reconstruction.FractionalCoreRestriction
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Original marginal mass controls expected empirical core loss

The expected fraction of samples outside a measurable physical core is exactly
its original marginal mass. Every measurable feasible assignment therefore loses
at most the sum of the two original marginal masses when these endpoints are
discarded. No energy estimate or restriction of the full sample law is used.
-/

open Set Matrix MeasureTheory
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Original sample marginals determine the exact expected empirical event mass;
independence is not required for this identity. -/
theorem integral_empirical_event_mass_of_marginals
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} [IsFiniteMeasure P] {μ : Measure X} [IsFiniteMeasure μ]
    {n : ℕ} (hn : 0 < n) (Xsample : Ω → Fin n → X)
    (hX : ∀ i, MeasurePreserving (fun ω ↦ Xsample ω i) P μ)
    {S : Set X} (hS : MeasurableSet S) :
    Integrable (fun ω ↦ (∑ i : Fin n, S.indicator (fun _ ↦ (1 : ℝ)) (Xsample ω i)) / n) P ∧
    (∫ ω, (∑ i : Fin n, S.indicator (fun _ ↦ (1 : ℝ)) (Xsample ω i)) / n ∂P) =
      μ.real S := by
  classical
  have hm : Measurable (S.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hS
  have hi (i : Fin n) : Integrable
      (fun ω ↦ S.indicator (fun _ ↦ (1 : ℝ)) (Xsample ω i)) P := by
    apply Integrable.of_bound (hm.comp (hX i).measurable).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hx : Xsample ω i ∈ S <;> simp [hx]
  have he (i : Fin n) : (∫ ω, S.indicator (fun _ ↦ (1 : ℝ)) (Xsample ω i) ∂P) =
      μ.real S := by
    rw [← integral_map (hX i).measurable.aemeasurable hm.aestronglyMeasurable, (hX i).map_eq]
    simpa using integral_indicator_const (μ := μ) (1 : ℝ) hS
  refine ⟨(integrable_finsetSum _ (fun i _ ↦ hi i)).div_const _, ?_⟩
  rw [integral_div, integral_finsetSum _ (fun i _ ↦ hi i)]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn.ne')

/-- Under the original sample law, the expected mass of edges touching discarded
physical endpoints is bounded by the two original marginal losses, uniformly
over every measurable feasible fractional assignment. -/
theorem expected_fractional_endpoint_loss_le
    {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {μ : Measure X} [IsFiniteMeasure μ] {ν : Measure Y} [IsFiniteMeasure ν]
    {n : ℕ} (hn : 0 < n) (Xsample : Ω → Fin n → X) (Ysample : Ω → Fin n → Y)
    (hX : ∀ i, MeasurePreserving (fun ω ↦ Xsample ω i) P μ)
    (hY : ∀ i, MeasurePreserving (fun ω ↦ Ysample ω i) P ν)
    (W : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hWm : ∀ i j, Measurable (fun ω ↦ W ω i j))
    (hW : ∀ᵐ ω ∂P, W ω ∈ doublyStochastic ℝ (Fin n))
    {S : Set X} {T : Set Y} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    Integrable (fun ω ↦ fractionalEdgeMass
      {ij | Xsample ω ij.1 ∈ S ∨ Ysample ω ij.2 ∈ T} (W ω)) P ∧
    (∫ ω, fractionalEdgeMass
      {ij | Xsample ω ij.1 ∈ S ∨ Ysample ω ij.2 ∈ T} (W ω) ∂P) ≤
        μ.real S + ν.real T := by
  classical
  have hQ (i j : Fin n) :
      MeasurableSet {ω | Xsample ω i ∈ S ∨ Ysample ω j ∈ T} :=
    ((hX i).measurable hS).union ((hY j).measurable hT)
  have hm := measurable_fractionalEdgeMass
    (fun ω ↦ {ij | Xsample ω ij.1 ∈ S ∨ Ysample ω ij.2 ∈ T}) W hQ hWm
  have hi : Integrable (fun ω ↦ fractionalEdgeMass
      {ij | Xsample ω ij.1 ∈ S ∨ Ysample ω ij.2 ∈ T} (W ω)) P := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards [hW] with ω hω
    have hb := fractionalEdgeMass_mem_Icc hn hω
      {ij | Xsample ω ij.1 ∈ S ∨ Ysample ω ij.2 ∈ T}
    simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
  obtain ⟨hsource, hesource⟩ := integral_empirical_event_mass_of_marginals hn Xsample hX hS
  obtain ⟨htarget, hetarget⟩ := integral_empirical_event_mass_of_marginals hn Ysample hY hT
  refine ⟨hi, ?_⟩
  have hle := integral_mono_ae hi (hsource.add htarget) (by
    filter_upwards [hW] with ω hω
    simpa only [add_div, Pi.add_apply, Set.indicator, mem_ofPred_eq] using
      fractionalEdgeMass_endpoint_union_le (W ω) hω
      {i | Xsample ω i ∈ S} {j | Ysample ω j ∈ T})
  simp only [Pi.add_apply] at hle
  rwa [integral_add hsource htarget, hesource, hetarget] at hle

/-- The unchanged independent two-color iid experiment satisfies the core-loss
bound for every measurable feasible plan, including sample-dependent optimizers. -/
theorem iid_expected_fractional_endpoint_loss_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n)
    (W : (Fin n → X) × (Fin n → Y) → Matrix (Fin n) (Fin n) ℝ)
    (hWm : ∀ i j, Measurable (fun ω ↦ W ω i j))
    (hW : ∀ᵐ ω ∂(Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν)),
      W ω ∈ doublyStochastic ℝ (Fin n))
    {S : Set X} {T : Set Y} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    let law := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    Integrable (fun ω ↦ fractionalEdgeMass {ij | ω.1 ij.1 ∈ S ∨ ω.2 ij.2 ∈ T} (W ω)) law ∧
      (∫ ω, fractionalEdgeMass {ij | ω.1 ij.1 ∈ S ∨ ω.2 ij.2 ∈ T} (W ω) ∂law) ≤
        μ.real S + ν.real T := by
  exact expected_fractional_endpoint_loss_le hn Prod.fst Prod.snd
    (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ μ) i).comp measurePreserving_fst)
    (fun i ↦ (measurePreserving_eval (fun _ : Fin n ↦ ν) i).comp measurePreserving_snd)
    W hWm hW hS hT

end OTSelector.Reconstruction
