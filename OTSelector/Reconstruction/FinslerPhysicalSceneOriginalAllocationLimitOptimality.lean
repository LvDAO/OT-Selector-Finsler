import OTSelector.Probability.ZeroCostWeakLimit
import OTSelector.Transport.Calibration.LabelFaceOptimality
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalTargetMarginal
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalSourceMarginal
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalPlanCostDecay

/-!
# Original paired-plan weak limits belong to the original optimal face

The original iid weighted targets, exact source, and original scaled distance
budget identify both plans. A second weak limit preserves all three properties.
-/
open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
variable {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ProperSpace M] [PolishSpace M] [Nonempty M] [MeasurableSpace Z]
local instance : SecondCountableTopology (ProbabilityMeasure (M × M)) :=
  probabilityMeasure_weakSecondCountable
local instance : BorelSpace (ProbabilityMeasure (M × M)) :=
  probabilityMeasure_weakBorelSpace

/-- The unchanged distance cost after subtracting the calibrated potential. -/
def originalDistanceSlack (u : M → ℝ) (hu : Continuous u) : C(M × M, ℝ) :=
  ⟨fun p ↦ dist p.1 p.2 - u p.2 + u p.1,
    (continuous_fst.dist continuous_snd).sub (hu.comp continuous_snd) |>.add
      (hu.comp continuous_fst)⟩

theorem originalDistanceSlack_nonnegative (u : M → ℝ) (hu : LipschitzWith 1 u)
    (p : M × M) : 0 ≤ originalDistanceSlack u hu.continuous p :=
  originalDistanceSlack_nonneg hu p.1 p.2

section Face
variable (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (u : M → ℝ) (hu : LipschitzWith 1 u) (a : M → Z) (ha : Measurable a)
  (N : Set M) (hN : MeasurableSet N)
  (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
  (horder : ∀ x ∈ N, ∀ y ∈ N,
    (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
  (hface : ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
    ∃ k : Kernel Z (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
      ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
        (condDistrib id a μ z) (condDistrib id a ν z) ∧
        ∀ᵐ p ∂k z, p.1 ∈ N ∧ p.2 ∈ N ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)

include μ ν u hu a ha N hN hμN hνN horder hface

/-- Exact original marginals and vanishing original distance slack return
both coordinates of the same paired law to the original optimal face. -/
theorem ae_original_pair_optimal_of_marginals_of_calibrated
    (Q : ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
    (hf : ∀ᵐ q ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      (q.1 : Measure (M × M)).fst = μ ∧ (q.2 : Measure (M × M)).fst = μ)
    (hs : ∀ᵐ q ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      (q.1 : Measure (M × M)).snd = ν ∧ (q.2 : Measure (M × M)).snd = ν)
    (hc₁ : ∀ᵐ q ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      ∀ᵐ p ∂(q.1 : Measure (M × M)), originalDistanceSlack u hu.continuous p = 0)
    (hc₂ : ∀ᵐ q ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      ∀ᵐ p ∂(q.2 : Measure (M × M)), originalDistanceSlack u hu.continuous p = 0) :
    ∀ᵐ q ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      IsOptimalCoupling edist μ ν (q.1 : Measure (M × M)) ∧
      IsOptimalCoupling edist μ ν (q.2 : Measure (M × M)) := by
  filter_upwards [hf, hs, hc₁, hc₂] with q hqf hqs hq₁ hq₂
  constructor
  · apply isOptimalCoupling_of_calibrated_of_original_label_face
      μ ν u hu.continuous a ha N hN hμN hνN horder hface _ ⟨hqf.1, hqs.1⟩
    filter_upwards [hq₁] with p hp
    change dist p.1 p.2 - u p.2 + u p.1 = 0 at hp
    linarith
  · apply isOptimalCoupling_of_calibrated_of_original_label_face
      μ ν u hu.continuous a ha N hN hμN hνN horder hface _ ⟨hqf.2, hqs.2⟩
    filter_upwards [hq₂] with p hp
    change dist p.1 p.2 - u p.2 + u p.1 = 0 at hp
    linarith

/-- Every weak limit of the actual original iid/Dirichlet paired allocation
laws is carried by original optimal couplings. All marginal and calibration
conditions are derived from the finite experiments and their scaled budget. -/
theorem ae_originalAllocationPlanPairLaw_optimal_of_tendsto
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (ap am : ∀ k, ((Fin (m k + 1) → M) × (Fin (m k + 1) → ℝ)) →
      M → Fin (m k + 1) → ℝ)
    (hpm : ∀ k i, Measurable (fun z :
      ((Fin (m k + 1) → M) × (Fin (m k + 1) → ℝ)) × M ↦ ap k z.1 z.2 i))
    (hmm : ∀ k i, Measurable (fun z :
      ((Fin (m k + 1) → M) × (Fin (m k + 1) → ℝ)) × M ↦ am k z.1 z.2 i))
    (hfp : ∀ k, ∀ᵐ w ∂originalTargetEnvironmentLaw (m k) ν,
      IsSemidiscreteAllocation μ w.2 (ap k w))
    (hfm : ∀ k, ∀ᵐ w ∂originalTargetEnvironmentLaw (m k) ν,
      IsSemidiscreteAllocation μ w.2 (am k w))
    (scale : ℕ → ℝ) (hpos : ∀ k, 0 < scale k) (hscale : Tendsto scale atTop atTop)
    {Energy : ℝ≥0∞} (hEnergy : Energy ≠ ⊤)
    (hbp : ∀ k, (∫⁻ w, ∫⁻ p, ENNReal.ofReal
      (scale k ^ 2 * originalDistanceSlack u hu.continuous p)
      ∂physicalSceneGlobalAllocationFamily μ (ap k) Prod.fst w
      ∂originalTargetEnvironmentLaw (m k) ν) ≤ Energy)
    (hbm : ∀ k, (∫⁻ w, ∫⁻ p, ENNReal.ofReal
      (scale k ^ 2 * originalDistanceSlack u hu.continuous p)
      ∂physicalSceneGlobalAllocationFamily μ (am k) Prod.fst w
      ∂originalTargetEnvironmentLaw (m k) ν) ≤ Energy)
    (Q : ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
    (hweak : Tendsto (fun k ↦ physicalSceneOriginalAllocationPlanPairLaw
      (originalTargetEnvironmentLaw (m k) ν) μ ν (ap k) (am k) (hpm k) (hmm k)
      Prod.fst (fun i ↦ (measurable_pi_apply i).comp measurable_fst)) atTop (𝓝 Q)) :
    ∀ᵐ q ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      IsOptimalCoupling edist μ ν (q.1 : Measure (M × M)) ∧
      IsOptimalCoupling edist μ ν (q.2 : Measure (M × M)) := by
  have hf := ae_fst_eq_of_originalAllocationPlanPairLaw_tendsto m
    (fun k ↦ originalTargetEnvironmentLaw (m k) ν) μ ν ap am hpm hmm
    (fun _ ↦ Prod.fst) (fun _ i ↦ (measurable_pi_apply i).comp measurable_fst)
    (fun _ ↦ Prod.snd) hfp hfm Q hweak
  have hs := ae_snd_eq_of_originalAllocationPlanPairLaw_tendsto
    m hm μ ν ap am hpm hmm hfp hfm Q hweak
  have hc := tendsto_canonical_originalAllocationPlanPairLaw_expected_cost_zero
    m μ ν ap am hpm hmm hfp hfm (originalDistanceSlack u hu.continuous)
    scale hpos hscale hEnergy hbp hbm
  apply ae_original_pair_optimal_of_marginals_of_calibrated
    μ ν u hu a ha N hN hμN hνN horder hface Q hf hs
  · exact ae_cost_zero_of_probabilityPlanLaw_weak_of_expected_cost_zero
      _ Q hweak Prod.fst continuous_fst _ (originalDistanceSlack_nonnegative u hu) hc.1
  · exact ae_cost_zero_of_probabilityPlanLaw_weak_of_expected_cost_zero
      _ Q hweak Prod.snd continuous_snd _ (originalDistanceSlack_nonnegative u hu) hc.2

/-- A further weak limit preserves the same original optimal face in both
coordinates. Its marginals and calibrated slack are recovered explicitly. -/
theorem ae_original_pair_optimal_of_tendsto_of_ae
    (P : ℕ → ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
    (Q : ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))
    (hweak : Tendsto P atTop (𝓝 Q))
    (hP : ∀ n, ∀ᵐ q ∂(P n :
      Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      IsOptimalCoupling edist μ ν (q.1 : Measure (M × M)) ∧
      IsOptimalCoupling edist μ ν (q.2 : Measure (M × M))) :
    ∀ᵐ q ∂(Q : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      IsOptimalCoupling edist μ ν (q.1 : Measure (M × M)) ∧
      IsOptimalCoupling edist μ ν (q.2 : Measure (M × M)) := by
  have hcouple (n : ℕ) : ∀ᵐ q ∂(P n :
      Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      Vlasov.IsCoupling (q.1 : Measure (M × M)) μ ν ∧
      Vlasov.IsCoupling (q.2 : Measure (M × M)) μ ν :=
    (hP n).mono fun q hq ↦ ⟨hq.1.1, hq.2.1⟩
  have hcal (n : ℕ) : ∀ᵐ q ∂(P n :
      Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
      (∀ᵐ p ∂(q.1 : Measure (M × M)), originalDistanceSlack u hu.continuous p = 0) ∧
      (∀ᵐ p ∂(q.2 : Measure (M × M)), originalDistanceSlack u hu.continuous p = 0) := by
    filter_upwards [hP n] with q hq
    have one (π : Measure (M × M)) (hπ : IsOptimalCoupling edist μ ν π) :
        ∀ᵐ p ∂π, originalDistanceSlack u hu.continuous p = 0 := by
      obtain ⟨k, hk, hrec, hc⟩ := (hface π).mp hπ
      rw [← hrec]
      apply Measure.ae_comp_of_ae_ae
        (measurableSet_eq_fun (originalDistanceSlack u hu.continuous).continuous.measurable
          measurable_const)
      filter_upwards [hc] with z hz
      filter_upwards [hz.2] with p hp
      have hh := (horder p.1 hp.1 p.2 hp.2.1).mp hp.2.2
      change dist p.1 p.2 - u p.2 + u p.1 = 0
      linarith
    exact ⟨one _ hq.1, one _ hq.2⟩
  have hf := ae_fst_pair_eq_of_tendsto_of_ae P Q μ hweak
    (fun n ↦ (hcouple n).mono fun q hq ↦ ⟨hq.1.1, hq.2.1⟩)
  have hs := ae_snd_pair_eq_of_tendsto_of_ae P Q ν hweak
    (fun n ↦ (hcouple n).mono fun q hq ↦ ⟨hq.1.2, hq.2.2⟩)
  apply ae_original_pair_optimal_of_marginals_of_calibrated
    μ ν u hu a ha N hN hμN hνN horder hface Q hf hs
  · exact ae_cost_zero_of_probabilityPlanLaw_weak_of_ae_cost_zero P Q hweak
      Prod.fst continuous_fst _ (originalDistanceSlack_nonnegative u hu)
      (fun n ↦ (hcal n).mono fun q hq ↦ hq.1)
  · exact ae_cost_zero_of_probabilityPlanLaw_weak_of_ae_cost_zero P Q hweak
      Prod.snd continuous_snd _ (originalDistanceSlack_nonnegative u hu)
      (fun n ↦ (hcal n).mono fun q hq ↦ hq.2)
end Face
end OTSelector.Reconstruction
