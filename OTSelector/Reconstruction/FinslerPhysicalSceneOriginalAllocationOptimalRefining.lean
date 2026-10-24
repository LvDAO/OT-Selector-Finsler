import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationLimitOptimality
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationPlanIterated
import OTSelector.Topology.CommonIteratedRefiningSubsequence

/-! Original iid weighted allocations produce both optimal weak-law stages. -/
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


/-- Compact original populations and the actual scaled distance budget
construct both separate weak limits, each carried by original optimal plans.
Neither limiting law, a coupling, nor an optimality witness is a premise. -/
theorem exists_refining_iterated_optimal_originalAllocationPlanPairLaw
    (ap am : ∀ (_ℓ n : ℕ), ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) →
      M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n i, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap ℓ n z.1 z.2 i))
    (hmm : ∀ ℓ n i, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am ℓ n z.1 z.2 i))
    (hfp : ∀ ℓ n, ∀ᵐ w ∂originalTargetEnvironmentLaw n ν,
      IsSemidiscreteAllocation μ w.2 (ap ℓ n w))
    (hfm : ∀ ℓ n, ∀ᵐ w ∂originalTargetEnvironmentLaw n ν,
      IsSemidiscreteAllocation μ w.2 (am ℓ n w))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (scale : ℕ → ℝ) (hpos : ∀ n, 0 < scale n) (hscale : Tendsto scale atTop atTop)
    {Energy : ℝ≥0∞} (hEnergy : Energy ≠ ⊤)
    (hbp : ∀ ℓ n, (∫⁻ w, ∫⁻ p, ENNReal.ofReal
      (scale n ^ 2 * originalDistanceSlack u hu.continuous p)
      ∂physicalSceneGlobalAllocationFamily μ (ap ℓ n) Prod.fst w
      ∂originalTargetEnvironmentLaw n ν) ≤ Energy)
    (hbm : ∀ ℓ n, (∫⁻ w, ∫⁻ p, ENNReal.ofReal
      (scale n ^ 2 * originalDistanceSlack u hu.continuous p)
      ∂physicalSceneGlobalAllocationFamily μ (am ℓ n) Prod.fst w
      ∂originalTargetEnvironmentLaw n ν) ≤ Energy)
    (φ₀ : ℕ → ℕ → ℕ) (hφ₀ : ∀ ℓ, StrictMono (φ₀ ℓ))
    (ψ₀ : ℕ → ℕ) (_hψ₀ : StrictMono ψ₀) :
    let laws := fun ℓ n ↦ physicalSceneOriginalAllocationPlanPairLaw
      (originalTargetEnvironmentLaw n ν) μ ν (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n)
      Prod.fst (fun i ↦ (measurable_pi_apply i).comp measurable_fst)
    ∃ Q : ℕ → ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)),
      ∃ φ : ℕ → ℕ → ℕ, (∀ ℓ, StrictMono (φ ℓ)) ∧
        (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ₀ ℓ (φ ℓ n))) atTop (𝓝 (Q ℓ))) ∧
        (∀ ℓ, ∀ᵐ q ∂(Q ℓ : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
          IsOptimalCoupling edist μ ν (q.1 : Measure (M × M)) ∧
          IsOptimalCoupling edist μ ν (q.2 : Measure (M × M))) ∧
        ∃ R : ProbabilityMeasure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)),
          ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (fun ℓ ↦ Q (ψ₀ (ψ ℓ))) atTop (𝓝 R) ∧
            ∀ᵐ q ∂(R : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))),
              IsOptimalCoupling edist μ ν (q.1 : Measure (M × M)) ∧
              IsOptimalCoupling edist μ ν (q.2 : Measure (M × M)) := by
  intro laws
  have hYB (n : ℕ) : ∀ᵐ w ∂originalTargetEnvironmentLaw n ν, ∀ i, w.1 i ∈ B := by
    apply ae_of_ae_map (μ := originalTargetEnvironmentLaw n ν)
      (p := fun y : Fin (n + 1) → M ↦ ∀ i, y i ∈ B) measurable_fst.aemeasurable
    have hi : ∀ᵐ y ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν), ∀ i, y i ∈ B := by
      apply ae_all_iff.mpr
      intro i
      apply ae_of_ae_map (μ := Measure.pi (fun _ : Fin (n + 1) ↦ ν))
        (p := fun y : M ↦ y ∈ B) (measurable_pi_apply i).aemeasurable
      rwa [(measurePreserving_eval (μ := fun _ : Fin (n + 1) ↦ ν) i).map_eq]
    simpa only [originalTargetEnvironmentLaw, Measure.map_fst_prod, measure_univ, one_smul]
      using hi
  have htight := isTightMeasureSet_originalAllocationPlanPairLaw
    (fun s : ℕ × ℕ ↦ s.2) (fun s : ℕ × ℕ ↦ originalTargetEnvironmentLaw s.2 ν)
    μ ν (fun s ↦ ap s.1 s.2) (fun s ↦ am s.1 s.2)
    (fun s ↦ hpm s.1 s.2) (fun s ↦ hmm s.1 s.2)
    (fun _ ↦ Prod.fst) (fun _ i ↦ (measurable_pi_apply i).comp measurable_fst)
    (fun _ ↦ Prod.snd) (fun s ↦ hfp s.1 s.2) (fun s ↦ hfm s.1 s.2)
    hA hB hμA (fun s ↦ hYB s.2)
  obtain ⟨Q₀, φ, hφ, hi, R₀, ψ, hψ, ho⟩ :=
    exists_common_iterated_refining_probabilityMeasure_subseq_of_isTight
      (fun _ : Unit ↦ laws) (fun _ ↦ htight) φ₀ ψ₀
  let Q := Q₀ ()
  let R := R₀ ()
  have hinner := hi ()
  have houter := ho ()
  have hopt (ℓ : ℕ) := ae_originalAllocationPlanPairLaw_optimal_of_tendsto
    μ ν u hu a ha N hN hμN hνN horder hface (φ₀ ℓ ∘ φ ℓ) ((hφ₀ ℓ).comp (hφ ℓ)).tendsto_atTop
    (fun n ↦ ap ℓ (φ₀ ℓ (φ ℓ n))) (fun n ↦ am ℓ (φ₀ ℓ (φ ℓ n)))
    (fun n ↦ hpm ℓ (φ₀ ℓ (φ ℓ n))) (fun n ↦ hmm ℓ (φ₀ ℓ (φ ℓ n)))
    (fun n ↦ hfp ℓ (φ₀ ℓ (φ ℓ n))) (fun n ↦ hfm ℓ (φ₀ ℓ (φ ℓ n)))
    (scale ∘ φ₀ ℓ ∘ φ ℓ) (fun n ↦ hpos (φ₀ ℓ (φ ℓ n))) (hscale.comp ((hφ₀ ℓ).comp (hφ ℓ)).tendsto_atTop)
    hEnergy (fun n ↦ hbp ℓ (φ₀ ℓ (φ ℓ n))) (fun n ↦ hbm ℓ (φ₀ ℓ (φ ℓ n))) (Q ℓ) (hinner ℓ)
  refine ⟨Q, φ, hφ, hinner, hopt, R, ψ, hψ, houter, ?_⟩
  exact ae_original_pair_optimal_of_tendsto_of_ae
    μ ν u hu a ha N hN hμN hνN horder hface (fun ℓ ↦ Q (ψ₀ (ψ ℓ))) R houter
    (fun ℓ ↦ hopt (ψ₀ (ψ ℓ)))
end Face
end OTSelector.Reconstruction
