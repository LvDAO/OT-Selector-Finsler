import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalAllocationPlanLaw
import OTSelector.Probability.DirichletReference
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Decay of original unscaled plan-law costs

The original scaled global energy bounds the unscaled cost by its exact
inverse-square scale. Almost-sure probability completion and the original
joint pushforward law preserve these expectations without changing the
sampled environment or either original allocation.
-/

open Set Function Filter MeasureTheory OTSelector.Probability
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- A finite scalar factors out of the original two successive integrals,
even when their values may be infinite. -/
theorem lintegral_lintegral_scaled_cost_eq (R : Measure Ω) (Γ : Ω → Measure X)
    (e : X → ℝ) (scale : ℝ) :
    (∫⁻ w, ∫⁻ x, ENNReal.ofReal (scale ^ 2 * e x) ∂Γ w ∂R) =
      ENNReal.ofReal (scale ^ 2) * ∫⁻ w, ∫⁻ x, ENNReal.ofReal (e x) ∂Γ w ∂R := by
  simp_rw [ENNReal.ofReal_mul (sq_nonneg scale),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The actual original scaled budget gives an explicit unscaled expected
cost bound. -/
theorem lintegral_lintegral_cost_le_of_scaled_budget
    (R : Measure Ω) (Γ : Ω → Measure X) (e : X → ℝ)
    {scale : ℝ} (hscale : 0 < scale) {Energy : ℝ≥0∞}
    (hbudget : (∫⁻ w, ∫⁻ x, ENNReal.ofReal (scale ^ 2 * e x) ∂Γ w ∂R) ≤ Energy) :
    (∫⁻ w, ∫⁻ x, ENNReal.ofReal (e x) ∂Γ w ∂R) ≤
      Energy / ENNReal.ofReal (scale ^ 2) := by
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hscale))))
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [mul_comm, ← lintegral_lintegral_scaled_cost_eq]
  exact hbudget

/-- Any finite uniform scaled energy forces the original unscaled expected
cost to vanish as the real scale tends to infinity. -/
theorem tendsto_original_expected_cost_zero_of_scaled_budget
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (R : ∀ n, Measure (Ωn n)) (Γ : ∀ n, Ωn n → Measure X) (e : X → ℝ)
    (scale : ℕ → ℝ) (hpos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop) {Energy : ℝ≥0∞} (hEnergy : Energy ≠ ⊤)
    (hbudget : ∀ n, (∫⁻ w, ∫⁻ x, ENNReal.ofReal (scale n ^ 2 * e x)
      ∂Γ n w ∂R n) ≤ Energy) :
    Tendsto (fun n ↦ ∫⁻ w, ∫⁻ x, ENNReal.ofReal (e x) ∂Γ n w ∂R n)
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun n ↦ scale n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).comp hscale
  have hden : Tendsto (fun n ↦ ENNReal.ofReal (scale n ^ 2)) atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_nhds_top.mpr hpow
  have hrate : Tendsto (fun n ↦ Energy / ENNReal.ofReal (scale n ^ 2))
      atTop (𝓝 0) := by
    simpa only [ENNReal.div_top] using ENNReal.Tendsto.div tendsto_const_nhds
      (Or.inr (by simp)) hden (Or.inr hEnergy)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrate
    (fun _ ↦ bot_le) (fun n ↦ lintegral_lintegral_cost_le_of_scaled_budget
      (R n) (Γ n) e (hpos n) (hbudget n))

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

/-- The true original paired plan law has exactly the original global-plan
cost expectations, for each member of the pair. The probability completion
is removed by its almost-sure identity under the same original law. -/
theorem lintegral_originalAllocationPlanPairLaw_cost_eq
    (R : Measure Ω) [IsProbabilityMeasure R]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (hpm : ∀ k, Measurable (fun z : Ω × M ↦ ap z.1 z.2 k))
    (hmm : ∀ k, Measurable (fun z : Ω × M ↦ am z.1 z.2 k))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ k, Measurable (fun w ↦ Y w k))
    (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂R, IsSemidiscreteAllocation μ (p w) (ap w))
    (hfm : ∀ᵐ w ∂R, IsSemidiscreteAllocation μ (p w) (am w))
    (e : M × M → ℝ) (he : Measurable e) :
    let law := physicalSceneOriginalAllocationPlanPairLaw R μ ν ap am hpm hmm Y hY
    ((∫⁻ q, ∫⁻ x, ENNReal.ofReal (e x) ∂(q.1 : Measure (M × M))
        ∂(law : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))) =
      ∫⁻ w, ∫⁻ x, ENNReal.ofReal (e x) ∂physicalSceneGlobalAllocationFamily μ ap Y w ∂R) ∧
    ((∫⁻ q, ∫⁻ x, ENNReal.ofReal (e x) ∂(q.2 : Measure (M × M))
        ∂(law : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M)))) =
      ∫⁻ w, ∫⁻ x, ENNReal.ofReal (e x) ∂physicalSceneGlobalAllocationFamily μ am Y w ∂R) := by
  intro law
  let pair := fun w ↦
    (physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap Y w,
      physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am Y w)
  have hm : Measurable pair :=
    (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν ap hpm Y hY).prodMk
      (measurable_physicalSceneOriginalAllocationProbabilityPlanFamily μ ν am hmm Y hY)
  have hpmeas : Measurable (fun q :
      ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M) ↦
      ∫⁻ x, ENNReal.ofReal (e x) ∂(q.1 : Measure (M × M))) :=
    (Measure.measurable_lintegral he.ennreal_ofReal).comp
      (measurable_subtype_coe.comp measurable_fst)
  have hmmeas : Measurable (fun q :
      ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M) ↦
      ∫⁻ x, ENNReal.ofReal (e x) ∂(q.2 : Measure (M × M))) :=
    (Measure.measurable_lintegral he.ennreal_ofReal).comp
      (measurable_subtype_coe.comp measurable_snd)
  constructor
  · change (∫⁻ q, ∫⁻ x, ENNReal.ofReal (e x) ∂(q.1 : Measure (M × M))
        ∂Measure.map pair R) = _
    rw [lintegral_map hpmeas hm]
    apply lintegral_congr_ae
    filter_upwards [physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq
      R μ ν ap Y p hfp] with w hw
    exact congrArg (fun π : Measure (M × M) ↦ ∫⁻ x, ENNReal.ofReal (e x) ∂π) hw
  · change (∫⁻ q, ∫⁻ x, ENNReal.ofReal (e x) ∂(q.2 : Measure (M × M))
        ∂Measure.map pair R) = _
    rw [lintegral_map hmmeas hm]
    apply lintegral_congr_ae
    filter_upwards [physicalSceneOriginalAllocationProbabilityPlanFamily_ae_eq
      R μ ν am Y p hfm] with w hw
    exact congrArg (fun π : Measure (M × M) ↦ ∫⁻ x, ENNReal.ofReal (e x) ∂π) hw

/-- Under any original measurable environment, both actual paired-plan law
cost expectations vanish under a finite uniform original scaled budget.
The sample-size indexing is unrestricted: decay is controlled by the scale. -/
theorem tendsto_originalAllocationPlanPairLaw_expected_cost_zero
    {Ωn : ℕ → Type*} [∀ k, MeasurableSpace (Ωn k)]
    (m : ℕ → ℕ) (R : ∀ k, Measure (Ωn k)) [∀ k, IsProbabilityMeasure (R k)]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : ∀ k, Ωn k → M → Fin (m k + 1) → ℝ)
    (hpm : ∀ k i, Measurable (fun z : Ωn k × M ↦ ap k z.1 z.2 i))
    (hmm : ∀ k i, Measurable (fun z : Ωn k × M ↦ am k z.1 z.2 i))
    (Y : ∀ k, Ωn k → Fin (m k + 1) → M)
    (hY : ∀ k i, Measurable (fun w ↦ Y k w i))
    (p : ∀ k, Ωn k → Fin (m k + 1) → ℝ)
    (hfp : ∀ k, ∀ᵐ w ∂R k, IsSemidiscreteAllocation μ (p k w) (ap k w))
    (hfm : ∀ k, ∀ᵐ w ∂R k, IsSemidiscreteAllocation μ (p k w) (am k w))
    (e : M × M → ℝ) (he : Measurable e)
    (scale : ℕ → ℝ) (hpos : ∀ k, 0 < scale k)
    (hscale : Tendsto scale atTop atTop) {Energy : ℝ≥0∞} (hEnergy : Energy ≠ ⊤)
    (hbp : ∀ k, (∫⁻ w, ∫⁻ x, ENNReal.ofReal (scale k ^ 2 * e x)
      ∂physicalSceneGlobalAllocationFamily μ (ap k) (Y k) w ∂R k) ≤ Energy)
    (hbm : ∀ k, (∫⁻ w, ∫⁻ x, ENNReal.ofReal (scale k ^ 2 * e x)
      ∂physicalSceneGlobalAllocationFamily μ (am k) (Y k) w ∂R k) ≤ Energy) :
    let laws := fun k ↦ physicalSceneOriginalAllocationPlanPairLaw
      (R k) μ ν (ap k) (am k) (hpm k) (hmm k) (Y k) (hY k)
    Tendsto (fun k ↦ ∫⁻ q, ∫⁻ x, ENNReal.ofReal (e x) ∂(q.1 : Measure (M × M))
      ∂(laws k : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))))
      atTop (𝓝 0) ∧
    Tendsto (fun k ↦ ∫⁻ q, ∫⁻ x, ENNReal.ofReal (e x) ∂(q.2 : Measure (M × M))
      ∂(laws k : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))))
      atTop (𝓝 0) := by
  intro laws
  have heq (k : ℕ) := lintegral_originalAllocationPlanPairLaw_cost_eq
    (R k) μ ν (ap k) (am k) (hpm k) (hmm k) (Y k) (hY k) (p k) (hfp k) (hfm k) e he
  constructor
  · convert tendsto_original_expected_cost_zero_of_scaled_budget R
      (fun k ↦ physicalSceneGlobalAllocationFamily μ (ap k) (Y k)) e
      scale hpos hscale hEnergy hbp using 1
    funext k
    exact (heq k).1
  · convert tendsto_original_expected_cost_zero_of_scaled_budget R
      (fun k ↦ physicalSceneGlobalAllocationFamily μ (am k) (Y k)) e
      scale hpos hscale hEnergy hbm using 1
    funext k
    exact (heq k).2

variable [TopologicalSpace M] [OpensMeasurableSpace (M × M)]

/-- Specialization to the unchanged original iid-targets times Dirichlet-one
experiment and a true continuous cost. Any divergent real scale is allowed,
including the original scale along a sample subsequence. -/
theorem tendsto_canonical_originalAllocationPlanPairLaw_expected_cost_zero
    (m : ℕ → ℕ) (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ap am : ∀ k, ((Fin (m k + 1) → M) × (Fin (m k + 1) → ℝ)) →
      M → Fin (m k + 1) → ℝ)
    (hpm : ∀ k i, Measurable (fun z :
      ((Fin (m k + 1) → M) × (Fin (m k + 1) → ℝ)) × M ↦ ap k z.1 z.2 i))
    (hmm : ∀ k i, Measurable (fun z :
      ((Fin (m k + 1) → M) × (Fin (m k + 1) → ℝ)) × M ↦ am k z.1 z.2 i))
    (hfp : ∀ k, ∀ᵐ w ∂(Measure.pi (fun _ : Fin (m k + 1) ↦ ν)).prod (dirichletOne (m k)),
      IsSemidiscreteAllocation μ w.2 (ap k w))
    (hfm : ∀ k, ∀ᵐ w ∂(Measure.pi (fun _ : Fin (m k + 1) ↦ ν)).prod (dirichletOne (m k)),
      IsSemidiscreteAllocation μ w.2 (am k w))
    (e : C(M × M, ℝ)) (scale : ℕ → ℝ) (hpos : ∀ k, 0 < scale k)
    (hscale : Tendsto scale atTop atTop) {Energy : ℝ≥0∞} (hEnergy : Energy ≠ ⊤)
    (hbp : ∀ k, (∫⁻ w, ∫⁻ x, ENNReal.ofReal (scale k ^ 2 * e x)
      ∂physicalSceneGlobalAllocationFamily μ (ap k) Prod.fst w
      ∂(Measure.pi (fun _ : Fin (m k + 1) ↦ ν)).prod (dirichletOne (m k))) ≤ Energy)
    (hbm : ∀ k, (∫⁻ w, ∫⁻ x, ENNReal.ofReal (scale k ^ 2 * e x)
      ∂physicalSceneGlobalAllocationFamily μ (am k) Prod.fst w
      ∂(Measure.pi (fun _ : Fin (m k + 1) ↦ ν)).prod (dirichletOne (m k))) ≤ Energy) :
    let laws := fun k ↦ physicalSceneOriginalAllocationPlanPairLaw
      ((Measure.pi (fun _ : Fin (m k + 1) ↦ ν)).prod (dirichletOne (m k)))
      μ ν (ap k) (am k) (hpm k) (hmm k) Prod.fst
      (fun i ↦ (measurable_pi_apply i).comp measurable_fst)
    Tendsto (fun k ↦ ∫⁻ q, ∫⁻ x, ENNReal.ofReal (e x) ∂(q.1 : Measure (M × M))
      ∂(laws k : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))))
      atTop (𝓝 0) ∧
    Tendsto (fun k ↦ ∫⁻ q, ∫⁻ x, ENNReal.ofReal (e x) ∂(q.2 : Measure (M × M))
      ∂(laws k : Measure (ProbabilityMeasure (M × M) × ProbabilityMeasure (M × M))))
      atTop (𝓝 0) :=
  tendsto_originalAllocationPlanPairLaw_expected_cost_zero m
    (fun k ↦ (Measure.pi (fun _ : Fin (m k + 1) ↦ ν)).prod (dirichletOne (m k)))
    μ ν ap am hpm hmm (fun _ ↦ Prod.fst)
    (fun _ i ↦ (measurable_pi_apply i).comp measurable_fst) (fun _ ↦ Prod.snd)
    hfp hfm e e.continuous.measurable scale hpos hscale hEnergy hbp hbm

end OTSelector.Reconstruction
