import OTSelector.Reconstruction.FinslerPhysicalSceneRootedGlobal
import OTSelector.Probability.CavityExpectedTiltSupergradient
import OTSelector.Probability.CavitySemidiscretePressureComparison

/-!
# Actual original allocation readouts are mean supergradient slopes

The real integral on the original physical plan is exactly its allocation
objective. Hence the original expectation of that readout is the expected
tilted-value supergradient, and the difference of the two mean slopes is
bounded by the original expected absolute gap on the same experiment.
-/

open Set Function Filter MeasureTheory OTSelector.Probability
open scoped Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {M Ω : Type*} [MeasurableSpace M] [MeasurableSpace Ω] {n : ℕ}

/-- Every integrable signed physical probe has precisely its actual original
allocation objective, before any expectation or weak limit. -/
theorem integral_physicalSceneAllocationPlan_eq_allocationCost
    (μ : Measure M) {p : Fin (n + 1) → ℝ} {alloc : M → Fin (n + 1) → ℝ}
    (halloc : IsSemidiscreteAllocation μ p alloc) (Y : Fin (n + 1) → M)
    (probe : M × M → ℝ) (hprobe : Measurable probe)
    (hint : ∀ j, Integrable (fun x ↦ probe (x, Y j)) μ) :
    (∫ e, probe e ∂physicalSceneAllocationPlan μ alloc Y) =
      semidiscreteAllocationCost μ (fun x j ↦ probe (x, Y j)) alloc := by
  unfold physicalSceneAllocationPlan
  rw [integral_map (measurable_id.prodMap (measurable_of_finite Y)).aemeasurable
    hprobe.aestronglyMeasurable]
  exact halloc.integral_allocationMeasure (fun x j ↦ probe (x, Y j))
    (hprobe.comp (measurable_id.prodMap (measurable_of_finite Y))) hint

/-- The finite completion keeps the full original signed allocation readout
almost surely under the unchanged original environment. -/
theorem ae_originalGlobal_probe_integral_eq_allocationCost
    (R : Measure Ω) (μ : Measure M) [IsFiniteMeasure μ]
    (alloc : Ω → M → Fin (n + 1) → ℝ) (Y : Ω → Fin (n + 1) → M)
    (p : Ω → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ w ∂R, IsSemidiscreteAllocation μ (p w) (alloc w))
    (probe : M × M → ℝ) (hprobe : Measurable probe)
    (hint : ∀ w j, Integrable (fun x ↦ probe (x, Y w j)) μ) :
    (fun w ↦ ∫ e, probe e ∂physicalSceneGlobalAllocationFamily μ alloc Y w) =ᵐ[R]
      (fun w ↦ semidiscreteAllocationCost μ (fun x j ↦ probe (x, Y w j)) (alloc w)) := by
  filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq R μ alloc Y p hfeas, hfeas]
    with w heq hw
  rw [heq]
  exact integral_physicalSceneAllocationPlan_eq_allocationCost μ hw (Y w) probe hprobe (hint w)

/-- The actual signed mean slope readout is integrable for every original
finite environment and bounded measurable physical probe. -/
theorem integrable_originalGlobal_probe_readout
    (R : Measure Ω) [IsFiniteMeasure R] (μ : Measure M) [IsProbabilityMeasure μ]
    (alloc : Ω → M → Fin (n + 1) → ℝ)
    (halloc : ∀ j, Measurable (fun z : Ω × M ↦ alloc z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (p : Ω → Fin (n + 1) → ℝ)
    (hfeas : ∀ᵐ w ∂R, IsSemidiscreteAllocation μ (p w) (alloc w))
    (probe : M × M → ℝ) (hprobe : Measurable probe)
    (G : ℝ≥0) (hbound : ∀ x y, |probe (x, y)| ≤ G) :
    Integrable (fun w ↦ ∫ e, probe e ∂physicalSceneGlobalAllocationFamily μ alloc Y w) R := by
  have hs (w : Ω) (j : Fin (n + 1)) : Integrable (fun x ↦ probe (x, Y w j)) μ :=
    Integrable.of_bound (hprobe.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      G (ae_of_all _ fun x ↦ hbound x (Y w j))
  have hc (j : Fin (n + 1)) : Measurable (fun z : Ω × M ↦ probe (z.2, Y z.1 j)) :=
    hprobe.comp (measurable_snd.prodMk ((hY j).comp measurable_fst))
  have hm := measurable_parameterized_semidiscreteAllocationCost μ
    (fun w j x ↦ probe (x, Y w j)) (fun z ↦ alloc z.1 z.2) hc halloc
  have hi : Integrable
      (fun w ↦ semidiscreteAllocationCost μ (fun x j ↦ probe (x, Y w j)) (alloc w)) R := by
    apply Integrable.of_bound hm.aestronglyMeasurable G
    filter_upwards [hfeas] with w hw
    exact hw.abs_cost_le _ (hs w) G (ae_of_all _ fun x j ↦ hbound x (Y w j))
  exact hi.congr (ae_originalGlobal_probe_integral_eq_allocationCost
    R μ alloc Y p hfeas probe hprobe hs).symm

/-- The absolute difference of the actual mean slopes is bounded by the
actual raw original expected absolute probe gap, with all integrability
supplied by bounded probes and original allocation feasibility. -/
theorem abs_originalGlobal_mean_probe_difference_le_expected_gap
    (R : Measure Ω) [IsFiniteMeasure R] (μ : Measure M) [IsProbabilityMeasure μ]
    (ap am : Ω → M → Fin (n + 1) → ℝ)
    (hpm : ∀ j, Measurable (fun z : Ω × M ↦ ap z.1 z.2 j))
    (hmm : ∀ j, Measurable (fun z : Ω × M ↦ am z.1 z.2 j))
    (Y : Ω → Fin (n + 1) → M) (hY : ∀ j, Measurable (fun w ↦ Y w j))
    (p : Ω → Fin (n + 1) → ℝ)
    (hfp : ∀ᵐ w ∂R, IsSemidiscreteAllocation μ (p w) (ap w))
    (hfm : ∀ᵐ w ∂R, IsSemidiscreteAllocation μ (p w) (am w))
    (probe : M × M → ℝ) (hprobe : Measurable probe)
    (G : ℝ≥0) (hbound : ∀ x y, |probe (x, y)| ≤ G) :
    |(∫ w, ∫ e, probe e ∂physicalSceneGlobalAllocationFamily μ ap Y w ∂R) -
      ∫ w, ∫ e, probe e ∂physicalSceneGlobalAllocationFamily μ am Y w ∂R| ≤
      ∫ w, |(∫ e, probe e ∂physicalSceneGlobalAllocationFamily μ ap Y w) -
        ∫ e, probe e ∂physicalSceneGlobalAllocationFamily μ am Y w| ∂R := by
  rw [← integral_sub
    (integrable_originalGlobal_probe_readout R μ ap hpm Y hY p hfp probe hprobe G hbound)
    (integrable_originalGlobal_probe_readout R μ am hmm Y hY p hfm probe hprobe G hbound)]
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := R)
    (fun w ↦ (∫ e, probe e ∂physicalSceneGlobalAllocationFamily μ ap Y w) -
      ∫ e, probe e ∂physicalSceneGlobalAllocationFamily μ am Y w)

variable [StandardBorelSpace M]

/-- The real expectation of the actual original physical allocation readout
is a supergradient of the actual target-times-Dirichlet value mean. The value
at every real tilt is jointly integrable internally by the existing cavity API. -/
theorem originalDirichletMean_supergradient_of_original_optimal_allocation
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost probe : M × M → ℝ) (hc : Measurable cost)
    (hci : Integrable cost (μ.prod ν)) (hg : Measurable probe)
    (hatom : ∀ᵐ y ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν),
      ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun x ↦ cost (x, y j) - cost (x, y l))))
    (G : ℝ≥0) (hbound : ∀ x y, |probe (x, y)| ≤ G)
    (alloc : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ)
    (halloc : ∀ j, Measurable (fun z :
      ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ alloc z.1 z.2 j))
    (t : ℝ)
    (hopt : ∀ᵐ w ∂(Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n),
      IsOptimalSemidiscreteAllocation μ w.2
        (fun x j ↦ cost (x, w.1 j) + t * probe (x, w.1 j)) (alloc w)) :
    let R := (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)
    let mean := fun s ↦ ∫ w, semidiscreteValue μ
      (fun x j ↦ cost (x, w.1 j) + s * probe (x, w.1 j)) w.2 ∂R
    (∀ s, Integrable (fun w ↦ semidiscreteValue μ
      (fun x j ↦ cost (x, w.1 j) + s * probe (x, w.1 j)) w.2) R) ∧
    ∀ s, mean s ≤ mean t +
      (∫ w, ∫ e, probe e ∂physicalSceneGlobalAllocationFamily μ alloc Prod.fst w ∂R) * (s - t) := by
  intro R mean
  let ρ := Measure.pi (fun _ : Fin (n + 1) ↦ ν)
  let c := fun (y : Fin (n + 1) → M) j x ↦ cost (x, y j)
  let g := fun (y : Fin (n + 1) → M) j x ↦ probe (x, y j)
  have hcm (j : Fin (n + 1)) :
      Measurable (fun z : (Fin (n + 1) → M) × M ↦ c z.1 j z.2) :=
    hc.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  have hcint (j : Fin (n + 1)) :
      Integrable (fun z : (Fin (n + 1) → M) × M ↦ c z.1 j z.2) (ρ.prod μ) := by
    have hpair : MeasurePreserving (fun z : (Fin (n + 1) → M) × M ↦ (z.2, z.1 j))
        (ρ.prod μ) (μ.prod ν) :=
      Measure.measurePreserving_swap.comp
        ((measurePreserving_eval (fun _ : Fin (n + 1) ↦ ν) j).prod (MeasurePreserving.id μ))
    exact hpair.integrable_comp_of_integrable hci
  have hgm (j : Fin (n + 1)) :
      Measurable (fun z : (Fin (n + 1) → M) × M ↦ g z.1 j z.2) :=
    hg.comp (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  have hint (w : (Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) (j : Fin (n + 1)) :
      Integrable (fun x ↦ probe (x, w.1 j)) μ :=
    Integrable.of_bound (hg.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      G (ae_of_all _ fun x ↦ hbound x (w.1 j))
  have hq := integral_congr_ae (ae_originalGlobal_probe_integral_eq_allocationCost
    R μ alloc Prod.fst Prod.snd (hopt.mono fun _ h ↦ h.1) probe hg hint)
  constructor
  · intro s
    exact integrable_parameterized_dirichlet_semidiscreteValue_tilt μ ρ c g
      hcm hcint hgm hatom G (fun y x j ↦ hbound x (y j)) s
  · intro s
    rw [hq]
    have hsup := integral_semidiscreteValue_supergradient_of_tilted_optimal μ ρ c g
      hcm hcint hgm hatom G (fun y x j ↦ hbound x (y j))
      (fun z ↦ alloc z.1 z.2) halloc hopt s
    simpa only [mul_comm] using hsup

end OTSelector.Reconstruction
