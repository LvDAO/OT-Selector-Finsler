import OTSelector.Reconstruction.FinslerPhysicalSceneCoordinates
import OTSelector.Geometry.FinslerPressureAssumptionAdapters
import OTSelector.Transport.Semidiscrete.OppositeOptima
import OTSelector.Probability.CavitySemidiscreteEnergyBridge
import OTSelector.Probability.CavitySemidiscretePrimal

/-!
# Physical allocation and cost transport to actual seed scenes

The exact observation and reconstruction laws transport allocations and their
full objectives.  The optimality theorem compares every fractional competitor,
using the original almost-everywhere inverse.  Scaled original distance-slack
differences are atomless on the same coordinate source law.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

section Allocation

variable {X S : Type*} [MeasurableSpace X] [MeasurableSpace S] {m : ℕ}
  {μ : Measure X} {ν : Measure S} {physical : S → X}

/-- An allocation pulls back along an exact measurable physical observation. -/
theorem semidiscreteAllocation_comp_of_map
    (hp : Measurable physical) (hmap : ν.map physical = μ)
    {p : Fin (m + 1) → ℝ} {a : X → Fin (m + 1) → ℝ}
    (ha : OTSelector.Probability.IsSemidiscreteAllocation μ p a) :
    OTSelector.Probability.IsSemidiscreteAllocation ν p (fun s ↦ a (physical s)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    have hi : Integrable (fun x ↦ a x j) (ν.map physical) := hmap.symm ▸ ha.integrable j
    exact hi.comp_measurable hp
  · apply ae_of_ae_map (p := fun x ↦ ∀ j, 0 ≤ a x j) hp.aemeasurable
    simpa only [hmap] using ha.nonneg
  · apply ae_of_ae_map (p := fun x ↦ ∑ j, a x j = 1) hp.aemeasurable
    simpa only [hmap] using ha.sum_one
  · intro j
    have hi : Integrable (fun x ↦ a x j) (ν.map physical) := hmap.symm ▸ ha.integrable j
    calc
      ∫ s, a (physical s) j ∂ν = ∫ x, a x j ∂ν.map physical :=
        (integral_map hp.aemeasurable hi.aestronglyMeasurable).symm
      _ = p j := by rw [hmap]; exact ha.mass j

/-- Every integrable original cost, including a bounded physical probe, has
exactly the same allocation objective in the actual scene coordinates. -/
theorem semidiscreteAllocationCost_comp_of_map
    (hp : Measurable physical) (hmap : ν.map physical = μ)
    {p : Fin (m + 1) → ℝ} {a : X → Fin (m + 1) → ℝ}
    (ha : OTSelector.Probability.IsSemidiscreteAllocation μ p a)
    (c : X → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun x ↦ c x j) μ) :
    OTSelector.Probability.semidiscreteAllocationCost ν
        (fun s j ↦ c (physical s) j) (fun s ↦ a (physical s)) =
      OTSelector.Probability.semidiscreteAllocationCost μ c a := by
  have hi : Integrable (fun x ↦ ∑ j, a x j * c x j) μ :=
    integrable_finsetSum _ fun j _ ↦ ha.integrable_mul c hc j
  have him : AEStronglyMeasurable (fun x ↦ ∑ j, a x j * c x j) (ν.map physical) :=
    hmap.symm ▸ hi.aestronglyMeasurable
  unfold OTSelector.Probability.semidiscreteAllocationCost
  rw [← hmap]
  exact (integral_map hp.aemeasurable him).symm

/-- The complete sets of feasible fractional objectives agree under the actual
coordinate observation and physical inverse. -/
theorem semidiscrete_objectives_comp_of_inverse
    (hp : Measurable physical) (hmap : ν.map physical = μ)
    (coord : X → S) (hq : Measurable coord) (hqmap : μ.map coord = ν)
    (hinverse : ∀ᵐ x ∂μ, physical (coord x) = x)
    (p : Fin (m + 1) → ℝ) (c : X → Fin (m + 1) → ℝ)
    (hc : ∀ j, Integrable (fun x ↦ c x j) μ) :
    OTSelector.Probability.semidiscreteAllocationCost ν (fun s j ↦ c (physical s) j) ''
        {a | OTSelector.Probability.IsSemidiscreteAllocation ν p a} =
      OTSelector.Probability.semidiscreteAllocationCost μ c ''
        {a | OTSelector.Probability.IsSemidiscreteAllocation μ p a} := by
  ext z
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hdq := semidiscreteAllocation_comp_of_map hq hqmap hd
    refine ⟨fun x ↦ d (coord x), hdq, ?_⟩
    have hcc (j : Fin (m + 1)) : Integrable (fun s ↦ c (physical s) j) ν := by
      have hi : Integrable (fun x ↦ c x j) (ν.map physical) := hmap.symm ▸ hc j
      exact hi.comp_measurable hp
    rw [← semidiscreteAllocationCost_comp_of_map hq hqmap hd
      (fun s j ↦ c (physical s) j) hcc]
    apply integral_congr_ae
    filter_upwards [hinverse] with x hx
    simp only [hx]
  · rintro ⟨d, hd, rfl⟩
    exact ⟨fun s ↦ d (physical s), semidiscreteAllocation_comp_of_map hp hmap hd,
      semidiscreteAllocationCost_comp_of_map hp hmap hd c hc⟩

/-- The actual physical semidiscrete pressure is preserved at every target-mass
vector, through equality of all fractional objective values. -/
theorem semidiscreteValue_comp_of_inverse
    (hp : Measurable physical) (hmap : ν.map physical = μ)
    (coord : X → S) (hq : Measurable coord) (hqmap : μ.map coord = ν)
    (hinverse : ∀ᵐ x ∂μ, physical (coord x) = x)
    (p : Fin (m + 1) → ℝ) (c : X → Fin (m + 1) → ℝ)
    (hc : ∀ j, Integrable (fun x ↦ c x j) μ) :
    OTSelector.Probability.semidiscreteValue ν (fun s j ↦ c (physical s) j) p =
      OTSelector.Probability.semidiscreteValue μ c p :=
  congrArg sInf (semidiscrete_objectives_comp_of_inverse hp hmap coord hq hqmap
    hinverse p c hc)

/-- Observing source and target coordinates preserves the full physical coupling
pressure of a distinct target cloud. -/
theorem fullSemidiscreteValue_comp_of_inverse
    {Y T : Type*} [MeasurableSpace Y] [MeasurableSpace T]
    [MeasurableSingletonClass Y] [MeasurableSingletonClass T]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hp : Measurable physical) (hmap : ν.map physical = μ)
    (coord : X → S) (hq : Measurable coord) (hqmap : μ.map coord = ν)
    (hinverse : ∀ᵐ x ∂μ, physical (coord x) = x)
    (target : T → Y) (ht : Measurable target)
    (cloud : Fin (m + 1) → T) (hcloud : Injective (target ∘ cloud))
    (c : X → Y → ℝ) (hcm : Measurable (Function.uncurry c))
    (hc : ∀ j, Integrable (fun x ↦ c x (target (cloud j))) μ)
    (p : Fin (m + 1) → ℝ) (hpm : ∀ j, 0 ≤ p j) :
    OTSelector.Probability.fullSemidiscreteValue ν cloud
        (fun s y ↦ c (physical s) (target y)) p =
      OTSelector.Probability.fullSemidiscreteValue μ (target ∘ cloud) c p := by
  have hcloud' : Injective cloud := by
    intro j l he
    exact hcloud (congrArg target he)
  have hcc (j : Fin (m + 1)) :
      Integrable (fun s ↦ c (physical s) (target (cloud j))) ν := by
    have hi : Integrable (fun x ↦ c x (target (cloud j))) (ν.map physical) :=
      hmap.symm ▸ hc j
    exact hi.comp_measurable hp
  rw [OTSelector.Probability.fullSemidiscreteValue_eq_semidiscreteValue ν cloud hcloud'
      (fun s y ↦ c (physical s) (target y)) (hcm.comp (hp.prodMap ht)) hcc p hpm,
    OTSelector.Probability.fullSemidiscreteValue_eq_semidiscreteValue μ
      (target ∘ cloud) hcloud c hcm hc p hpm]
  exact semidiscreteValue_comp_of_inverse hp hmap coord hq hqmap hinverse p
    (fun x j ↦ c x (target (cloud j))) hc

/-- The full fractional optimum transports through the actual observation and
its physical inverse.  Every coordinate competitor is compared. -/
theorem optimalSemidiscreteAllocation_comp_of_inverse
    (hp : Measurable physical) (hmap : ν.map physical = μ)
    (coord : X → S) (hq : Measurable coord) (hqmap : μ.map coord = ν)
    (hinverse : ∀ᵐ x ∂μ, physical (coord x) = x)
    {p : Fin (m + 1) → ℝ} {a : X → Fin (m + 1) → ℝ}
    (c : X → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun x ↦ c x j) μ)
    (ha : OTSelector.Probability.IsOptimalSemidiscreteAllocation μ p c a) :
    OTSelector.Probability.IsOptimalSemidiscreteAllocation ν p
      (fun s j ↦ c (physical s) j) (fun s ↦ a (physical s)) := by
  have hac := semidiscreteAllocation_comp_of_map hp hmap ha.1
  refine ⟨hac, fun d hd ↦ ?_⟩
  have hdq := semidiscreteAllocation_comp_of_map hq hqmap hd
  have hcc (j : Fin (m + 1)) : Integrable (fun s ↦ c (physical s) j) ν := by
    have hi : Integrable (fun x ↦ c x j) (ν.map physical) := hmap.symm ▸ hc j
    exact hi.comp_measurable hp
  have hcostd := semidiscreteAllocationCost_comp_of_map hq hqmap hd
    (fun s j ↦ c (physical s) j) hcc
  have heq : OTSelector.Probability.semidiscreteAllocationCost μ
      (fun x j ↦ c (physical (coord x)) j) (fun x ↦ d (coord x)) =
        OTSelector.Probability.semidiscreteAllocationCost μ c (fun x ↦ d (coord x)) := by
    apply integral_congr_ae
    filter_upwards [hinverse] with x hx
    simp only [hx]
  rw [semidiscreteAllocationCost_comp_of_map hp hmap ha.1 c hc, ← hcostd, heq]
  exact ha.2 _ hdq

/-- Original nonnegative allocation energy becomes the same scene-plan
lintegral.  This converts a physical real-energy estimate without a new
coercivity assumption. -/
theorem lintegral_scene_allocation_energy_eq
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hp : Measurable physical) (hmap : ν.map physical = μ)
    {p : Fin (m + 1) → ℝ} {a : X → Fin (m + 1) → ℝ}
    (ha : OTSelector.Probability.IsSemidiscreteAllocation μ p a)
    (c : X → Fin (m + 1) → ℝ)
    (hcm : Measurable (Function.uncurry c))
    (hc : ∀ j, Integrable (fun x ↦ c x j) μ)
    (hcn : ∀ᵐ x ∂μ, ∀ j, 0 ≤ c x j) :
    (∫⁻ e, ENNReal.ofReal (c (physical e.1) e.2)
      ∂OTSelector.Probability.semidiscreteAllocationMeasure ν (fun s ↦ a (physical s))) =
        ENNReal.ofReal (OTSelector.Probability.semidiscreteAllocationCost μ c a) := by
  have hac := semidiscreteAllocation_comp_of_map hp hmap ha
  have hci (j : Fin (m + 1)) : Integrable (fun s ↦ c (physical s) j) ν := by
    have hi : Integrable (fun x ↦ c x j) (ν.map physical) := hmap.symm ▸ hc j
    exact hi.comp_measurable hp
  have hcc : Measurable (Function.uncurry (fun s j ↦ c (physical s) j)) :=
    hcm.comp (hp.prodMap measurable_id)
  have hnc : ∀ᵐ s ∂ν, ∀ j, 0 ≤ c (physical s) j := by
    apply ae_of_ae_map (p := fun x ↦ ∀ j, 0 ≤ c x j) hp.aemeasurable
    simpa only [hmap] using hcn
  rw [OTSelector.Probability.lintegral_ofReal_semidiscreteAllocationCost ν
    (fun s ↦ a (physical s)) hac (fun s j ↦ c (physical s) j) hcc hci hnc,
    semidiscreteAllocationCost_comp_of_map hp hmap ha c hc]

end Allocation

section OriginalSlack

variable {E M S : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace S] {F : ContinuousFinslerNorm E M}

/-- The same original physical slack is atomless on an actual coordinate source
law recovering a normalized physical restriction.  Source potential values
cancel, so the potential needs no additional regularity. -/
theorem nullSingletonClass_scene_scaled_distanceSlack_sub
    (hF : F.IsSmoothStronglyConvex)
    (m : Measure E) [m.IsAddHaarMeasure] (μ : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (H : Set M) (ν : Measure S) (physical : S → M) (hp : Measurable physical)
    (hmap : ν.map physical = normalizedFiniteLaw (μ.restrict H))
    (φ : M → ℝ) {k : ℝ} (hk : k ≠ 0) {y z : M} (hyz : y ≠ z) :
    let _instSceneSlackMetric : MetricSpace M := F.metricSpace
    NullSingletonClass (ν.map (fun s ↦
      k * (dist (physical s) y - φ y + φ (physical s)) -
        k * (dist (physical s) z - φ z + φ (physical s)))) := by
  let _instSceneSlackMetric : MetricSpace M := F.metricSpace
  let g : M → ℝ := fun x ↦
    k * (dist x y - φ y + φ x) - k * (dist x z - φ z + φ x)
  have hg : Measurable g := by
    have heq : g = fun x ↦ k * ((dist x y - dist x z) - φ y + φ z) := by
      funext x
      dsimp only [g]
      ring
    rw [heq]
    exact ((((continuous_id.dist continuous_const).sub
      (continuous_id.dist continuous_const)).sub continuous_const).add
        continuous_const).const_mul k |>.measurable
  have hres : NullSingletonClass ((μ.restrict H).map g) :=
    hF.nullSingletonClass_map_scaled_distanceSlack_sub_restrict m μ hdim hchart
      hcomplete φ hk hyz H
  have hnorm : NullSingletonClass ((normalizedFiniteLaw (μ.restrict H)).map g) := by
    rw [normalizedFiniteLaw, Measure.map_smul]
    refine ⟨fun z ↦ ?_⟩
    simp only [Measure.smul_apply, hres.measure_singleton z, smul_zero]
  change NullSingletonClass (ν.map (g ∘ physical))
  rw [← Measure.map_map hg hp, hmap]
  exact hnorm

end OriginalSlack
end OTSelector.Reconstruction
