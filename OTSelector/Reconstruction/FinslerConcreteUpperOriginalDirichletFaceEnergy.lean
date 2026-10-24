import OTSelector.Reconstruction.FinslerConcreteUpperOriginalDirichletEnergy
import OTSelector.Geometry.Finsler.Calibration.OptimalFaceCarrier
import OTSelector.Transport.Coupling.OptimalPlanExistence
import OTSelector.Reconstruction.PopulationUniformEnergyBound
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutFixedEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedGlobal
import Mathlib.Analysis.Normed.Group.Bounded

/-! The original empirical atlas supplies the actual Dirichlet physical-plan energy. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The original whole-face representation supplies its own calibrated optimizer,
so actual positive and negative Dirichlet allocations have finite uniform energy
without an energy or calibrated-plan input. The original potential is retained. -/
theorem exists_original_global_dirichlet_allocation_energy_of_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → (ℚ → M)} (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    (W : F.CalibratedSeedWindow u)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hnormalization : ∀ n, scale n ^ finrank ℝ W.seed.covector.ker = (n : ℝ) + 1)
    (probe : M → M → ℝ) (hprobe : Measurable (Function.uncurry probe))
    (G : ℝ≥0) (hprobeBound : ∀ x y, |probe x y| ≤ G)
    (tilt : ℕ → ℝ) (htilt : Tendsto tilt atTop (𝓝 0)) :
    ∃ Energy : ℝ≥0∞, Energy ≠ ⊤ ∧ ∀ (ℓ n : ℕ) (t : ℝ),
      (t = tilt ℓ ∨ t = -tilt ℓ) →
      ∀ allocation : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ,
      (∀ j, Measurable (fun z : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦
        allocation z.1 z.2 j)) →
      (∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
        IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
          scale n ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
            t * probe x (w.1 j)) (allocation w)) →
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ allocation (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : StandardBorelSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨π,hπ⟩ := exists_isOptimalCoupling_edist_of_compact_carrier μ ν (hA.union hB)
    (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
  letI : IsProbabilityMeasure (π.map Prod.fst) := hπ.1.1.symm ▸ inferInstance
  letI : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  have hcarried := ae_original_regular_sameLabel_forward_of_optimal_face hF hcomplete hu ha hface hπ
  have hcal : ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2 :=
    hcarried.mono fun p hp ↦ (horder p.1 hp.1 p.2 hp.2.1).mp ⟨hp.2.2.1,hp.2.2.2⟩
  exact exists_original_global_dirichlet_allocation_energy hF hcomplete hdim hu ha hinj horder
    m hμchart hνchart hA hB hAB hμA hνB hμreg hνreg π hπ.1 hcal
    W scale hscale hnormalization probe hprobe G hprobeBound tilt htilt

end OTSelector.Reconstruction
