import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetPhysical
import OTSelector.Reconstruction.FinslerOriginalChosenPopulationAtlas
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalDirichletFaceEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalCanonicalSceneScale

/-! A genuine original iid physical energy budget for the same chosen population potential. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped ENNReal NNReal Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The original whole-optimal-face representation produces its own calibrated plan
and one physical iid energy budget, retaining this same potential and every particle.
The same constant also controls the entire measurable fractional tilted optimal face. -/
theorem exists_original_iid_physical_energy_of_same_face
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ finrank ℝ E)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → (ℚ → M)} (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
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
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2) :
    let q := finrank ℝ E-1
    let cost := fun x y ↦ (F.lengthEDist x y).toReal-u y+u x
    ∃ C : ℝ, 0 < C ∧ PopulationUniformEnergyBound μ ν q cost C ∧
      ∀ (g : M × M →ᵇ ℝ) (t : ℝ) (n : ℕ),
        let k := (physicalSceneCanonicalHaarScale q n)^2
        (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (k*cost p.1 p.2)
          ∂originalIIDOptimalPhysicalPlan (n := n+1) (fun x y ↦ k*cost x y+t*g (x,y)) 1 ξ
          ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤
          ENNReal.ofReal (C+2 * |t| * ‖g‖) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : StandardBorelSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  intro q cost
  obtain ⟨π,hπ⟩ := exists_isOptimalCoupling_edist_of_compact_carrier μ ν (hA.union hB)
    (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
  letI : IsProbabilityMeasure (π.map Prod.fst) := hπ.1.1.symm ▸ inferInstance
  letI : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  have hcarried := ae_original_regular_sameLabel_forward_of_optimal_face hF hcomplete hu ha hface hπ
  have hcal : ∀ᵐ p ∂π, u p.2-u p.1 = dist p.1 p.2 :=
    hcarried.mono fun p hp ↦ (horder p.1 hp.1 p.2 hp.2.1).mp ⟨hp.2.2.1,hp.2.2.2⟩
  obtain ⟨C,hC,henergy⟩ := exists_uniform_original_finsler_energy hF hcomplete hdim hu ha hinj
    horder hA hB hAB hμA hνB hμreg hνreg π hπ.1 hcal
  have hcost : Measurable (Function.uncurry cost) := F.measurable_distance_slack hu
  have hnonneg (x y : M) : 0 ≤ cost x y := by
    have h := hu.le_add_mul y x
    simp only [NNReal.coe_one, one_mul, dist_comm y x] at h
    change 0 ≤ dist x y-u y+u x
    linarith
  refine ⟨C,hC,henergy,?_⟩
  intro g t n
  have hscale : (physicalSceneCanonicalHaarScale q n)^2 =
      ((n+1 : ℕ) : ℝ) ^ (2/(q : ℝ)) := original_scale_sq_eq_count_rpow
    (by dsimp [q]; omega) (physicalSceneCanonicalHaarScale_pos q n)
    (physicalSceneCanonicalHaarScale_pow q (by dsimp [q]; omega) n)
  dsimp only
  rw [hscale]
  exact lintegral_originalIID_tiltedPhysicalPlan_base_energy_le μ ν cost hcost hnonneg henergy
    (fun x y ↦ g (x,y)) g.continuous.measurable ‖g‖
    (fun x y ↦ by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm (x,y)) t n

/-- The SAME chosenPopulationPotential_atlas supplies the uniform actual iid budget.
No new population potential, calibrated plan or energy bound is supplied. -/
theorem chosenPopulationPotential_original_iid_physical_energy
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ y ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)), y ∈ B) :
    let u := chosenPopulationPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
      hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
    let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
    let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
    let q := finrank ℝ E-1
    let cost := fun x y ↦ (F.lengthEDist x y).toReal-u y+u x
    ∃ C : ℝ, 0 < C ∧ PopulationUniformEnergyBound μ ν q cost C ∧
      ∀ (g : M × M →ᵇ ℝ) (t : ℝ) (n : ℕ),
        let k := (physicalSceneCanonicalHaarScale q n)^2
        (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (k*cost p.1 p.2)
          ∂originalIIDOptimalPhysicalPlan (n := n+1) (fun x y ↦ k*cost x y+t*g (x,y)) 1 ξ
          ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤
          ENNReal.ofReal (C+2 * |t| * ‖g‖) := by
  let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let u := chosenPopulationPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
    hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  have hatlas := chosenPopulationPotential_atlas
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
      hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  dsimp only [ChosenWitnessSpec] at hatlas
  obtain ⟨a, hu, _hN, hμreg, hνreg, ha, hinj, horder, _hbalance, hface, _tail⟩ := hatlas
  exact exists_original_iid_physical_energy_of_same_face hF hcomplete hdim hu ha hinj horder
    hA hB hAB hμ hν hμreg hνreg hface

end OTSelector.Reconstruction
