import OTSelector.Reconstruction.FinslerGeneralUpperEnergy
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

/-- An actual positive transverse normalization has the physical quadratic scale. -/
theorem original_scale_sq_eq_count_rpow {q n : ℕ} (hq : 0 < q) {scale : ℝ}
    (hscale : 0 < scale) (hnormalization : scale ^ q = (n : ℝ) + 1) :
    scale ^ 2 = ((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ)) := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  calc scale ^ 2 = scale ^ ((q : ℝ) * (2 / (q : ℝ))) := by
        rw [mul_div_cancel₀ 2 hqR, Real.rpow_two]
    _ = (scale ^ (q : ℝ)) ^ (2 / (q : ℝ)) := Real.rpow_mul hscale.le _ _
    _ = ((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ)) := by
      rw [Real.rpow_natCast, hnormalization, Nat.cast_add, Nat.cast_one]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The SAME original potential, calibrated population and true Dirichlet
allocations produce one finite physical slack-energy bound for both signs of
every convergent tilt sequence. No allocation energy estimate is a premise. -/
theorem exists_original_global_dirichlet_allocation_energy
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
    (π : Measure (M × M)) [IsFiniteMeasure π] (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2)
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
  letI : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨C,hC,hbound⟩ := exists_uniform_original_finsler_energy hF hcomplete hdim hu ha hinj
    horder hA hB hAB hμA hνB hμreg hνreg π hπ hcal
  have hbound' : PopulationUniformEnergyBound μ ν (Module.finrank ℝ E - 1)
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x) C := hbound
  obtain ⟨T,hT,habs⟩ := (Metric.isBounded_range_of_tendsto tilt htilt).exists_pos_norm_le
  let Energy : ℝ≥0∞ := ENNReal.ofReal (C + 2 * T * (G : ℝ))
  refine ⟨Energy,ENNReal.ofReal_ne_top,?_⟩
  intro ℓ n t ht allocation hm hopt
  have hfeas := hopt.mono fun w hw ↦ hw.1
  have hqdim : finrank ℝ W.seed.covector.ker = finrank ℝ E - 1 := by
    have hh : finrank ℝ W.seed.covector.ker + 1 = finrank ℝ E := by
      simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using
        W.seed.normalization.toLinearEquiv.finrank_eq
    omega
  have hqpos : 0 < finrank ℝ W.seed.covector.ker := by omega
  have hscaleEq : scale n ^ 2 = ((n + 1 : ℕ) : ℝ) ^ (2 / ((finrank ℝ E - 1 : ℕ) : ℝ)) := by
    rw [← hqdim]
    exact original_scale_sq_eq_count_rpow hqpos (hscale n) (hnormalization n)
  let allocation' := fun y w x j ↦ allocation (y,w) x j
  have henergy := finsler_given_potential_dirichlet_plan_energy_le hF hcomplete (by omega)
    m μ ν hμchart hνchart hA hB hμA hνB u hu C hbound' n probe G hprobe hprobeBound t
    allocation' hm hfeas (hopt.mono fun w hw d hd ↦ by
      simpa only [hscaleEq, allocation'] using hw.2 d hd)
  have heq := lintegral_physicalSceneGlobalAllocationFamily_eq
    ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ allocation
    (fun w ↦ w.1) (fun w ↦ w.2) hfeas
    (fun _ p ↦ ENNReal.ofReal (scale n ^ 2 *
      ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)))
    (fun _ ↦ ((F.measurable_distance_slack hu).const_mul (scale n ^ 2)).ennreal_ofReal)
  rw [heq]
  have htBound : |t| ≤ T := by
    have h := habs (tilt ℓ) (mem_range_self ℓ)
    rcases ht with rfl | rfl <;> simpa only [Real.norm_eq_abs, abs_neg] using h
  have henergy' : (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale n ^ 2 *
      ((F.lengthEDist p.1 (w.1 p.2)).toReal - u (w.1 p.2) + u p.1))
      ∂semidiscreteAllocationMeasure μ (allocation w)
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤
      ENNReal.ofReal (C + 2 * |t| * (G : ℝ)) := by
    simpa only [allocation', hscaleEq] using henergy
  have hnum : C + 2 * |t| * (G : ℝ) ≤ C + 2 * T * (G : ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_right htBound G.coe_nonneg]
  exact henergy'.trans (ENNReal.ofReal_le_ofReal hnum)

end OTSelector.Reconstruction
