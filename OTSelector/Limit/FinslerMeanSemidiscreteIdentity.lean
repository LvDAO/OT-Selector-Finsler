import OTSelector.Limit.FinslerPressureUpperBound

/-!
# The physical mean as a Dirichlet integral of the allocation value

The selector endpoint is stated with the full coupling value
`fullSemidiscreteValue`.  For almost every Dirichlet mass vector this equals the
allocation value `semidiscreteValue`, and for almost every iid target cloud the
target positions are distinct.  Integrating both facts identifies the physical
semidiscrete mean with a double integral of the allocation value over the target
cloud law and the Dirichlet law.

This identity is the deterministic platform for the expected supergradient
bound at every tilt.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Metric Filter OTSelector.Geometry
open OTSelector.Reconstruction OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

noncomputable section
universe u v

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false

/-- **Allocation-value form of the physical semidiscrete mean.** -/
theorem finslerSemidiscreteMean_eq_integral_semidiscreteValue
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) [NullSingletonClass (ν : Measure M)]
    (K : Set M) (hK : IsCompact K)
    (hμK : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hνK : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (pot : M → ℝ) (hpot : let _instIdentityMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 pot)
    (hcost : Integrable (Function.uncurry
      (fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x))
      ((μ : Measure M).prod (ν : Measure M)))
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) :
    let _instIdentityMetric : MetricSpace M := F.metricSpace
    let cost : M → M → ℝ := fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x
    let probe : M → M → ℝ := fun x y ↦ f (supportProjection μ K hK.measurableSet hμK x,
      supportProjection ν K hK.measurableSet hνK y)
    finslerSemidiscreteMean F μ ν K hK hμK hνK pot f t n =
      ∫ y : Fin (n + 1) → M, ∫ p,
        semidiscreteValue (μ : Measure M) (fun s j ↦
          ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
            cost s (y j) + t * probe s (y j)) p
        ∂dirichletOne n ∂Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instSecondCountable : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace _instProper
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  let _instMeasEq : MeasurableEq M := inferInstance
  dsimp only
  let cost : M → M → ℝ := fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x
  let probe : M → M → ℝ := fun x y ↦ f (supportProjection μ K hK.measurableSet hμK x,
    supportProjection ν K hK.measurableSet hνK y)
  have hpotL : LipschitzWith 1 pot := hpot
  have hcostm : Measurable (Function.uncurry cost) := F.measurable_distance_slack hpotL
  have hprobeM : Measurable (Function.uncurry probe) := by
    have hmap : Measurable (fun p : M × M ↦
        (supportProjection μ K hK.measurableSet hμK p.1,
          supportProjection ν K hK.measurableSet hνK p.2)) :=
      ((measurable_supportProjection μ K hK.measurableSet hμK).comp measurable_fst).prodMk
        ((measurable_supportProjection ν K hK.measurableSet hνK).comp measurable_snd)
    exact f.continuous.measurable.comp hmap
  have hprobe : ∀ x y, |probe x y| ≤ (‖f‖₊ : ℝ) := by
    intro x y
    have h := BoundedContinuousFunction.nnnorm_coe_le_nnnorm f
      (supportProjection μ K hK.measurableSet hμK x,
        supportProjection ν K hK.measurableSet hνK y)
    have h' : ((‖f (supportProjection μ K hK.measurableSet hμK x,
        supportProjection ν K hK.measurableSet hνK y)‖₊ : ℝ) ≤ (‖f‖₊ : ℝ)) :=
      NNReal.coe_le_coe.mpr h
    simpa only [probe, coe_nnnorm, Real.norm_eq_abs] using h'
  have hdim1 : 1 ≤ Module.finrank ℝ E := by omega
  have hqeq : ((Module.finrank ℝ E - 1 : ℕ) : ℝ) =
      (Module.finrank ℝ E : ℝ) - 1 := by
    rw [Nat.cast_sub hdim1]
    norm_num
  have hdim2 : 2 ≤ Module.finrank ℝ E := hdim
  have hcostν : Integrable (Function.uncurry cost) ((μ : Measure M).prod (ν : Measure M)) := hcost
  let ρ : Measure (Fin (n + 1) → M) := Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))
  let kval : ℝ := ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
  have hi : ∀ᵐ y ∂ρ, ∀ j, Integrable (fun x ↦ kval * cost x (y j)) (μ : Measure M) := by
    apply ae_all_iff.mpr
    intro j
    have hj := (measurePreserving_eval (fun _ : Fin (n + 1) ↦ (ν : Measure M)) j)
      |>.quasiMeasurePreserving
    exact hj.tendsto_ae.eventually ((hcostν.const_mul kval).prod_left_ae)
  have houter : (fun y : Fin (n + 1) → M ↦
      ∫ p, fullSemidiscreteValue (μ : Measure M) y (fun x y ↦
        kval * ((F.lengthEDist x y).toReal - pot y + pot x) + t * probe x y) p
        ∂dirichletOne n) =ᵐ[ρ]
      (fun y ↦ ∫ p, semidiscreteValue (μ : Measure M) (fun s j ↦
        kval * cost s (y j) + t * probe s (y j)) p ∂dirichletOne n) := by
    filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (n + 1)) (ν : Measure M),
      hi] with y hy hiy
    refine integral_congr_ae ?_
    have h := ae_fullSemidiscreteValue_eq_semidiscreteValue (μ : Measure M) y hy
      (fun x y ↦ kval * cost x y) probe
      (hcostm.const_mul kval) hiy hprobeM (‖f‖₊) hprobe t
    filter_upwards [h] with p hp
    simpa only [F.metricSpace_dist] using hp
  unfold finslerSemidiscreteMean
  dsimp only
  rw [← hqeq]
  exact integral_congr_ae houter

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
