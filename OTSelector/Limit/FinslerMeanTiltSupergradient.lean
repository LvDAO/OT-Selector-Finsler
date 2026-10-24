import OTSelector.Limit.FinslerMeanSemidiscreteIdentity
import OTSelector.Probability.CavityExpectedTiltSupergradient

/-!
# Supergradients of the physical semidiscrete mean at every tilt

The physical mean is, by `finslerSemidiscreteMean_eq_integral_semidiscreteValue`,
the Dirichlet integral of the allocation value with base slack cost and probe.
A jointly measurable optimal allocation for the tilted cost therefore gives the
expected probe cost as a supergradient of the mean at that tilt.

Tilt-specific atomlessness of the tilted cost differences is the only stochastic
input; for the model cost it holds away from a countable exceptional set of
tilts (`countable_bad_parameterized_cavity_tilts`).
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

/-- The Finsler distance-slack edge cost. -/
noncomputable def finslerSlackCost (F : ContinuousFinslerNorm E M) (pot : M → ℝ) :
    M → M → ℝ :=
  fun x y ↦ (F.lengthEDist x y).toReal - pot y + pot x

/-- The microscopic scale `(n + 1)^(2/(dim - 1))` of the physical mean. -/
noncomputable def finslerMeanScale (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))

/-- The compact-carrier probe, extended by the measurable support projections. -/
noncomputable def finslerCarrierProbe (μ ν : ProbabilityMeasure M) (K : Set M)
    (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (f : (K × K) →ᵇ ℝ) : M → M → ℝ :=
  fun x y ↦ f (supportProjection μ K hK hμ x, supportProjection ν K hK hν y)

set_option backward.isDefEq.respectTransparency false

/-- **Expected tilt supergradients of the physical mean.**  Away from tilts whose
pairwise cost differences are atomic on the source law, there is a jointly
measurable optimal allocation whose expected probe cost is a supergradient of the
physical semidiscrete mean at that tilt. -/
theorem exists_finslerSemidiscreteMean_tilt_supergradient
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) [NullSingletonClass (ν : Measure M)]
    (K : Set M) (hK : IsCompact K)
    (hμK : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hνK : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (pot : M → ℝ) (hpot : let _instSupergradientMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 pot)
    (f : (K × K) →ᵇ ℝ) (n : ℕ) (t : ℝ)
    (hcost : Integrable (Function.uncurry (finslerSlackCost F pot))
      ((μ : Measure M).prod (ν : Measure M)))
    (hhat : ∀ᵐ y ∂(Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ : Measure M).map (fun s ↦ finslerMeanScale E n *
          (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l)))))
    (htilt : ∀ᵐ y ∂(Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ : Measure M).map (fun s ↦
          finslerMeanScale E n *
              (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l)) +
            t * (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y j) -
              finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y l))))) :
    let _instSupergradientMetric : MetricSpace M := F.metricSpace
    ∃ (A : (((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M) → Fin (n + 1) → ℝ)
      (q : ℝ),
      (∀ j, Measurable (fun z ↦ A z j)) ∧
      (∀ u : ℝ, finslerSemidiscreteMean F μ ν K hK hμK hνK pot f u n ≤
        finslerSemidiscreteMean F μ ν K hK hμK hνK pot f t n + (u - t) * q) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instSecondCountable : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace _instProper
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  let _instMeasEq : MeasurableEq M := inferInstance
  dsimp only
  let V := Fin (n + 1) → M
  let ρ : Measure V := Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))
  let cost : M → M → ℝ := finslerSlackCost F pot
  let probe : M → M → ℝ := finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f
  let kval : ℝ := finslerMeanScale E n
  let base : V → Fin (n + 1) → M → ℝ := fun y j s ↦ kval * cost s (y j)
  let g : V → Fin (n + 1) → M → ℝ := fun y j s ↦ probe s (y j)
  let ctilt : V → Fin (n + 1) → M → ℝ := fun y j s ↦ base y j s + t * g y j s
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
    simpa only [probe, finslerCarrierProbe, coe_nnnorm, Real.norm_eq_abs] using h'
  -- Measurability and joint integrability of the base and tilted costs.
  have hbase_meas (j : Fin (n + 1)) : Measurable (fun z : V × M ↦ base z.1 j z.2) := by
    have hpair : Measurable (fun z : V × M ↦ (z.2, z.1 j)) :=
      measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst)
    exact ((hcostm.comp hpair).const_mul kval)
  have hbase_int (j : Fin (n + 1)) : Integrable (fun z : V × M ↦ base z.1 j z.2)
      (ρ.prod (μ : Measure M)) := by
    have hpair : MeasurePreserving (fun z : V × M ↦ (z.2, z.1 j))
        (ρ.prod (μ : Measure M)) ((μ : Measure M).prod (ν : Measure M)) :=
      Measure.measurePreserving_swap.comp
        ((measurePreserving_eval (fun _ : Fin (n + 1) ↦ (ν : Measure M)) j).prod
          (MeasurePreserving.id (μ : Measure M)))
    exact (hpair.integrable_comp_of_integrable hcost).const_mul kval
  have hg_meas (j : Fin (n + 1)) : Measurable (fun z : V × M ↦ g z.1 j z.2) := by
    have hpair : Measurable (fun z : V × M ↦ (z.2, z.1 j)) :=
      measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst)
    exact hprobeM.comp hpair
  have hg_int (j : Fin (n + 1)) : Integrable (fun z : V × M ↦ g z.1 j z.2)
      (ρ.prod (μ : Measure M)) :=
    (integrable_const (‖f‖₊ : ℝ)).mono' (hg_meas j).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ by
        simpa only [Real.norm_eq_abs] using hprobe z.2 (z.1 j))
  have hctilt_meas (j : Fin (n + 1)) : Measurable (fun z : V × M ↦ ctilt z.1 j z.2) :=
    (hbase_meas j).add ((hg_meas j).const_mul t)
  have hctilt_int : ∀ᵐ y ∂ρ, ∀ j, Integrable (ctilt y j) (μ : Measure M) := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [(hbase_int j).prod_right_ae, (hg_int j).prod_right_ae] with y hb hgv
    exact (hb.add (hgv.const_mul t)).congr (Eventually.of_forall fun s => by simp only [ctilt]; rfl)
  -- A jointly measurable optimal allocation for the tilted cost.
  have htilt' : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l → NullSingletonClass
      ((μ : Measure M).map (fun s ↦ ctilt v j s - ctilt v l s)) := by
    filter_upwards [htilt] with y hy j l hjl
    have heq : (fun s ↦ ctilt y j s - ctilt y l s) =
        (fun s ↦ finslerMeanScale E n *
            (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l)) +
          t * (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y j) -
            finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y l))) := by
      funext s
      simp only [ctilt, base, g, kval, cost, mul_sub]
      ring
    rw [heq]
    exact hy j l hjl
  have hhat' : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l → NullSingletonClass
      ((μ : Measure M).map (fun s ↦ base v j s - base v l s)) := by
    filter_upwards [hhat] with y hy j l hjl
    have heq : (fun s ↦ base y j s - base y l s) =
        (fun s ↦ finslerMeanScale E n *
          (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l))) := by
      funext s
      simp only [base, kval, cost, mul_sub]
    rw [heq]
    exact hy j l hjl
  obtain ⟨A, hA, hopt⟩ :=
    exists_jointlyMeasurable_parameterized_dirichlet_optimalAllocation
      (μ := (μ : Measure M)) (ρ := ρ) (c := ctilt) hctilt_meas hctilt_int htilt'
  have hopt' : ∀ᵐ z ∂ρ.prod (dirichletOne n),
      IsOptimalSemidiscreteAllocation (μ : Measure M) z.2
        (fun s j ↦ base z.1 j s + t * g z.1 j s) (fun s ↦ A (z, s)) := by
    filter_upwards [hopt] with z hz
    simpa only [ctilt] using hz.1
  refine ⟨A, (∫ z : V × (Fin (n + 1) → ℝ),
      semidiscreteAllocationCost (μ : Measure M) (fun s j ↦ g z.1 j s)
        (fun s ↦ A (z, s)) ∂ρ.prod (dirichletOne n)), hA, ?_⟩
  intro u
  have hsup := integral_semidiscreteValue_supergradient_of_tilted_optimal
    (μ := (μ : Measure M)) (ρ := ρ) (c := base) (g := g)
    hbase_meas hbase_int hg_meas hhat' (‖f‖₊) (fun y s j ↦ hprobe s (y j))
    A hA (t := t) hopt'
  dsimp only at hsup
  have hmean_u := finslerSemidiscreteMean_eq_integral_semidiscreteValue hF hcomplete m hdim
    μ ν K hK hμK hνK pot hpot f u n (hcost := hcost)
  have hmean_t := finslerSemidiscreteMean_eq_integral_semidiscreteValue hF hcomplete m hdim
    μ ν K hK hμK hνK pot hpot f t n (hcost := hcost)
  dsimp only [finslerSlackCost, finslerCarrierProbe, finslerMeanScale, kval] at hmean_u hmean_t
  have hjoint_u := integrable_parameterized_dirichlet_semidiscreteValue_tilt
    (μ := (μ : Measure M)) (ρ := ρ) (c := base) (g := g)
    hbase_meas hbase_int hg_meas hhat' (‖f‖₊) (fun y s j ↦ hprobe s (y j)) u
  have hjoint_t := integrable_parameterized_dirichlet_semidiscreteValue_tilt
    (μ := (μ : Measure M)) (ρ := ρ) (c := base) (g := g)
    hbase_meas hbase_int hg_meas hhat' (‖f‖₊) (fun y s j ↦ hprobe s (y j)) t
  have hprod_u : (∫ y : V, ∫ p, semidiscreteValue (μ : Measure M)
        (fun s j ↦ base y j s + u * g y j s) p ∂dirichletOne n ∂ρ) =
      ∫ z : V × (Fin (n + 1) → ℝ), semidiscreteValue (μ : Measure M)
        (fun s j ↦ base z.1 j s + u * g z.1 j s) z.2 ∂ρ.prod (dirichletOne n) :=
    (integral_prod _ hjoint_u).symm
  have hprod_t : (∫ y : V, ∫ p, semidiscreteValue (μ : Measure M)
        (fun s j ↦ base y j s + t * g y j s) p ∂dirichletOne n ∂ρ) =
      ∫ z : V × (Fin (n + 1) → ℝ), semidiscreteValue (μ : Measure M)
        (fun s j ↦ base z.1 j s + t * g z.1 j s) z.2 ∂ρ.prod (dirichletOne n) :=
    (integral_prod _ hjoint_t).symm
  simp only [base, g, finslerMeanScale, finslerSlackCost, finslerCarrierProbe, kval, cost] at hmean_u hmean_t ⊢
  simp only [ρ, V, probe, base, g, finslerMeanScale, finslerSlackCost, finslerCarrierProbe, kval, cost] at hprod_u hprod_t
  rw [hmean_u, hmean_t, hprod_u, hprod_t]
  exact hsup u

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
