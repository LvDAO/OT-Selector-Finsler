import OTSelector.Limit.FinslerMeanSemidiscreteIdentity
import OTSelector.Limit.FinslerMeanTiltSupergradient
import OTSelector.Probability.CavityMarkProbeSupergradientAssembly
import OTSelector.Probability.CavitySemidiscretePressureJoint

/-!
# The physical mean as a cavity pressure on the trivial spatial coordinate

This module instantiates the cavity mark-probe model on the trivial spatial
coordinate `Unit → ℝ`, with source and target marks pushed to the zero spatial
slice, and identifies the resulting cavity pressure with the physical Finsler
semidiscrete mean.

## Main results

* `cavityZeroSlice` / `cavityZeroSliceMeasure`: the zero-slice embedding
  `M → (Unit → ℝ) × M` and its pushforward on measures;
* `ae_map_cavityZeroSlice_iff`: a.e. transfer along the zero-slice embedding,
  valid for arbitrary predicates because the embedding is measurable;
* `semidiscreteValue_cavityZeroSlice`: pushing a measure to the zero slice
  preserves the semidiscrete value whenever the cost ignores the spatial
  coordinate;
* `map_pi_cavityZeroSlice_prod`: the target-cloud product measure pushes
  forward along the mark projection to the physical target-cloud law;
* `finslerMeanCavityCost`: the level-`n` physical slack cost
  `finslerMeanScale E n * finslerSlackCost F pot`, as a cavity cost ignoring the
  spatial coordinate;
* `finslerSemidiscreteMean_eq_cavityMarkProbePressure`: the physical mean equals
  the cavity mark-probe pressure at every tilt (with the level-`n` scaled cost,
  and under the base atomlessness hypothesis already used by the physical
  supergradient theorem);
* `finslerSemidiscreteMean_supergradients_with_readout`: the physical
  plus/minus supergradient inequalities with the supergradient values identified
  with the cavity mark-probe allocation costs.  The vanishing readout
  `qpos n - qneg n → 0` is retained as an explicit hypothesis; see the module
  notes below;
* `pressure_limit_supergradient_of_tendsto` and its negative-tilt analogue:
  passage of the finite-`n` supergradient inequalities to a limit pressure when
  the tilt and the supergradient values converge.

## Residual hypotheses

The cavity source law in `CavityProbeReadoutBridge` is a normalized product of
a spatial window law and a mark law, while the zero-slice model is supported on
a single spatial point.  These cannot be equal for positive sample sizes, so the
scene-level readout theorem is not instantiated here; its conclusion is exposed
as the explicit `hreadout` hypothesis.  Likewise the cavity wrapper
`markProbe_opposite_tilt_supergradient_pair` requires a compact mark space,
whereas the physical target manifold is only proper; the supergradient
inequalities are therefore obtained from the underlying
`integral_semidiscreteValue_supergradient_of_tilted_optimal` directly.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Metric Filter OTSelector.Geometry
open OTSelector.Reconstruction OTSelector.Probability
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

noncomputable section
universe u v

namespace OTSelector.Probability

variable {M : Type*} [MeasurableSpace M]

/-- The zero spatial-slice embedding of the mark space. -/
def cavityZeroSlice (x : M) : (Unit → ℝ) × M := ((0 : Unit → ℝ), x)

/-- The zero-slice pushforward of a mark measure. -/
def cavityZeroSliceMeasure (μ : Measure M) : Measure ((Unit → ℝ) × M) :=
  μ.map (cavityZeroSlice (M := M))

theorem measurableEmbedding_cavityZeroSlice :
    MeasurableEmbedding (cavityZeroSlice (M := M)) := by
  have hrange : Set.range (cavityZeroSlice (M := M)) = {z : (Unit → ℝ) × M | z.1 = 0} := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      rfl
    · intro hz
      exact ⟨z.2, Prod.ext hz.symm rfl⟩
  have hrangeM : MeasurableSet (Set.range (cavityZeroSlice (M := M))) := by
    rw [hrange]
    exact (measurableSet_singleton (0 : Unit → ℝ)).preimage measurable_fst
  exact MeasurableEmbedding.of_measurable_inverse (measurable_const.prodMk measurable_id)
    hrangeM measurable_snd (fun x ↦ rfl)

theorem ae_map_cavityZeroSlice_iff (μ : Measure M) {P : (Unit → ℝ) × M → Prop} :
    (∀ᵐ s ∂(μ.map (cavityZeroSlice (M := M))), P s) ↔ ∀ᵐ x ∂μ, P (cavityZeroSlice x) := by
  rw [ae_iff, ae_iff, (measurableEmbedding_cavityZeroSlice (M := M)).map_apply]
  rfl

/-- Pushing a measure to the zero spatial slice preserves the semidiscrete value for
costs that ignore the spatial coordinate. -/
theorem semidiscreteValue_cavityZeroSlice {m : ℕ}
    (μ : Measure M) (c : M → Fin (m + 1) → ℝ)
    (hc : ∀ j, Measurable (fun s ↦ c s j)) (p : Fin (m + 1) → ℝ) :
    semidiscreteValue (μ.map (cavityZeroSlice (M := M)))
      (fun s j ↦ c s.2 j) p = semidiscreteValue μ c p := by
  let e : M → (Unit → ℝ) × M := cavityZeroSlice
  have he : MeasurableEmbedding e := measurableEmbedding_cavityZeroSlice
  have hc' : ∀ j, Measurable (fun s : (Unit → ℝ) × M ↦ c s.2 j) :=
    fun j ↦ (hc j).comp measurable_snd
  have hcost_map (a' : (Unit → ℝ) × M → Fin (m + 1) → ℝ)
      (ha'm : ∀ j, AEStronglyMeasurable (fun s ↦ a' s j) (μ.map e)) :
      semidiscreteAllocationCost (μ.map e) (fun s j ↦ c s.2 j) a' =
        semidiscreteAllocationCost μ c (fun x j ↦ a' (e x) j) := by
    unfold semidiscreteAllocationCost
    let F : (Unit → ℝ) × M → ℝ := fun s ↦ ∑ j, a' s j * c s.2 j
    have hF : AEStronglyMeasurable F (μ.map e) := by
      have h := Finset.aestronglyMeasurable_sum Finset.univ fun j _ ↦
        (ha'm j).mul (hc' j).aestronglyMeasurable
      convert h using 1
      ext s
      simp only [F, Finset.sum_apply, Pi.mul_apply]
    have hmap : ∫ s, F s ∂(μ.map e) = ∫ x, F (e x) ∂μ :=
      integral_map he.measurable.aemeasurable hF
    change (∫ s, F s ∂(μ.map e)) = ∫ x, ∑ j, a' (e x) j * c x j ∂μ
    rw [hmap]
    simp only [F, e, cavityZeroSlice]
  unfold semidiscreteValue
  congr 1
  ext r
  constructor
  · rintro ⟨a', ha', rfl⟩
    have hinteg : ∀ j, Integrable (fun x ↦ a' (e x) j) μ := fun j ↦
      (he.integrable_map_iff (μ := μ) (g := fun s ↦ a' s j)).mp (ha'.integrable j)
    have hnonneg : ∀ᵐ x ∂μ, ∀ j, 0 ≤ a' (e x) j :=
      (ae_map_cavityZeroSlice_iff μ).mp ha'.nonneg
    have hsum : ∀ᵐ x ∂μ, ∑ j, a' (e x) j = 1 :=
      (ae_map_cavityZeroSlice_iff μ).mp ha'.sum_one
    have hmass : ∀ j, ∫ x, a' (e x) j ∂μ = p j := by
      intro j
      rw [← integral_map he.measurable.aemeasurable (ha'.integrable j).aestronglyMeasurable]
      exact ha'.mass j
    refine ⟨fun x j ↦ a' (e x) j, ⟨hinteg, hnonneg, hsum, hmass⟩, ?_⟩
    exact (hcost_map a' (fun j ↦ (ha'.integrable j).aestronglyMeasurable)).symm
  · rintro ⟨a, ha, rfl⟩
    have hinteg : ∀ j, Integrable (fun s : (Unit → ℝ) × M ↦ a s.2 j) (μ.map e) := by
      intro j
      refine (he.integrable_map_iff (μ := μ) (g := fun s : (Unit → ℝ) × M ↦ a s.2 j)).mpr ?_
      simpa only [Function.comp_def, e, cavityZeroSlice] using ha.integrable j
    have hnonneg : ∀ᵐ s ∂(μ.map e), ∀ j, 0 ≤ a s.2 j :=
      (ae_map_cavityZeroSlice_iff μ).mpr ha.nonneg
    have hsum : ∀ᵐ s ∂(μ.map e), ∑ j, a s.2 j = 1 :=
      (ae_map_cavityZeroSlice_iff μ).mpr ha.sum_one
    have hmass : ∀ j, ∫ s, a s.2 j ∂(μ.map e) = p j := by
      intro j
      rw [integral_map he.measurable.aemeasurable (hinteg j).aestronglyMeasurable]
      exact ha.mass j
    refine ⟨fun s j ↦ a s.2 j, ⟨hinteg, hnonneg, hsum, hmass⟩, ?_⟩
    exact hcost_map (fun s j ↦ a s.2 j) (fun j ↦ (hinteg j).aestronglyMeasurable)

/-- Pushing the target-cloud product measure along the mark projection. -/
theorem map_pi_cavityZeroSlice_prod (ν : Measure M) [IsProbabilityMeasure ν] (n : ℕ) :
    Measure.map (fun z : (Fin (n + 1) → ((Unit → ℝ) × M)) × (Fin (n + 1) → ℝ) ↦
        ((fun j ↦ (z.1 j).2), z.2))
      ((Measure.pi (fun _ : Fin (n + 1) ↦ Measure.map (cavityZeroSlice (M := M)) ν)).prod
        (dirichletOne n))
    = (Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n) := by
  have hsingle : ∀ _ : Fin (n + 1),
      Measure.map Prod.snd (Measure.map (cavityZeroSlice (M := M)) ν) = ν := by
    intro _
    rw [Measure.map_map (f := cavityZeroSlice) (g := Prod.snd) measurable_snd
      (measurable_const.prodMk measurable_id)]
    rw [show (Prod.snd ∘ cavityZeroSlice) = id from rfl, Measure.map_id]
  have hsig : ∀ i : Fin (n + 1),
      SigmaFinite (Measure.map Prod.snd (Measure.map (cavityZeroSlice (M := M)) ν)) :=
    fun _ => inferInstance
  have hpi : Measure.map (fun u : Fin (n + 1) → ((Unit → ℝ) × M) ↦ fun j ↦ (u j).2)
      (Measure.pi (fun _ : Fin (n + 1) ↦ Measure.map (cavityZeroSlice (M := M)) ν))
      = Measure.pi (fun _ : Fin (n + 1) ↦ ν) := by
    rw [Measure.pi_map_pi]
    · rw [show (fun _ : Fin (n + 1) ↦
          Measure.map Prod.snd (Measure.map (cavityZeroSlice (M := M)) ν)) =
          (fun _ => ν) from funext hsingle]
    · intro _
      exact measurable_snd.aemeasurable
  rw [← hpi]
  have hm : Measurable (fun u : Fin (n + 1) → ((Unit → ℝ) × M) ↦ fun j ↦ (u j).2) :=
    measurable_pi_iff.mpr fun j ↦ measurable_snd.comp (measurable_pi_apply j)
  have h := Measure.map_prod_map (Measure.pi (fun _ : Fin (n + 1) ↦
      Measure.map (cavityZeroSlice (M := M)) ν)) (dirichletOne n) hm measurable_id
  change Measure.map (Prod.map (fun u : Fin (n + 1) → ((Unit → ℝ) × M) ↦ fun j ↦ (u j).2) id)
      ((Measure.pi (fun _ : Fin (n + 1) ↦ Measure.map (cavityZeroSlice (M := M)) ν)).prod
        (dirichletOne n)) =
    (Measure.map (fun u : Fin (n + 1) → ((Unit → ℝ) × M) ↦ fun j ↦ (u j).2)
      (Measure.pi (fun _ : Fin (n + 1) ↦ Measure.map (cavityZeroSlice (M := M)) ν))).prod
        (dirichletOne n)
  simpa only [Measure.map_id] using h.symm

end OTSelector.Probability

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false

/-- The scaled slack edge cost of the physical mean, as a cavity cost ignoring the
trivial spatial coordinate. -/
noncomputable def finslerMeanCavityCost (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (F : ContinuousFinslerNorm E M) (pot : M → ℝ) (n : ℕ) :
    M → M → (Unit → ℝ) → ℝ :=
  fun a b _ ↦ finslerMeanScale E n * finslerSlackCost F pot a b

set_option maxHeartbeats 1200000 in
/-- **The physical semidiscrete mean is the cavity mark-probe pressure.**  Instantiate
the cavity model on the trivial spatial coordinate and on the zero spatial slice of
the physical source and target laws. -/
theorem finslerSemidiscreteMean_eq_cavityMarkProbePressure
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (mE : Measure E) [mE.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) [NullSingletonClass (ν : Measure M)]
    (K : Set M) (hK : IsCompact K)
    (hμK : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hνK : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (pot : M → ℝ) (hpot : let _instPressureMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 pot)
    (hcost : Integrable (Function.uncurry (finslerSlackCost F pot))
      ((μ : Measure M).prod (ν : Measure M)))
    (f : (K × K) →ᵇ ℝ) (u : ℝ) (n : ℕ)
    (hhat : ∀ᵐ y ∂(Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ : Measure M).map (fun s ↦ finslerMeanScale E n *
          (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l))))) :
    let _instPressureMetric : MetricSpace M := F.metricSpace
    finslerSemidiscreteMean F μ ν K hK hμK hνK pot f u n =
      cavityMarkProbePressure n
        (Measure.map (cavityZeroSlice (M := M)) (μ : Measure M))
        (Measure.map (cavityZeroSlice (M := M)) (ν : Measure M))
        (finslerMeanCavityCost E F pot n)
        (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f) u := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instSecondCountable : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace _instProper
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  let _instMeasEq : MeasurableEq M := inferInstance
  dsimp only
  let cost : M → M → ℝ := finslerSlackCost F pot
  let probe : M → M → ℝ := finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f
  let kval : ℝ := finslerMeanScale E n
  let ρ : Measure (Fin (n + 1) → M) := Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))
  let μcav : Measure ((Unit → ℝ) × M) := Measure.map (cavityZeroSlice (M := M)) (μ : Measure M)
  let νcav : Measure ((Unit → ℝ) × M) := Measure.map (cavityZeroSlice (M := M)) (ν : Measure M)
  let kcav : M → M → (Unit → ℝ) → ℝ := finslerMeanCavityCost E F pot n
  let Φ : (Fin (n + 1) → ((Unit → ℝ) × M)) × (Fin (n + 1) → ℝ) →
      (Fin (n + 1) → M) × (Fin (n + 1) → ℝ) :=
    fun z ↦ ((fun j ↦ (z.1 j).2), z.2)
  let Fphys : (Fin (n + 1) → M) × (Fin (n + 1) → ℝ) → ℝ :=
    fun z ↦ semidiscreteValue (μ : Measure M)
      (fun s j ↦ kval * cost s (z.1 j) + u * probe s (z.1 j)) z.2
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
  have hmean : finslerSemidiscreteMean F μ ν K hK hμK hνK pot f u n =
      ∫ y : Fin (n + 1) → M, ∫ p, Fphys (y, p) ∂dirichletOne n ∂ρ := by
    have h := finslerSemidiscreteMean_eq_integral_semidiscreteValue hF hcomplete mE hdim
      μ ν K hK hμK hνK pot hpot f u n (hcost := hcost)
    dsimp only at h
    rw [h]
    dsimp only [Fphys, cost, probe, kval, ρ]
    rfl
  -- Joint integrability of the physical integrand on the product space.
  let V := Fin (n + 1) → M
  let cV : V → Fin (n + 1) → M → ℝ := fun y j s ↦ kval * cost s (y j)
  let gV : V → Fin (n + 1) → M → ℝ := fun y j s ↦ probe s (y j)
  have hcV (j : Fin (n + 1)) : Measurable (fun z : V × M ↦ cV z.1 j z.2) := by
    have hpair : Measurable (fun z : V × M ↦ (z.2, z.1 j)) :=
      measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst)
    exact ((hcostm.comp hpair).const_mul kval)
  have hciV (j : Fin (n + 1)) :
      Integrable (fun z : V × M ↦ cV z.1 j z.2) (ρ.prod (μ : Measure M)) := by
    have hpair : MeasurePreserving (fun z : V × M ↦ (z.2, z.1 j))
        (ρ.prod (μ : Measure M)) ((μ : Measure M).prod (ν : Measure M)) :=
      Measure.measurePreserving_swap.comp
        ((measurePreserving_eval (fun _ : Fin (n + 1) ↦ (ν : Measure M)) j).prod
          (MeasurePreserving.id (μ : Measure M)))
    exact (hpair.integrable_comp_of_integrable hcost).const_mul kval
  have hgV (j : Fin (n + 1)) : Measurable (fun z : V × M ↦ gV z.1 j z.2) := by
    have hpair : Measurable (fun z : V × M ↦ (z.2, z.1 j)) :=
      measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst)
    exact hprobeM.comp hpair
  have hhatV : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l → NullSingletonClass
      ((μ : Measure M).map (fun s ↦ cV v j s - cV v l s)) := by
    filter_upwards [hhat] with y hy j l hjl
    have heq : (fun s ↦ cV y j s - cV y l s) =
        (fun s ↦ finslerMeanScale E n *
          (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l))) := by
      funext s
      simp only [cV, kval, cost, mul_sub]
    rw [heq]
    exact hy j l hjl
  have hFint : Integrable Fphys (ρ.prod (dirichletOne n)) := by
    have h := integrable_parameterized_dirichlet_semidiscreteValue_tilt
      (μ := (μ : Measure M)) (ρ := ρ) (c := cV) (g := gV)
      hcV hciV hgV hhatV (‖f‖₊) (fun v s j ↦ hprobe s (v j)) u
    simpa only [Fphys, cV, gV] using h
  -- The cavity integrand is the physical integrand precomposed with the mark projection.
  have hcomp : (fun z : (Fin (n + 1) → ((Unit → ℝ) × M)) × (Fin (n + 1) → ℝ) ↦
      semidiscreteValue μcav
        (fun s j ↦ cavitySpatialDifferenceCost kcav s (z.1 j) +
          u * probe s.2 ((z.1 j).2)) z.2) = Fphys ∘ Φ := by
    funext z
    let cz : M → Fin (n + 1) → ℝ :=
      fun x j ↦ kval * cost x ((z.1 j).2) + u * probe x ((z.1 j).2)
    have hcz : ∀ j, Measurable (fun x : M ↦ cz x j) := by
      intro j
      have h1 : Measurable (fun x : M ↦ cost x ((z.1 j).2)) :=
        hcostm.comp (measurable_id.prodMk measurable_const)
      have h2 : Measurable (fun x : M ↦ probe x ((z.1 j).2)) :=
        hprobeM.comp (measurable_id.prodMk measurable_const)
      exact (h1.const_mul kval).add (h2.const_mul u)
    have hinv := semidiscreteValue_cavityZeroSlice (μ := (μ : Measure M)) cz hcz z.2
    simpa only [Function.comp_apply, Fphys, Φ, cz, μcav, kcav, finslerMeanCavityCost, cavitySpatialDifferenceCost] using hinv
  have hmapPhi : Measure.map Φ
      ((Measure.pi (fun _ : Fin (n + 1) ↦ νcav)).prod (dirichletOne n)) =
      ρ.prod (dirichletOne n) := by
    simpa only [Φ, νcav, ρ] using
      map_pi_cavityZeroSlice_prod (M := M) (ν := (ν : Measure M)) n
  have hΦ : Measurable Φ := by
    have hfirst : Measurable (fun z : (Fin (n + 1) → ((Unit → ℝ) × M)) ×
        (Fin (n + 1) → ℝ) ↦ fun j ↦ (z.1 j).2) :=
      measurable_pi_iff.mpr fun j ↦
        measurable_snd.comp ((measurable_pi_apply j).comp measurable_fst)
    exact hfirst.prodMk measurable_snd
  have hcav : cavityMarkProbePressure n μcav νcav kcav probe u =
      ∫ z, Fphys z ∂(ρ.prod (dirichletOne n)) := by
    unfold cavityMarkProbePressure
    change (∫ z : (Fin (n + 1) → ((Unit → ℝ) × M)) × (Fin (n + 1) → ℝ),
      semidiscreteValue μcav
        (fun s j ↦ cavitySpatialDifferenceCost kcav s (z.1 j) +
          u * probe s.2 ((z.1 j).2)) z.2
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ νcav)).prod (dirichletOne n)) =
      ∫ z, Fphys z ∂(ρ.prod (dirichletOne n))
    rw [hcomp]
    rw [← hmapPhi]
    have hFmap : AEStronglyMeasurable Fphys
        (Measure.map Φ ((Measure.pi (fun _ : Fin (n + 1) ↦ νcav)).prod
          (dirichletOne n))) := by
      rw [hmapPhi]
      exact hFint.aestronglyMeasurable
    exact (integral_map hΦ.aemeasurable hFmap).symm
  calc
    finslerSemidiscreteMean F μ ν K hK hμK hνK pot f u n
        = ∫ y : Fin (n + 1) → M, ∫ p, Fphys (y, p) ∂dirichletOne n ∂ρ := hmean
    _ = ∫ z, Fphys z ∂(ρ.prod (dirichletOne n)) := (integral_prod Fphys hFint).symm
    _ = cavityMarkProbePressure n μcav νcav kcav probe u := hcav.symm

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

set_option maxHeartbeats 1600000 in
/-- **Physical supergradient package with the cavity readout.**  The level-`n`
cavity cost is the physical scaled slack cost `finslerMeanCavityCost pot n`, so
the pressure identity discharges the `hpressure_id` input of the cavity
supergradient theorem.  The vanishing readout is retained as the explicit
residual hypothesis `hreadout`. -/
theorem finslerSemidiscreteMean_supergradients_with_readout
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (mE : Measure E) [mE.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) [NullSingletonClass (ν : Measure M)]
    (K : Set M) (hK : IsCompact K)
    (hμK : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hνK : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (pot : M → ℝ) (hpot : let _instSuperMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 pot)
    (hcost : Integrable (Function.uncurry (finslerSlackCost F pot))
      ((μ : Measure M).prod (ν : Measure M)))
    (f : (K × K) →ᵇ ℝ)
    (t : ℕ → ℝ)
    (Aplus Amin : ∀ n, ((Fin (n + 1) → ((Unit → ℝ) × M)) × (Fin (n + 1) → ℝ)) ×
      ((Unit → ℝ) × M) → Fin (n + 1) → ℝ)
    (hAplusm : ∀ n j, Measurable (fun z ↦ Aplus n z j))
    (hAminm : ∀ n j, Measurable (fun z ↦ Amin n z j))
    (hplusopt : ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (n + 1) ↦
        cavityZeroSliceMeasure (ν : Measure M))).prod (dirichletOne n),
      IsOptimalSemidiscreteAllocation (cavityZeroSliceMeasure (μ : Measure M)) z.2
        (fun s j ↦ cavitySpatialDifferenceCost (finslerMeanCavityCost E F pot n) s (z.1 j) +
          t n * finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s.2 ((z.1 j).2))
        (fun s ↦ Aplus n (z, s)))
    (hminusopt : ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (n + 1) ↦
        cavityZeroSliceMeasure (ν : Measure M))).prod (dirichletOne n),
      IsOptimalSemidiscreteAllocation (cavityZeroSliceMeasure (μ : Measure M)) z.2
        (fun s j ↦ cavitySpatialDifferenceCost (finslerMeanCavityCost E F pot n) s (z.1 j) +
          (-(t n)) * finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s.2 ((z.1 j).2))
        (fun s ↦ Amin n (z, s)))
    (hcostc : ∀ n, Continuous (Function.uncurry
      (cavitySpatialDifferenceCost (finslerMeanCavityCost E F pot n))))
    (hcij : ∀ n j, Integrable
      (fun z : (Fin (n + 1) → ((Unit → ℝ) × M)) × ((Unit → ℝ) × M) ↦
        cavitySpatialDifferenceCost (finslerMeanCavityCost E F pot n) z.2 (z.1 j))
      ((Measure.pi (fun _ : Fin (n + 1) ↦ cavityZeroSliceMeasure (ν : Measure M))).prod
        (cavityZeroSliceMeasure (μ : Measure M))))
    (hatom : ∀ n, ∀ᵐ v ∂(Measure.pi (fun _ : Fin (n + 1) ↦
        cavityZeroSliceMeasure (ν : Measure M))),
      ∀ j l, j ≠ l → NullSingletonClass
        ((cavityZeroSliceMeasure (μ : Measure M)).map
          (fun s ↦ cavitySpatialDifferenceCost (finslerMeanCavityCost E F pot n) s (v j) -
            cavitySpatialDifferenceCost (finslerMeanCavityCost E F pot n) s (v l))))
    (hhat : ∀ n, ∀ᵐ y ∂(Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ : Measure M).map (fun s ↦ finslerMeanScale E n *
          (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l)))))
    (hreadout : Tendsto (fun n ↦
      cavityMarkProbeAllocationCost (cavityZeroSliceMeasure (μ : Measure M))
        (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f)
        (cavityZeroSliceMeasure (ν : Measure M)) (Aplus n) -
      cavityMarkProbeAllocationCost (cavityZeroSliceMeasure (μ : Measure M))
        (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f)
        (cavityZeroSliceMeasure (ν : Measure M)) (Amin n)) atTop (𝓝 0)) :
    ∃ qpos qneg : ℕ → ℝ,
      (∀ n, qpos n = cavityMarkProbeAllocationCost
        (cavityZeroSliceMeasure (μ : Measure M))
        (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f)
        (cavityZeroSliceMeasure (ν : Measure M)) (Aplus n)) ∧
      (∀ n, qneg n = cavityMarkProbeAllocationCost
        (cavityZeroSliceMeasure (μ : Measure M))
        (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f)
        (cavityZeroSliceMeasure (ν : Measure M)) (Amin n)) ∧
      (∀ᶠ n in atTop, ∀ u,
        finslerSemidiscreteMean F μ ν K hK hμK hνK pot f u n ≤
          finslerSemidiscreteMean F μ ν K hK hμK hνK pot f (t n) n + qpos n * (u - t n)) ∧
      (∀ᶠ n in atTop, ∀ u,
        finslerSemidiscreteMean F μ ν K hK hμK hνK pot f u n ≤
          finslerSemidiscreteMean F μ ν K hK hμK hνK pot f (-(t n)) n + qneg n * (u + t n)) ∧
      Tendsto (fun n ↦ qpos n - qneg n) atTop (𝓝 0) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instSecondCountable : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace _instProper
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  let _instMeasEq : MeasurableEq M := inferInstance
  have hSB : StandardBorelSpace ((Unit → ℝ) × M) := inferInstance
  let μcav : Measure ((Unit → ℝ) × M) := cavityZeroSliceMeasure (μ : Measure M)
  let νcav : Measure ((Unit → ℝ) × M) := cavityZeroSliceMeasure (ν : Measure M)
  let gm : M → M → ℝ := finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f
  have hμcavProb : IsProbabilityMeasure μcav := by
    dsimp only [μcav, cavityZeroSliceMeasure]
    refine Measure.isProbabilityMeasure_map ?_
    change AEMeasurable (fun x : M ↦ ((0 : Unit → ℝ), x)) (μ : Measure M)
    exact (measurable_const.prodMk measurable_id).aemeasurable
  have hνcavProb : IsProbabilityMeasure νcav := by
    dsimp only [νcav, cavityZeroSliceMeasure]
    refine Measure.isProbabilityMeasure_map ?_
    change AEMeasurable (fun x : M ↦ ((0 : Unit → ℝ), x)) (ν : Measure M)
    exact (measurable_const.prodMk measurable_id).aemeasurable
  have hgm : Measurable (Function.uncurry gm) := by
    have hmap : Measurable (fun p : M × M ↦
        (supportProjection μ K hK.measurableSet hμK p.1,
          supportProjection ν K hK.measurableSet hνK p.2)) :=
      ((measurable_supportProjection μ K hK.measurableSet hμK).comp measurable_fst).prodMk
        ((measurable_supportProjection ν K hK.measurableSet hνK).comp measurable_snd)
    exact f.continuous.measurable.comp hmap
  have hgmb : ∀ a b, |gm a b| ≤ (‖f‖₊ : ℝ) := by
    intro a b
    have h := BoundedContinuousFunction.nnnorm_coe_le_nnnorm f
      (supportProjection μ K hK.measurableSet hμK a,
        supportProjection ν K hK.measurableSet hνK b)
    have h' : ((‖f (supportProjection μ K hK.measurableSet hμK a,
        supportProjection ν K hK.measurableSet hνK b)‖₊ : ℝ) ≤ (‖f‖₊ : ℝ)) :=
      NNReal.coe_le_coe.mpr h
    simpa only [gm, finslerCarrierProbe, coe_nnnorm, Real.norm_eq_abs] using h'
  let qpos : ℕ → ℝ := fun n ↦ cavityMarkProbeAllocationCost μcav gm νcav (Aplus n)
  let qneg : ℕ → ℝ := fun n ↦ cavityMarkProbeAllocationCost μcav gm νcav (Amin n)
  have hmeasCav : ∀ (n : ℕ) (j : Fin (n + 1)),
      Measurable (fun z : (Fin (n + 1) → (Unit → ℝ) × M) × ((Unit → ℝ) × M) ↦
        cavitySpatialDifferenceCost (finslerMeanCavityCost E F pot n) z.2 (z.1 j)) := by
    intro n j
    exact (hcostc n).measurable.comp
      (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst))
  have hmeasProbe : ∀ (n : ℕ) (j : Fin (n + 1)),
      Measurable (fun z : (Fin (n + 1) → (Unit → ℝ) × M) × ((Unit → ℝ) × M) ↦
        gm z.2.2 ((z.1 j).2)) := by
    intro n j
    have hpair : Measurable (fun z : (Fin (n + 1) → (Unit → ℝ) × M) ×
        ((Unit → ℝ) × M) ↦ (z.2.2, (z.1 j).2)) :=
      measurable_snd.snd.prodMk (((measurable_pi_apply j).comp measurable_fst).snd)
    exact hgm.comp hpair
  have hboundCav : ∀ (n : ℕ) (v : Fin (n + 1) → (Unit → ℝ) × M)
      (s : (Unit → ℝ) × M) (j : Fin (n + 1)), |gm s.2 ((v j).2)| ≤ (‖f‖₊ : ℝ) :=
    fun n v s j ↦ hgmb s.2 ((v j).2)
  have hpos : ∀ᶠ n in atTop, ∀ u,
      finslerSemidiscreteMean F μ ν K hK hμK hνK pot f u n ≤
        finslerSemidiscreteMean F μ ν K hK hμK hνK pot f (t n) n + qpos n * (u - t n) := by
    filter_upwards with n u
    have hpair := integral_semidiscreteValue_supergradient_of_tilted_optimal
      (m := n) (S := (Unit → ℝ) × M)
      (V := Fin (n + 1) → (Unit → ℝ) × M)
      (μ := μcav) (ρ := Measure.pi (fun _ : Fin (n + 1) ↦ νcav))
      (c := fun v j s ↦ cavitySpatialDifferenceCost (finslerMeanCavityCost E F pot n) s (v j))
      (g := fun v j s ↦ gm s.2 ((v j).2))
      (fun j ↦ hmeasCav n j) (hcij n) (fun j ↦ hmeasProbe n j) (hatom n) (‖f‖₊) (hboundCav n)
      (Aplus n) (hAplusm n) (t := t n) (hplusopt n)
    dsimp only at hpair
    change ∀ u, cavityMarkProbePressure n μcav νcav (finslerMeanCavityCost E F pot n) gm u ≤
      cavityMarkProbePressure n μcav νcav (finslerMeanCavityCost E F pot n) gm (t n) +
        (u - t n) * qpos n at hpair
    have hid_u := finslerSemidiscreteMean_eq_cavityMarkProbePressure
      (F := F) hF hcomplete mE hdim μ ν K hK hμK hνK pot hpot hcost f u n (hhat n)
    have hid_t := finslerSemidiscreteMean_eq_cavityMarkProbePressure
      (F := F) hF hcomplete mE hdim μ ν K hK hμK hνK pot hpot hcost f (t n) n (hhat n)
    have hval := hpair u
    simp only [μcav, νcav, gm, cavityZeroSliceMeasure] at hval
    rw [← hid_u, ← hid_t] at hval
    simpa only [mul_comm] using hval
  have hneg : ∀ᶠ n in atTop, ∀ u,
      finslerSemidiscreteMean F μ ν K hK hμK hνK pot f u n ≤
        finslerSemidiscreteMean F μ ν K hK hμK hνK pot f (-(t n)) n + qneg n * (u + t n) := by
    filter_upwards with n u
    have hpair := integral_semidiscreteValue_supergradient_of_tilted_optimal
      (m := n) (S := (Unit → ℝ) × M)
      (V := Fin (n + 1) → (Unit → ℝ) × M)
      (μ := μcav) (ρ := Measure.pi (fun _ : Fin (n + 1) ↦ νcav))
      (c := fun v j s ↦ cavitySpatialDifferenceCost (finslerMeanCavityCost E F pot n) s (v j))
      (g := fun v j s ↦ gm s.2 ((v j).2))
      (fun j ↦ hmeasCav n j) (hcij n) (fun j ↦ hmeasProbe n j) (hatom n) (‖f‖₊) (hboundCav n)
      (Amin n) (hAminm n) (t := -(t n)) (hminusopt n)
    dsimp only at hpair
    change ∀ u, cavityMarkProbePressure n μcav νcav (finslerMeanCavityCost E F pot n) gm u ≤
      cavityMarkProbePressure n μcav νcav (finslerMeanCavityCost E F pot n) gm (-(t n)) +
        (u - (-(t n))) * qneg n at hpair
    have hid_u := finslerSemidiscreteMean_eq_cavityMarkProbePressure
      (F := F) hF hcomplete mE hdim μ ν K hK hμK hνK pot hpot hcost f u n (hhat n)
    have hid_m := finslerSemidiscreteMean_eq_cavityMarkProbePressure
      (F := F) hF hcomplete mE hdim μ ν K hK hμK hνK pot hpot hcost f (-(t n)) n (hhat n)
    have hval := hpair u
    simp only [μcav, νcav, gm, cavityZeroSliceMeasure] at hval
    rw [← hid_u, ← hid_m] at hval
    simpa only [mul_comm, sub_neg_eq_add] using hval
  refine ⟨qpos, qneg, fun n ↦ rfl, fun n ↦ rfl, hpos, hneg, ?_⟩
  simpa only [qpos, qneg, μcav, νcav, gm] using hreadout

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- Passage of the plus-tilt supergradient inequality to the limit pressure,
when the tilt and the supergradient values converge. -/
theorem pressure_limit_supergradient_of_tendsto
    {P : ℕ → ℝ → ℝ} {t qpos : ℕ → ℝ} {pressure : ℝ → ℝ} {q : ℝ}
    (hsup : ∀ᶠ n in atTop, ∀ u, P n u ≤ P n (t n) + qpos n * (u - t n))
    (hP : ∀ u, Tendsto (fun n ↦ P n u) atTop (𝓝 (pressure u)))
    (hPt : Tendsto (fun n ↦ P n (t n)) atTop (𝓝 (pressure 0)))
    (ht : Tendsto t atTop (𝓝 0)) (hq : Tendsto qpos atTop (𝓝 q)) :
    ∀ u, pressure u ≤ pressure 0 + q * u := by
  intro u
  have hright : Tendsto (fun n ↦ P n (t n) + qpos n * (u - t n)) atTop
      (𝓝 (pressure 0 + q * u)) := by
    have h2 : Tendsto (fun n ↦ qpos n * (u - t n)) atTop (𝓝 (q * u)) := by
      simpa using hq.mul (tendsto_const_nhds.sub ht)
    simpa using hPt.add h2
  exact le_of_tendsto_of_tendsto (hP u) hright (hsup.mono fun n hn ↦ hn u)

/-- Passage of the minus-tilt supergradient inequality to the limit pressure. -/
theorem pressure_limit_supergradient_of_tendsto_neg
    {P : ℕ → ℝ → ℝ} {t qneg : ℕ → ℝ} {pressure : ℝ → ℝ} {q : ℝ}
    (hsup : ∀ᶠ n in atTop, ∀ u, P n u ≤ P n (-(t n)) + qneg n * (u + t n))
    (hP : ∀ u, Tendsto (fun n ↦ P n u) atTop (𝓝 (pressure u)))
    (hPneg : Tendsto (fun n ↦ P n (-(t n))) atTop (𝓝 (pressure 0)))
    (ht : Tendsto t atTop (𝓝 0)) (hq : Tendsto qneg atTop (𝓝 q)) :
    ∀ u, pressure u ≤ pressure 0 + q * u := by
  intro u
  have hright : Tendsto (fun n ↦ P n (-(t n)) + qneg n * (u + t n)) atTop
      (𝓝 (pressure 0 + q * u)) := by
    have h2 : Tendsto (fun n ↦ qneg n * (u + t n)) atTop (𝓝 (q * u)) := by
      simpa using hq.mul (tendsto_const_nhds.add ht)
    simpa using hPneg.add h2
  exact le_of_tendsto_of_tendsto (hP u) hright (hsup.mono fun n hn ↦ hn u)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

