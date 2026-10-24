import OTSelector.Limit.FinslerMeanTiltSupergradient
import OTSelector.Probability.CavityModelTiltSupergradients
import OTSelector.Probability.ParameterizedAffineTilts

/-!
# Opposite-tilt supergradients of the physical mean off a countable bad set

The differentiability assembly `exists_hasDerivAt_of_finslerSemidiscreteMean` takes
as its stochastic input `hsup`: for every tilt sequence avoiding a countable set,
the physical Dirichlet semidiscrete mean admits opposite-tilt supergradients.
`Probability/CavityModelTiltSupergradients` already produces such a pair once the
tilted pairwise cost differences are atomless on the source law, level by level.

This module supplies the missing bookkeeping:

* `finslerBadTiltsAt` is the level-`n` set of tilts for which the tilted pairwise
  differences `kval * (slack y_j - slack y_l) + u * (probe y_j - probe y_l)` fail
  to be null-singleton on the source law on a positive-measure set of target
  clouds;
* `finslerBadTilts` is the union over all levels;
* `countable_finslerBadTiltsAt` and `countable_finslerBadTilts` prove that these
  exceptional sets are countable, using
  `countable_bad_parameterized_cavity_tilts` level by level, with the base-cost
  atomlessness supplied by `nullSingletonClass_map_scaled_distanceSlack_sub`;
* `exists_finslerSemidiscreteMean_opposite_tilt_supergradients_of_tilt_good` is
  the direct form taking the per-level a.e. atomlessness hypotheses;
* `exists_finslerSemidiscreteMean_opposite_tilt_supergradients` is the bad-set
  form: every sequence whose tilts and negative tilts avoid `finslerBadTilts`
  has opposite-tilt supergradients at every level.

The probe-cost equality `qpos n - qneg n -> 0` is the paper's rooted-scene
readout and is *not* proved here.
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

/-- **Level-`n` bad tilts.**  A tilt `u` is bad at level `n` when, on a
positive-measure set of target clouds, some tilted pairwise cost difference
`kval (c y_j - c y_l) + u (g y_j - g y_l)` fails to have null-singleton image
under the source law.  Here `kval = finslerMeanScale E n`, `c` is the Finsler
distance-slack cost, and `g` is the compact-carrier probe. -/
noncomputable def finslerBadTiltsAt (F : ContinuousFinslerNorm E M)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (pot : M → ℝ) (f : (K × K) →ᵇ ℝ) (n : ℕ) : Set ℝ :=
  {u | ¬ ∀ᵐ y ∂(Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))),
    ∀ j l, j ≠ l → NullSingletonClass
      ((μ : Measure M).map (fun s ↦
        finslerMeanScale E n *
            (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l)) +
          u * (finslerCarrierProbe μ ν K hK.measurableSet hμ hν f s (y j) -
            finslerCarrierProbe μ ν K hK.measurableSet hμ hν f s (y l))))}

/-- **The countable exceptional tilt set.**  Union over all levels of the bad
tilt sets `finslerBadTiltsAt`. -/
noncomputable def finslerBadTilts (F : ContinuousFinslerNorm E M)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (pot : M → ℝ) (f : (K × K) →ᵇ ℝ) : Set ℝ :=
  ⋃ n, finslerBadTiltsAt F μ ν K hK hμ hν pot f n

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- **Level-`n` bad tilts are countable.**  The cavity countability theorem is
applied to the finite target cloud with base cost `kval * slack`; its base
atomlessness follows from the Finsler distance level-set theorem at the nonzero
scale `finslerMeanScale E n`. -/
theorem countable_finslerBadTiltsAt
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) [NullSingletonClass (ν : Measure M)]
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμK : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hνK : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (pot : M → ℝ) (hpot : let _instCountableBadTiltsMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 pot)
    (f : (K × K) →ᵇ ℝ) (n : ℕ) :
    (finslerBadTiltsAt F μ ν K hK hμK hνK pot f n).Countable := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instSecondCountable : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace _instProper
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  let _instMeasEq : MeasurableEq M := inferInstance
  let V := Fin (n + 1) → M
  let ρ : Measure V := Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))
  let c : Fin (n + 1) → V → M → ℝ :=
    fun j y s ↦ finslerMeanScale E n * finslerSlackCost F pot s (y j)
  let g : Fin (n + 1) → V → M → ℝ :=
    fun j y s ↦ finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y j)
  have hpotL : LipschitzWith 1 pot := hpot
  have hcostm : Measurable (Function.uncurry (finslerSlackCost F pot)) :=
    F.measurable_distance_slack hpotL
  have hprobeM : Measurable
      (Function.uncurry (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f)) := by
    have hmap : Measurable (fun p : M × M ↦
        (supportProjection μ K hK.measurableSet hμK p.1,
          supportProjection ν K hK.measurableSet hνK p.2)) :=
      ((measurable_supportProjection μ K hK.measurableSet hμK).comp measurable_fst).prodMk
        ((measurable_supportProjection ν K hK.measurableSet hνK).comp measurable_snd)
    exact f.continuous.measurable.comp hmap
  have hc (j : Fin (n + 1)) : Measurable (Function.uncurry (c j)) := by
    have hpair : Measurable (fun z : V × M ↦ (z.2, z.1 j)) :=
      measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst)
    exact (hcostm.comp hpair).const_mul (finslerMeanScale E n)
  have hg (j : Fin (n + 1)) : Measurable (Function.uncurry (g j)) := by
    have hpair : Measurable (fun z : V × M ↦ (z.2, z.1 j)) :=
      measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst)
    exact hprobeM.comp hpair
  have hkval : finslerMeanScale E n ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hatom : ∀ᵐ y ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass ((μ : Measure M).map (fun s ↦ c j y s - c l y s)) := by
    filter_upwards [ae_injective_pi_of_nullSingletonClass (ι := Fin (n + 1))
      (ν : Measure M)] with y hy j l hjl
    have h := nullSingletonClass_map_scaled_distanceSlack_sub hF m (μ : Measure M) hdim
      hμchart hcomplete pot hkval (hy.ne hjl)
    simpa only [c, finslerSlackCost, F.metricSpace_dist] using h
  have h := countable_bad_parameterized_cavity_tilts
    (μ := (μ : Measure M)) (ρ := ρ) (V := V) (ι := Fin (n + 1)) c g hc hg hatom
  refine h.mono ?_
  intro u hu hgood
  apply hu
  filter_upwards [hgood] with y hy j l hjl
  have hfun : (fun s ↦
      finslerMeanScale E n *
          (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l)) +
        u * (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y j) -
          finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y l))) =
      (fun s ↦ (c j y s + u * g j y s) - (c l y s + u * g l y s)) := by
    funext s
    simp only [c, g]
    ring
  rw [hfun]
  exact hy j l hjl

/-- **The exceptional tilt set is countable.**  Union of the level-wise
countable bad tilt sets. -/
theorem countable_finslerBadTilts
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) [NullSingletonClass (ν : Measure M)]
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμK : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hνK : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (pot : M → ℝ) (hpot : let _instCountableBadTiltsMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 pot)
    (f : (K × K) →ᵇ ℝ) :
    (finslerBadTilts F μ ν K hK hμK hνK pot f).Countable := by
  unfold finslerBadTilts
  exact Set.countable_iUnion fun n ↦
    countable_finslerBadTiltsAt hF hcomplete m hdim μ ν hμchart hνchart
      K hK hμK hνK pot hpot f n

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- **Opposite-tilt supergradients from pointwise good tilts.**  If at every level
`n` the tilted pairwise cost differences at `t n` and `-t n` are atomless on the
source law for almost every target cloud, then the physical semidiscrete mean has
opposite-tilt supergradients at `± t n`, simultaneously for all `n` and all
tilts `s`. -/
theorem exists_finslerSemidiscreteMean_opposite_tilt_supergradients_of_tilt_good
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) [NullSingletonClass (ν : Measure M)]
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμK : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hνK : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (pot : M → ℝ) (hpot : let _instPairGoodMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 pot)
    (f : (K × K) →ᵇ ℝ)
    (hcost : Integrable (Function.uncurry (finslerSlackCost F pot))
      ((μ : Measure M).prod (ν : Measure M)))
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (htgood : ∀ n, ∀ᵐ y ∂(Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ : Measure M).map (fun s ↦
          finslerMeanScale E n *
              (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l)) +
            t n * (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y j) -
              finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y l)))))
    (htgoodneg : ∀ n, ∀ᵐ y ∂(Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))),
      ∀ j l, j ≠ l → NullSingletonClass
        ((μ : Measure M).map (fun s ↦
          finslerMeanScale E n *
              (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l)) +
            (-t n) * (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y j) -
              finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y l))))) :
    let _instPairGoodMetric : MetricSpace M := F.metricSpace
    ∃ qpos qneg : ℕ → ℝ,
      (∀ n, ∀ s,
        finslerSemidiscreteMean F μ ν K hK hμK hνK pot f s n ≤
          finslerSemidiscreteMean F μ ν K hK hμK hνK pot f (t n) n +
            qpos n * (s - t n)) ∧
      (∀ n, ∀ s,
        finslerSemidiscreteMean F μ ν K hK hμK hνK pot f s n ≤
          finslerSemidiscreteMean F μ ν K hK hμK hνK pot f (-(t n)) n +
            qneg n * (s + t n)) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instSecondCountable : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace _instProper
  let _instPolish : PolishSpace M := inferInstance
  let _instStandard : StandardBorelSpace M := inferInstance
  let _instMeasEq : MeasurableEq M := inferInstance
  dsimp only
  have hpotL : LipschitzWith 1 pot := hpot
  have hcostm : Measurable (Function.uncurry (finslerSlackCost F pot)) :=
    F.measurable_distance_slack hpotL
  have hprobeM : Measurable
      (Function.uncurry (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f)) := by
    have hmap : Measurable (fun p : M × M ↦
        (supportProjection μ K hK.measurableSet hμK p.1,
          supportProjection ν K hK.measurableSet hνK p.2)) :=
      ((measurable_supportProjection μ K hK.measurableSet hμK).comp measurable_fst).prodMk
        ((measurable_supportProjection ν K hK.measurableSet hνK).comp measurable_snd)
    exact f.continuous.measurable.comp hmap
  have hprobe : ∀ x y,
      |finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f x y| ≤ (‖f‖₊ : ℝ) := by
    intro x y
    have h := BoundedContinuousFunction.nnnorm_coe_le_nnnorm f
      (supportProjection μ K hK.measurableSet hμK x,
        supportProjection ν K hK.measurableSet hνK y)
    have h' : ((‖f (supportProjection μ K hK.measurableSet hμK x,
        supportProjection ν K hK.measurableSet hνK y)‖₊ : ℝ) ≤ (‖f‖₊ : ℝ)) :=
      NNReal.coe_le_coe.mpr h
    simpa only [finslerCarrierProbe, coe_nnnorm, Real.norm_eq_abs] using h'
  have hkval : ∀ n : ℕ, finslerMeanScale E n ≠ 0 := fun n ↦
    (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hex : ∀ n : ℕ, ∃ qp qn : ℝ,
      (∀ s : ℝ,
        finslerSemidiscreteMean F μ ν K hK hμK hνK pot f s n ≤
          finslerSemidiscreteMean F μ ν K hK hμK hνK pot f (t n) n +
            qp * (s - t n)) ∧
      (∀ s : ℝ,
        finslerSemidiscreteMean F μ ν K hK hμK hνK pot f s n ≤
          finslerSemidiscreteMean F μ ν K hK hμK hνK pot f (-(t n)) n +
            qn * (s + t n)) := by
    intro n
    let V := Fin (n + 1) → M
    let ρ : Measure V := Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))
    let cost : M → M → ℝ := finslerSlackCost F pot
    let probe : M → M → ℝ := finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f
    let base : M → M → ℝ := fun s y ↦ finslerMeanScale E n * cost s y
    let g : M → M → ℝ := probe
    let P : ℝ → ℝ := fun u ↦ ∫ z : V × (Fin (n + 1) → ℝ),
      semidiscreteValue (μ : Measure M) (fun s j ↦ base s (z.1 j) + u * g s (z.1 j)) z.2
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))).prod (dirichletOne n)
    have hbase_meas : Measurable (Function.uncurry base) := by
      have hfun : Function.uncurry base =
          (fun p : M × M ↦ finslerMeanScale E n * cost p.1 p.2) := rfl
      rw [hfun]
      exact hcostm.const_mul _
    have hbase_int : Integrable (Function.uncurry base)
        ((μ : Measure M).prod (ν : Measure M)) := by
      have hfun : Function.uncurry base =
          (fun p : M × M ↦ finslerMeanScale E n * cost p.1 p.2) := rfl
      rw [hfun]
      exact hcost.const_mul _
    have hg_meas : Measurable (Function.uncurry g) := hprobeM
    have hg_bound : ∀ x y, |g x y| ≤ (‖f‖₊ : ℝ) := fun x y ↦ hprobe x y
    have hatomBase : ∀ y z : M, y ≠ z →
        NullSingletonClass ((μ : Measure M).map (fun x ↦ base x y - base x z)) := by
      intro y z hyz
      have h := nullSingletonClass_map_scaled_distanceSlack_sub hF m (μ : Measure M) hdim
        hμchart hcomplete pot (hkval n) hyz
      simpa only [base, cost, finslerSlackCost, F.metricSpace_dist] using h
    have hgoodAt (u : ℝ)
        (hu : ∀ᵐ y ∂(Measure.pi (fun _ : Fin (n + 1) ↦ (ν : Measure M))),
          ∀ j l, j ≠ l → NullSingletonClass
            ((μ : Measure M).map (fun s ↦
              finslerMeanScale E n *
                  (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l)) +
                u * (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y j) -
                  finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y l))))) :
        ∀ᵐ y ∂ρ, ∀ j l, j ≠ l → NullSingletonClass
          ((μ : Measure M).map (fun s ↦
            (base s (y j) + u * g s (y j)) - (base s (y l) + u * g s (y l)))) := by
      filter_upwards [hu] with y hy j l hjl
      have hfun : (fun s ↦
          (base s (y j) + u * g s (y j)) - (base s (y l) + u * g s (y l))) =
          (fun s ↦
            finslerMeanScale E n *
                (finslerSlackCost F pot s (y j) - finslerSlackCost F pot s (y l)) +
              u * (finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y j) -
                finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f s (y l))) := by
        funext s
        simp only [base, g, cost, probe]
        ring
      rw [hfun]
      exact hy j l hjl
    obtain ⟨qp, qn, hqp, hqn⟩ :=
      exists_bipartite_opposite_tilt_supergradients (m := n) (S := M) (T := M)
        (μ := (μ : Measure M)) (ν := (ν : Measure M)) base g hbase_meas hbase_int
        hg_meas hatomBase (‖f‖₊) hg_bound (fun _ ↦ t n) (fun _ ↦ htpos n)
        (fun _ ↦ hgoodAt (t n) (htgood n)) (fun _ ↦ hgoodAt (-(t n)) (htgoodneg n))
    dsimp only at hqp hqn
    have hP : ∀ u : ℝ,
        finslerSemidiscreteMean F μ ν K hK hμK hνK pot f u n = P u := by
      intro u
      have hmean := finslerSemidiscreteMean_eq_integral_semidiscreteValue hF hcomplete m hdim
        μ ν K hK hμK hνK pot hpot f u n (hcost := hcost)
      have hjoint := integrable_bipartite_dirichlet_semidiscreteValue (m := n) (S := M) (T := M)
        (μ := (μ : Measure M)) (ν := (ν : Measure M)) base g hbase_meas hbase_int
        hg_meas hatomBase (‖f‖₊) hg_bound u
      have hprod : (∫ y : V, ∫ p, semidiscreteValue (μ : Measure M)
            (fun s j ↦ base s (y j) + u * g s (y j)) p ∂dirichletOne n ∂ρ) =
          ∫ z : V × (Fin (n + 1) → ℝ), semidiscreteValue (μ : Measure M)
            (fun s j ↦ base s (z.1 j) + u * g s (z.1 j)) z.2
              ∂ρ.prod (dirichletOne n) :=
        (integral_prod _ hjoint).symm
      dsimp only [finslerSlackCost, finslerCarrierProbe, finslerMeanScale] at hmean
      simp only [P, base, g, cost, probe, ρ, V, finslerMeanScale, finslerSlackCost,
        finslerCarrierProbe] at hmean hprod ⊢
      rw [hmean, hprod]
    refine ⟨qp n, qn n, ?_, ?_⟩
    · intro s
      rw [hP s, hP (t n)]
      simpa only [P] using hqp n s
    · intro s
      rw [hP s, hP (-(t n))]
      simpa only [P] using hqn n s
  choose qpos qneg hq using hex
  exact ⟨qpos, qneg, fun n s ↦ (hq n).1 s, fun n s ↦ (hq n).2 s⟩

set_option maxHeartbeats 1600000 in
set_option linter.unusedVariables false in
/-- **Opposite-tilt supergradients off the countable bad set.**  For every tilt
sequence whose tilts and negative tilts avoid `finslerBadTilts`, the physical
Dirichlet semidiscrete mean admits opposite-tilt supergradients at every level,
simultaneously for all tilt arguments `s`. -/
theorem exists_finslerSemidiscreteMean_opposite_tilt_supergradients
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) [NullSingletonClass (ν : Measure M)]
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμK : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hνK : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (pot : M → ℝ) (hpot : let _instPairBadMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 pot)
    (f : (K × K) →ᵇ ℝ)
    (hcost : Integrable (Function.uncurry (finslerSlackCost F pot))
      ((μ : Measure M).prod (ν : Measure M)))
    (t : ℕ → ℝ) (htpos : ∀ n, 0 < t n)
    (htgood : ∀ n, t n ∉ finslerBadTilts F μ ν K hK hμK hνK pot f)
    (htgoodneg : ∀ n, -t n ∉ finslerBadTilts F μ ν K hK hμK hνK pot f) :
    let _instPairBadMetric : MetricSpace M := F.metricSpace
    ∃ qpos qneg : ℕ → ℝ,
      (∀ n, ∀ s,
        finslerSemidiscreteMean F μ ν K hK hμK hνK pot f s n ≤
          finslerSemidiscreteMean F μ ν K hK hμK hνK pot f (t n) n +
            qpos n * (s - t n)) ∧
      (∀ n, ∀ s,
        finslerSemidiscreteMean F μ ν K hK hμK hνK pot f s n ≤
          finslerSemidiscreteMean F μ ν K hK hμK hνK pot f (-(t n)) n +
            qneg n * (s + t n)) := by
  have hnotmem : ∀ (n : ℕ) (u : ℝ),
      u ∉ finslerBadTilts F μ ν K hK hμK hνK pot f →
        u ∉ finslerBadTiltsAt F μ ν K hK hμK hνK pot f n := by
    intro n u hu hmem
    exact hu (Set.mem_iUnion.mpr ⟨n, hmem⟩)
  refine exists_finslerSemidiscreteMean_opposite_tilt_supergradients_of_tilt_good
    hF hcomplete m hdim μ ν hμchart hνchart K hK hμK hνK pot hpot f hcost t htpos
    (fun n ↦ ?_) (fun n ↦ ?_)
  · by_contra hcon
    exact hnotmem n (t n) (htgood n) hcon
  · by_contra hcon
    exact hnotmem n (-t n) (htgoodneg n) hcon

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
