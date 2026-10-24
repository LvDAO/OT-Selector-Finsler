import OTSelector.Geometry.Finsler.DistanceDifference
import OTSelector.Probability.IIDBipartiteAssignment
import OTSelector.Finite.EmpiricalFractional

/-!
# Almost-sure uniqueness of the original Finsler empirical matching

For distinct fixed targets, chartwise absolute continuity in dimension at least two gives
atomless original length-distance differences. Applied to the original iid source array,
this yields a unique optimal permutation and a singleton fractional optimal face. The full
empirical-coupling representation then gives uniqueness among every original coupling,
including when source observations repeat. No atomlessness or chosen-plan oracle is supplied.

The two-color consumers also derive distinct targets from their original chartwise absolutely
continuous law. They use independence of the two full iid arrays on their original probability
space, without a target-injectivity premise or conditional replacement sampling.
-/

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [MeasurableSpace Ω] {n : ℕ}
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
  (m : Measure E) [m.IsAddHaarMeasure] (μ : Measure M)

include hF

/-- Fixed distinct targets and original iid sources have a unique original length assignment
almost surely; the difference laws are proved atomless from the actual Finsler geometry. -/
theorem ae_existsUnique_distanceAssignment
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin (n + 1) → Ω → M) (hX : ∀ i, Measurable (X i))
    (hindep : ProbabilityTheory.iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (Y : Fin (n + 1) → M) (hY : Function.Injective Y) :
    let _instFinslerIIDAssignmentMetric : MetricSpace M := F.metricSpace
    ∀ᵐ sample ∂P, ∃! σ, OptimalAssignment (fun i j ↦ dist (X i sample) (Y j)) σ := by
  let _instFinslerIIDAssignmentProofMetric : MetricSpace M := F.metricSpace
  apply Probability.ae_existsUnique_optimalAssignment_of_iid_atomless P μ X hX hindep hlaw
    (fun j x ↦ dist x (Y j))
  · intro j
    exact (continuous_id.dist continuous_const).measurable
  · intro j k hjk
    exact hF.nullSingletonClass_map_distance_sub m μ hdim hchart hcomplete
      (fun h ↦ hjk (hY h))

/-- The entire fractional optimal face for the actual sampled length matrix is a singleton. -/
theorem ae_existsUnique_distanceFractionalAssignment
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin (n + 1) → Ω → M) (hX : ∀ i, Measurable (X i))
    (hindep : ProbabilityTheory.iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (Y : Fin (n + 1) → M) (hY : Function.Injective Y) :
    let _instFinslerIIDFractionalMetric : MetricSpace M := F.metricSpace
    ∀ᵐ sample ∂P, ∃! A,
      OptimalFractionalAssignment (fun i j ↦ dist (X i sample) (Y j)) A := by
  let _instFinslerIIDFractionalProofMetric : MetricSpace M := F.metricSpace
  filter_upwards [hF.ae_existsUnique_distanceAssignment m μ hdim hchart hcomplete
    P X hX hindep hlaw Y hY] with sample hsample
  exact existsUnique_optimalFractionalAssignment_of_existsUnique_optimalAssignment _ hsample

/-- Every coupling of the original empirical marginals is covered by the uniqueness result.
No injectivity of the source sample map is required. -/
theorem ae_existsUnique_distanceEmpiricalCoupling
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin (n + 1) → Ω → M) (hX : ∀ i, Measurable (X i))
    (hindep : ProbabilityTheory.iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (Y : Fin (n + 1) → M) (hY : Function.Injective Y) :
    let _instFinslerIIDCouplingMetric : MetricSpace M := F.metricSpace
    ∀ᵐ sample ∂P, ∃! π : Measure (M × M),
      IsOptimalCoupling edist (empiricalMeasure (fun i ↦ X i sample)) (empiricalMeasure Y) π := by
  let _instFinslerIIDCouplingProofMetric : MetricSpace M := F.metricSpace
  filter_upwards [hF.ae_existsUnique_distanceFractionalAssignment m μ hdim hchart hcomplete
    P X hX hindep hlaw Y hY] with sample hsample
  obtain ⟨A, hA, huniq⟩ := hsample
  have hdist : (edist : M → M → ℝ≥0∞) = fun x y ↦ ENNReal.ofReal (dist x y) :=
    funext fun x ↦ funext fun y ↦ edist_dist x y
  have hiff (π : Measure (M × M)) :
      IsOptimalCoupling edist (empiricalMeasure (fun i ↦ X i sample)) (empiricalMeasure Y) π ↔
        ∃ B, OptimalFractionalAssignment (fun i j ↦ dist (X i sample) (Y j)) B ∧
          fractionalEmpiricalMeasure (fun i ↦ X i sample) Y B = π := by
    rw [hdist]
    exact isOptimalCoupling_empirical_iff_exists_optimalFractional
      (fun i ↦ X i sample) Y dist (fun _ _ ↦ dist_nonneg) π
  refine ⟨fractionalEmpiricalMeasure (fun i ↦ X i sample) Y A,
    (hiff _).mpr ⟨A, hA, rfl⟩, ?_⟩
  intro π hπ
  obtain ⟨B, hB, rfl⟩ := (hiff π).mp hπ
  rw [huniq B hB]

/-- Both original iid colors give an almost surely unique distance assignment. Target
injectivity and cost-difference atomlessness are both derived from the original geometry. -/
theorem ae_existsUnique_bipartiteDistanceAssignment (ν : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Fin (n + 1) → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXi : ProbabilityTheory.iIndepFun X P) (hYi : ProbabilityTheory.iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hXY : ProbabilityTheory.IndepFun (fun sample i ↦ X i sample) (fun sample j ↦ Y j sample) P) :
    let _instFinslerIIDBipartiteMetric : MetricSpace M := F.metricSpace
    ∀ᵐ sample ∂P, ∃! σ, OptimalAssignment (fun i j ↦ dist (X i sample) (Y j sample)) σ := by
  let _instFinslerIIDBipartiteProofMetric : MetricSpace M := F.metricSpace
  let _instFinslerIIDBipartiteProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instFinslerIIDBipartiteNull : NullSingletonClass ν :=
    nullSingletonClass_of_chartwise_ac m ν hdim hνchart
  apply Probability.ae_existsUnique_optimalAssignment_of_bipartite_iid_atomless
    P μ ν X Y hX hY hXi hYi hXlaw hYlaw hXY dist
  · exact (continuous_fst.dist continuous_snd).measurable
  · intro y z hyz
    exact hF.nullSingletonClass_map_distance_sub m μ hdim hμchart hcomplete hyz

/-- The two original iid colors have a singleton whole fractional optimal face almost surely. -/
theorem ae_existsUnique_bipartiteDistanceFractionalAssignment (ν : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Fin (n + 1) → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXi : ProbabilityTheory.iIndepFun X P) (hYi : ProbabilityTheory.iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hXY : ProbabilityTheory.IndepFun (fun sample i ↦ X i sample) (fun sample j ↦ Y j sample) P) :
    let _instFinslerIIDBipartiteFractionalMetric : MetricSpace M := F.metricSpace
    ∀ᵐ sample ∂P, ∃! A,
      OptimalFractionalAssignment (fun i j ↦ dist (X i sample) (Y j sample)) A := by
  let _instFinslerIIDBipartiteFractionalProofMetric : MetricSpace M := F.metricSpace
  filter_upwards [hF.ae_existsUnique_bipartiteDistanceAssignment m μ ν hdim hμchart hνchart
    hcomplete P X Y hX hY hXi hYi hXlaw hYlaw hXY] with sample hsample
  exact existsUnique_optimalFractionalAssignment_of_existsUnique_optimalAssignment _ hsample

/-- The original two-color iid empirical marginals have exactly one optimal coupling almost
surely, among all feasible measures, for the original Finsler length distance. -/
theorem ae_existsUnique_bipartiteDistanceEmpiricalCoupling (ν : Measure M)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Fin (n + 1) → Ω → M)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXi : ProbabilityTheory.iIndepFun X P) (hYi : ProbabilityTheory.iIndepFun Y P)
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hXY : ProbabilityTheory.IndepFun (fun sample i ↦ X i sample) (fun sample j ↦ Y j sample) P) :
    let _instFinslerIIDBipartiteCouplingMetric : MetricSpace M := F.metricSpace
    ∀ᵐ sample ∂P, ∃! π : Measure (M × M),
      IsOptimalCoupling edist (empiricalMeasure (fun i ↦ X i sample))
        (empiricalMeasure (fun j ↦ Y j sample)) π := by
  let _instFinslerIIDBipartiteCouplingProofMetric : MetricSpace M := F.metricSpace
  filter_upwards [hF.ae_existsUnique_bipartiteDistanceFractionalAssignment m μ ν
    hdim hμchart hνchart hcomplete P X Y hX hY hXi hYi hXlaw hYlaw hXY] with sample hsample
  obtain ⟨A, hA, huniq⟩ := hsample
  have hdist : (edist : M → M → ℝ≥0∞) = fun x y ↦ ENNReal.ofReal (dist x y) :=
    funext fun x ↦ funext fun y ↦ edist_dist x y
  have hiff (π : Measure (M × M)) :
      IsOptimalCoupling edist (empiricalMeasure (fun i ↦ X i sample))
          (empiricalMeasure (fun j ↦ Y j sample)) π ↔
        ∃ B, OptimalFractionalAssignment (fun i j ↦ dist (X i sample) (Y j sample)) B ∧
          fractionalEmpiricalMeasure (fun i ↦ X i sample) (fun j ↦ Y j sample) B = π := by
    rw [hdist]
    exact isOptimalCoupling_empirical_iff_exists_optimalFractional
      (fun i ↦ X i sample) (fun j ↦ Y j sample) dist (fun _ _ ↦ dist_nonneg) π
  refine ⟨fractionalEmpiricalMeasure (fun i ↦ X i sample) (fun j ↦ Y j sample) A,
    (hiff _).mpr ⟨A, hA, rfl⟩, ?_⟩
  intro π hπ
  obtain ⟨B, hB, rfl⟩ := (hiff π).mp hπ
  rw [huniq B hB]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
