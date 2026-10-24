import OTSelector.Probability.KernelBaseMarginal
import OTSelector.Reconstruction.FinslerPopulationSeedIntensityCompactCore
import OTSelector.Probability.ConditionalLabelCoreRecovery

/-!
# The original joint population law in actual seed coordinates

The retained physical population pushes forward to its original Haar intensity
and its original scalar conditional kernel. Both colors use the same original
base measure and the same actual coordinate map.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false



variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The original clock kernel read at the original root of an actual seed label.
Outside the actual labels it is completed by the fixed point mass at zero. -/
def populationSeedCoordinateClockKernel (S : F.CalibratedLevelSeedPatch u)
    (a : M → Z) (ha : Measurable a) (k : Kernel Z ℝ) : Kernel S.covector.ker ℝ where
  toFun := extend ((↑) : S.labels → S.covector.ker)
    (fun w ↦ k (a (S.curve w 0))) (fun _ ↦ Measure.dirac 0)
  measurable' := (MeasurableEmbedding.subtype_coe S.labels_measurable).measurable_extend
    (k.measurable.comp (ha.comp (continuousOn_iff_continuous_domRestrict.mp
      ((S.continuous_at_time 0).mono S.labels_subset)).measurable)) measurable_const

omit [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
    [MeasurableSpace.CountablySeparated Z] in
/-- On every actual seed label the coordinate kernel is the original kernel exactly. -/
theorem populationSeedCoordinateClockKernel_at_label
    (S : F.CalibratedLevelSeedPatch u) (a : M → Z) (ha : Measurable a)
    (k : Kernel Z ℝ) (w : S.labels) :
    populationSeedCoordinateClockKernel S a ha k w = k (a (S.curve w 0)) := by
  change extend ((↑) : S.labels → S.covector.ker)
    (fun v ↦ k (a (S.curve v 0))) (fun _ ↦ Measure.dirac 0) w = _
  exact Subtype.val_injective.extend_apply _ _ w

/-- The harmless completion outside actual labels preserves probability kernels. -/
instance isMarkovKernel_populationSeedCoordinateClockKernel
    (S : F.CalibratedLevelSeedPatch u) (a : M → Z) (ha : Measurable a)
    (k : Kernel Z ℝ) [IsMarkovKernel k] :
    IsMarkovKernel (populationSeedCoordinateClockKernel S a ha k) := by
  constructor
  intro w
  by_cases hw : ∃ v : S.labels, (v : S.covector.ker) = w
  · obtain ⟨v, rfl⟩ := hw
    rw [populationSeedCoordinateClockKernel_at_label]
    infer_instance
  · change IsProbabilityMeasure (extend ((↑) : S.labels → S.covector.ker)
      (fun v ↦ k (a (S.curve v 0))) (fun _ ↦ Measure.dirac 0) w)
    rw [Function.extend_apply' _ _ _ hw]
    infer_instance

variable (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
  (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
  [IsFiniteMeasure lambda]
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instIntensityLawMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The original physical joint law on any retained root core is exactly the
original Haar intensity times the original conditional clock kernel. -/
theorem original_seed_core_joint_eq_compProd_of_joint
    (η : Measure M) [IsFiniteMeasure η]
    (j : ℕ) [SigmaFinite (κ j)] {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j)
    (hjoint : (η.restrict (a ⁻¹' K)).map (fun x ↦ (a x, u x)) =
      lambda.restrict K ⊗ₘ condDistrib u a η) :
    (η.restrict (a ⁻¹' K)).map
        (fun x ↦ (populationSeedRootLabelValue (P j).seed a (a x), u x)) =
      (((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K)).withDensity
        (populationSeedPieceHaarDensity P a κ lambda j)) ⊗ₘ
          populationSeedCoordinateClockKernel (P j).seed a ha (condDistrib u a η) := by
  let _instIntensityLawMetric : MetricSpace M := F.metricSpace
  let r := populationSeedRootLabelValue (P j).seed a
  have hr : Measurable r :=
    measurable_populationSeedRootLabelValue (P j).seed hF hcomplete hu ha hinj
  have heq : ∀ᵐ z ∂lambda.restrict K,
      populationSeedCoordinateClockKernel (P j).seed a ha (condDistrib u a η) (r z) =
        condDistrib u a η z := by
    filter_upwards [ae_restrict_mem hK] with z hz
    dsimp only [r]
    rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj j ⟨z, hsub hz⟩,
      populationSeedCoordinateClockKernel_at_label,
      populationSeedPieceLabel_root P a κ lambda j ⟨z, hsub hz⟩]
  calc
    _ = ((η.restrict (a ⁻¹' K)).map (fun x ↦ (a x, u x))).map (Prod.map r id) := by
      rw [Measure.map_map (hr.prodMap measurable_id) (ha.prodMk hu.continuous.measurable)]
      rfl
    _ = (lambda.restrict K).map r ⊗ₘ
        populationSeedCoordinateClockKernel (P j).seed a ha (condDistrib u a η) := by
      rw [hjoint, map_compProd_base_of_ae_kernel_eq _ _ _ hr heq]
    _ = _ := by
      rw [map_populationSeedCore_eq_withDensity P a κ lambda hF hcomplete hu ha hinj j hK hsub]

/-- The same exact coordinate law follows directly from the original common
label marginal, with no supplied local conditional-law assumption. -/
theorem original_seed_core_joint_eq_compProd
    (η : Measure M) [IsFiniteMeasure η] (hlabel : η.map a = lambda)
    (j : ℕ) [SigmaFinite (κ j)] {K : Set Z} (hK : MeasurableSet K)
    (hsub : K ⊆ populationSeedRootPiece P a κ lambda j) :
    (η.restrict (a ⁻¹' K)).map
        (fun x ↦ (populationSeedRootLabelValue (P j).seed a (a x), u x)) =
      (((κ j).restrict (populationSeedRootLabelValue (P j).seed a '' K)).withDensity
        (populationSeedPieceHaarDensity P a κ lambda j)) ⊗ₘ
          populationSeedCoordinateClockKernel (P j).seed a ha (condDistrib u a η) := by
  let _instIntensityLawMetric : MetricSpace M := F.metricSpace
  apply original_seed_core_joint_eq_compProd_of_joint P a κ lambda
    hF hcomplete hu ha hinj η j hK hsub
  simpa only [hlabel] using
    original_label_clock_restrict_eq_compProd η ha hu.continuous.measurable hK

end OTSelector.Reconstruction
