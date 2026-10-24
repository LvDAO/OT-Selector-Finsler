import OTSelector.Reconstruction.OriginalMarkedPressureLimitMeasurability
import OTSelector.Reconstruction.FinslerPopulationSeedPieceMoments
import OTSelector.Reconstruction.FinslerConcreteUpperModel

/-! Canonical original root pressure uses the literal general Finsler
inverse compliance and unchanged original conditional physical laws. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The literal original inverse-compliance quadratic cost in its actual seed basis. -/
def originalSeedRootKinetic (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (z : Z) (x y : ℝ) (v : Fin (finrank ℝ S.covector.ker) → ℝ) : ℝ :=
  matrixQuadratic (populationSeedRootCoefficient S a (Module.finBasis ℝ S.covector.ker)
    (z,(x,y))) v

/-- The original bounded physical probe read at the same actual population root. -/
def originalPhysicalRootProbe (b : Z × ℝ → M) (f : M × M →ᵇ ℝ)
    (z : Z) (x y : ℝ) : ℝ := f (b (z,x),b (z,y))

/-- The unchanged original finite-cloud pressure, with true scalar legality. -/
def originalSeedRootScalePressure (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (b : Z × ℝ → M) (f : M × M →ᵇ ℝ) (R t : ℝ) (z : Z) : ℝ :=
  legalMarkedScalePressure (finrank ℝ S.covector.ker) id id
    (condDistrib u a η₀ z) (condDistrib u a η₁ z)
    (originalSeedRootKinetic S a z) (originalPhysicalRootProbe b f z) R t

/-- The canonical thermodynamic limit of the literal original root pressure.
Its actual existence on original seed pieces is proved from the original laws. -/
def originalSeedRootPressure (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (b : Z × ℝ → M) (f : M × M →ᵇ ℝ) (z : Z) (t : ℝ) : ℝ :=
  limUnder atTop (fun R : ℝ ↦ originalSeedRootScalePressure S a η₀ η₁ b f R t z)

variable (S : F.CalibratedLevelSeedPatch u)
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  {a : M → Z} (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))

include hF hcomplete hu ha hinj

/-- The actual original quadratic cost is jointly Borel in root, clocks and displacement. -/
theorem measurable_originalSeedRootKinetic :
    Measurable (fun p : Z × ((ℝ × ℝ) × (Fin (finrank ℝ S.covector.ker) → ℝ)) ↦
      originalSeedRootKinetic S a p.1 p.2.1.1 p.2.1.2 p.2.2) := by
  exact continuous_matrixQuadratic.measurable.comp
    (((measurable_populationSeedRootCoefficient S hF hcomplete hu ha hinj
      (Module.finBasis ℝ S.covector.ker)).comp
        (show Measurable (fun p : Z × ((ℝ × ℝ) × (Fin (finrank ℝ S.covector.ker) → ℝ)) ↦
          (p.1,p.2.1)) by fun_prop)).prodMk (measurable_snd.comp measurable_snd))

omit hF hu ha hinj in
/-- Original physical probe measurability is inherited from its actual readout. -/
theorem measurable_originalPhysicalRootProbe {b : Z × ℝ → M} (hb : Measurable b)
    (f : M × M →ᵇ ℝ) :
    Measurable (fun p : Z × (ℝ × ℝ) ↦ originalPhysicalRootProbe b f p.1 p.2.1 p.2.2) := by
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  exact f.continuous.measurable.comp
    ((hb.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (hb.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))

/-- Every actual finite scale pressure is measurable in the original root,
including the original root-dependent physical tilt. -/
theorem measurable_originalSeedRootScalePressure
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {b : Z × ℝ → M} (hb : Measurable b) (f : M × M →ᵇ ℝ)
    (tilt : Z → ℝ) (htilt : Measurable tilt) (R : ℝ) :
    Measurable (fun z ↦ originalSeedRootScalePressure S a η₀ η₁ b f R (tilt z) z) :=
  measurable_original_legalMarkedScalePressure (finrank ℝ S.covector.ker)
    (condDistrib u a η₀) (condDistrib u a η₁) measurable_snd measurable_snd
    (measurable_originalSeedRootKinetic S hF hcomplete hu ha hinj)
    (measurable_originalPhysicalRootProbe hcomplete hb f) tilt htilt R

end OTSelector.Reconstruction
