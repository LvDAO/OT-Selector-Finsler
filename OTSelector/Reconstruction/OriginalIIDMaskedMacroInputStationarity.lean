import OTSelector.Reconstruction.OriginalIIDMaskedMacroInputJointLaw
import OTSelector.Reconstruction.MarkedStationaryValueHaarRootConditionalPhysical

/-!
# Conditional stationarity of the same original masked iid inputs and optimal plans

The immutable physical mask filters original labels before spatial rooting.
Both full input measures retain their original clocks and multiplicities while
sharing the actual optimizer's Haar-root change. The retained macroscopic root
is fixed by the limiting joint action.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology ENNReal CompactlySupported BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

variable {ι : Type*} [Fintype ι]
local instance maskedInputStationarityPointPolish :
    PolishSpace (LocalFiniteMeasure ((ι → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance maskedInputStationarityPlanPolish :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance maskedInputStationarityPointNonempty :
    Nonempty (LocalFiniteMeasure ((ι → ℝ) × ℝ)) := ⟨⟨0, inferInstance⟩⟩
local instance maskedInputStationarityPlanNonempty :
    Nonempty (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  ⟨⟨0, inferInstance⟩⟩

/-- The unchanged two original plans and both literal masked input measures. -/
abbrev OriginalIIDMaskedMacroInputScene (ι : Type*) [Fintype ι] :=
  CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ×
    (LocalFiniteMeasure ((ι → ℝ) × ℝ) × LocalFiniteMeasure ((ι → ℝ) × ℝ))

/-- The same spatial reroot acts on every original plan and input point, keeping
both physical clocks and every original input multiplicity. -/
def originalIIDMaskedMacroInputSceneReroot (v : ι → ℝ)
    (s : OriginalIIDMaskedMacroInputScene ι) : OriginalIIDMaskedMacroInputScene ι :=
  (physicalSceneReroot v s.1,
    (localFiniteMapHomeomorph (physicalScenePointReroot v) s.2.1,
      localFiniteMapHomeomorph (physicalScenePointReroot v) s.2.2))

/-- Full input/plan rerooting is continuous in the original vague scene. -/
theorem continuous_originalIIDMaskedMacroInputSceneReroot (v : ι → ℝ) :
    Continuous (originalIIDMaskedMacroInputSceneReroot v) :=
  ((continuous_physicalSceneReroot v).comp continuous_fst).prodMk
    (((continuous_localFiniteMapHomeomorph _).comp continuous_snd.fst).prodMk
      ((continuous_localFiniteMapHomeomorph _).comp continuous_snd.snd))

/-- For a fixed full input measure, its spatial reroot varies continuously with
the physical root while the original clock coordinate is fixed. -/
theorem continuous_physicalScenePointReroot_localMeasure
    (μ : LocalFiniteMeasure ((ι → ℝ) × ℝ)) :
    Continuous (fun v : ι → ℝ ↦ localFiniteMapHomeomorph (physicalScenePointReroot v) μ) := by
  have hpoint : Continuous (fun p : (ι → ℝ) × ((ι → ℝ) × ℝ) ↦
      physicalScenePointReroot p.1 p.2) :=
    (continuous_snd.fst.sub continuous_fst).prodMk continuous_snd.snd
  have hcancel (v : ι → ℝ) (x : (ι → ℝ) × ℝ) :
      physicalScenePointReroot (-v) (physicalScenePointReroot v x) = x := by
    simp only [physicalScenePointReroot_apply, sub_neg_eq_add, sub_add_cancel]
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  change Continuous (fun v ↦ LocalFiniteMeasure.testIntegral
    (localFiniteMapHomeomorph (physicalScenePointReroot v) μ) f)
  have heq : (fun v ↦ LocalFiniteMeasure.testIntegral
      (localFiniteMapHomeomorph (physicalScenePointReroot v) μ) f) =
      (fun v ↦ ∫ x, f (physicalScenePointReroot v x) ∂(μ : Measure _)) := by
    funext v
    exact integral_map (physicalScenePointReroot v).continuous.measurable.aemeasurable
      f.continuous.aestronglyMeasurable
  rw [heq]
  apply continuous_iff_continuousAt.mpr
  intro v₀
  let U : Set (ι → ℝ) := Metric.closedBall v₀ 1
  let pull : (ι → ℝ) × ((ι → ℝ) × ℝ) → ((ι → ℝ) × ℝ) :=
    fun p ↦ physicalScenePointReroot (-p.1) p.2
  let K := pull '' (U ×ˢ tsupport f)
  have hpull : Continuous pull := hpoint.comp (continuous_fst.neg.prodMk continuous_snd)
  have hK : IsCompact K := ((isCompact_closedBall v₀ 1).prod f.hasCompactSupport).image hpull
  have hzero : ∀ v x, v ∈ U → x ∉ K → f (physicalScenePointReroot v x) = 0 := by
    intro v x hv hx
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    exact hx ⟨(v, physicalScenePointReroot v x), ⟨hv, hmem⟩, hcancel v x⟩
  have hc : ContinuousOn (fun v : ι → ℝ ↦
      ∫ x, f (physicalScenePointReroot v x) ∂(μ : Measure _)) U :=
    continuousOn_integral_of_compact_support hK (f.continuous.comp hpoint).continuousOn hzero
  exact hc.continuousAt (Metric.closedBall_mem_nhds _ (by norm_num))

/-- Both true input measures and both true plan coordinates share continuity
in the physical reroot parameter on the complete joint scene. -/
theorem continuous_originalIIDMaskedMacroInputSceneReroot_parameter
    (s : OriginalIIDMaskedMacroInputScene ι) :
    Continuous (fun v : ι → ℝ ↦ originalIIDMaskedMacroInputSceneReroot v s) :=
  (continuous_physicalSceneReroot_parameter s.1).prodMk
    ((continuous_physicalScenePointReroot_localMeasure s.2.1).prodMk
      (continuous_physicalScenePointReroot_localMeasure s.2.2))

variable {M : Type*} [MeasurableSpace M]
variable (base : (ι → ℝ) × ℝ)
local instance maskedInputStationarityPointStandardBorel :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance maskedInputStationarityConfigTopology :
    TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance maskedInputStationarityConfigBorel :
    BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance maskedInputStationarityConfigPolish :
    PolishSpace (LocalConfiguration base) := vaguePolishSpace
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "Macro" => (ι → ℝ) × (PairScene × LocalConfiguration base)

omit [MeasurableSpace M] in
/-- An exact counting-measure cocycle moves each retained original label once.
The physical H-mask is independent of the root and repeated points stay repeated. -/
theorem map_countingMeasure_ofMaskedTuple_physical_reroot {n : ℕ}
    (H : Set M) (coord : M → (ι → ℝ)) (u : M → ℝ) (sample : Fin n → M)
    (z v : ι → ℝ) :
    (countingMeasure (ofMaskedTuple base H (fun x ↦ (coord x - z, u x)) sample)).map
        (physicalScenePointReroot v) =
      countingMeasure (ofMaskedTuple base H (fun x ↦ (coord x - (z + v), u x)) sample) := by
  classical
  simp only [countingMeasure_ofMaskedTuple]
  rw [Measure.map_finset_sum' (physicalScenePointReroot v).continuous.measurable.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [Measure.map_dirac' (physicalScenePointReroot v).continuous.measurable]
    congr 1
    simp only [physicalScenePointReroot_apply, sub_sub]
  · simp only [Measure.map_zero]

omit [MeasurableSpace M] in
/-- The literal masked configuration's actual locally finite measure obeys the
same exact root change as both original optimizer plans. -/
theorem physicalScenePointReroot_maskedInputConfiguration {Ω : Type*} {n : ℕ}
    (H : Set M) (coord : M → (ι → ℝ)) (u : M → ℝ)
    (Y : Ω → Fin (n + 1) → M) (w : Ω) (z v : ι → ℝ) :
    localFiniteMapHomeomorph (physicalScenePointReroot v)
      (toLocalFiniteMeasure (physicalSceneRootedMaskedInputConfiguration base H coord u Y (w,z))) =
        toLocalFiniteMeasure
          (physicalSceneRootedMaskedInputConfiguration base H coord u Y (w,z+v)) := by
  apply Subtype.ext
  exact map_countingMeasure_ofMaskedTuple_physical_reroot base H coord u (Y w) z v

/-- Retain the common original macro tag, both actual plan coordinates and the
two full input measures of the SAME optimized masked macro observation. -/
def originalIIDMaskedMacroInputSceneProjection (s : Macro × Macro) :
    (ι → ℝ) × OriginalIIDMaskedMacroInputScene ι :=
  (s.1.1, (s.1.2.1, originalIIDMaskedMacroInputProjection base s))

omit [MeasurableSpace M] in
/-- All original plan and full-input coordinates are continuous projections. -/
theorem continuous_originalIIDMaskedMacroInputSceneProjection :
    Continuous (originalIIDMaskedMacroInputSceneProjection base) :=
  continuous_fst.fst.prodMk
    (continuous_fst.snd.fst.prodMk (continuous_originalIIDMaskedMacroInputProjection base))

/-- This readout uses the actual source-H-restricted iid optimizer together
with the two full original H-masked input arrays at the very same spatial root. -/
def originalIIDMaskedMacroInputSceneObservation
    (cost : M → M → ℝ) (k : ℝ) (n : ℕ) (H : Set M)
    (coord : M → (ι → ℝ)) (u : M → ℝ)
    (w : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) × (ι → ℝ)) :
    OriginalIIDMaskedMacroInputScene ι :=
  let Γ := fun ξ ↦ (originalIIDOptimalPhysicalPlan (n := n + 1) cost k ξ).restrict (H ×ˢ univ)
  (physicalSceneRootedLocalScene Γ Γ coord u ((n : ℝ) + 1) w,
    originalIIDMaskedMacroInputReadout base n H coord u w)

/-- The full continuous projection is exactly its literal original scene and
original macroscopic root, with no new sampling or discarded multiplicities. -/
theorem originalIIDMaskedMacroInputSceneProjection_observation
    (cost : M → M → ℝ) (k : ℝ) (n : ℕ) (H : Set M)
    (coord : M → (ι → ℝ)) (u : M → ℝ) (scale : ℝ)
    (w : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) × (ι → ℝ)) :
    originalIIDMaskedMacroInputSceneProjection base
      (originalIIDMaskedBipartiteMacroObservation base cost k n H coord u scale w) =
      (physicalSceneMacroscopicRoot scale w.2,
        originalIIDMaskedMacroInputSceneObservation base cost k n H coord u w) := rfl

/-- The original finite scene jointly measurably retains the optimizer and both inputs. -/
theorem measurable_originalIIDMaskedMacroInputSceneObservation
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) :
    Measurable (originalIIDMaskedMacroInputSceneObservation base cost k n H coord u) :=
  ((continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.comp
    (measurable_originalIIDMaskedBipartiteMacroObservation base cost hcost k n H hH
      coord hcoord u hu 0)).snd

/-- The SAME optimal finite plan and literal two original input arrays obey one
exact root-change cocycle; H and the original clocks remain fixed. -/
theorem originalIIDMaskedMacroInputSceneReroot_observation
    (cost : M → M → ℝ) (k : ℝ) (n : ℕ) (H : Set M)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (w : (Fin (n + 1) → M) × (Fin (n + 1) → M)) (z v : ι → ℝ) :
    originalIIDMaskedMacroInputSceneReroot v
      (originalIIDMaskedMacroInputSceneObservation base cost k n H coord u (w,z)) =
        originalIIDMaskedMacroInputSceneObservation base cost k n H coord u (w,z+v) := by
  let Γ : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) → Measure (M × M) :=
    fun ξ ↦ (originalIIDOptimalPhysicalPlan (n := n + 1) cost k ξ).restrict (H ×ˢ univ)
  apply Prod.ext
  · change physicalSceneReroot v (physicalSceneRootedLocalScene Γ Γ coord u ((n : ℝ) + 1)
      (w,z)) = physicalSceneRootedLocalScene Γ Γ coord u ((n : ℝ) + 1) (w,z+v)
    exact physicalSceneReroot_localScene v Γ Γ coord hcoord u hu ((n : ℝ) + 1) w z
  · apply Prod.ext
    · exact physicalScenePointReroot_maskedInputConfiguration base H coord u
        (fun ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M) ↦ ξ.1) w z v
    · exact physicalScenePointReroot_maskedInputConfiguration base H coord u
        (fun ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M) ↦ ξ.2) w z v

/-- The continuous full input/plan marginal of the actual masked macro law. -/
def originalIIDMaskedMacroInputSceneLaw
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) :
    ProbabilityMeasure ((ι → ℝ) × OriginalIIDMaskedMacroInputScene ι) :=
  (originalIIDMaskedBipartiteMacroLaw base μ ν hq cost hcost k n H hH coord hcoord u hu).map
    (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable

/-- The full marginal is the Haar average of the original jointly observed
optimizer and both masked input arrays, with its true original mass n+1. -/
theorem originalIIDMaskedMacroInputSceneLaw_eq_haarCubeAverageLaw
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) :
    (originalIIDMaskedMacroInputSceneLaw base μ ν hq cost hcost k n H hH coord hcoord u hu :
      Measure ((ι → ℝ) × OriginalIIDMaskedMacroInputScene ι)) =
      haarCubeAverageLaw
        ((Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))
        (fun w ↦ (physicalSceneMacroscopicRoot
            (2 * haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)) w.2,
          originalIIDMaskedMacroInputSceneObservation base cost k n H coord u w))
        (haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)) := by
  rw [originalIIDMaskedMacroInputSceneLaw, ProbabilityMeasure.toMeasure_map]
  change ((((Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))).prod (cavityRootMeasure volume
      (haarRootCube ι (haarRootRadius (Fintype.card ι) ((n : ℝ) + 1))) ((n : ℝ) + 1))).map
      (originalIIDMaskedBipartiteMacroObservation base cost k n H coord u
        (2 * haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)))).map
      (originalIIDMaskedMacroInputSceneProjection base) = _
  rw [Measure.map_map (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable
    (measurable_originalIIDMaskedBipartiteMacroObservation base cost hcost k n H hH
      coord hcoord u hu _)]
  simp only [Function.comp_def, originalIIDMaskedMacroInputSceneProjection_observation]
  rw [haarCubeAverageLaw, haarCubeRootLaw, haarRootRadius_mass _ hq (by positivity)]

/-- Every prescribed weak law of the original optimized masked macro experiment
retains its full input/plan marginal along the SAME sample subsequence. -/
theorem tendsto_originalIIDMaskedMacroInputSceneLaw_of_tendsto
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (m : ℕ → ℕ)
    {Q : ProbabilityMeasure (Macro × Macro)}
    (hweak : Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu) atTop (𝓝 Q)) :
    Tendsto (fun n ↦ originalIIDMaskedMacroInputSceneLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu) atTop
      (𝓝 (Q.map
        (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hweak
    (continuous_originalIIDMaskedMacroInputSceneProjection base)

/-- The actual optimized H-masked joint weak scene is stationary together with
BOTH full original input measures. On one common full-measure set of retained
macro roots, its conditional law is invariant under EVERY physical translation. -/
theorem joint_and_ae_conditional_originalIIDMaskedMacroInputSceneReroot_of_tendsto
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    {Q : ProbabilityMeasure (Macro × Macro)}
    (hweak : Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu) atTop (𝓝 Q)) :
    let ρ := (Q.map
      (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable :
        Measure ((ι → ℝ) × OriginalIIDMaskedMacroInputScene ι))
    (∀ v : ι → ℝ, MeasurePreserving (Prod.map id (originalIIDMaskedMacroInputSceneReroot v))
      ρ ρ) ∧
      ∀ᵐ w ∂ρ.fst, ∀ v : ι → ℝ,
        MeasurePreserving (originalIIDMaskedMacroInputSceneReroot v)
          (ρ.condKernel w) (ρ.condKernel w) := by
  let P := fun n ↦ (Measure.pi (fun _ : Fin (m n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (m n + 1) ↦ ν))
  let N := fun n ↦ (m n : ℝ) + 1
  let radius := fun n ↦ haarRootRadius (Fintype.card ι) (N n)
  have hR (n : ℕ) : 0 < radius n := haarRootRadius_pos _ (by dsimp [N]; positivity)
  have hNlarge : Tendsto N atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop.comp hm)
  have hRlarge : Tendsto radius atTop atTop := tendsto_haarRootRadius _ hq hNlarge
  have hslarge : Tendsto (fun n ↦ 2 * radius n) atTop atTop :=
    hRlarge.const_mul_atTop (by norm_num)
  let scene := fun n ↦ originalIIDMaskedMacroInputSceneObservation base
    (cost (m n)) (k (m n)) (m n) H (coord (m n)) u
  have hscene (n : ℕ) : Measurable (scene n) :=
    measurable_originalIIDMaskedMacroInputSceneObservation base
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu
  let laws := fun n ↦ originalIIDMaskedMacroInputSceneLaw base μ ν hq
    (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
    (coord (m n)) (hcoord (m n)) u hu
  have hlaw (n : ℕ) : (laws n : Measure ((ι → ℝ) × OriginalIIDMaskedMacroInputScene ι)) =
      haarCubeAverageLaw (P n)
        (fun p ↦ ((fun i ↦ p.2 i / (2 * radius n)), scene n p)) (radius n) :=
    originalIIDMaskedMacroInputSceneLaw_eq_haarCubeAverageLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu
  let Qfull : ProbabilityMeasure ((ι → ℝ) × OriginalIIDMaskedMacroInputScene ι) := Q.map
    (continuous_originalIIDMaskedMacroInputSceneProjection base).measurable.aemeasurable
  have hfull : Tendsto laws atTop (𝓝 Qfull) :=
    tendsto_originalIIDMaskedMacroInputSceneLaw_of_tendsto base μ ν hq
      cost hcost k H hH coord hcoord u hu m hweak
  have hjoint (v : ι → ℝ) :
      MeasurePreserving (Prod.map id (originalIIDMaskedMacroInputSceneReroot v))
        (Qfull : Measure ((ι → ℝ) × OriginalIIDMaskedMacroInputScene ι))
        (Qfull : Measure ((ι → ℝ) × OriginalIIDMaskedMacroInputScene ι)) :=
    measurePreserving_macroRoot_of_haarCubeAverageLaw_tendsto P scene hscene
      radius (fun n ↦ 2 * radius n) hR hRlarge hslarge laws hlaw hfull
      (continuous_originalIIDMaskedMacroInputSceneReroot v) v
      (fun n w z ↦ originalIIDMaskedMacroInputSceneReroot_observation base
        (cost (m n)) (k (m n)) (m n) H (coord (m n)) (hcoord (m n)) u hu w z v)
  refine ⟨hjoint, ?_⟩
  have hdense : DenseRange (fun r : ι → ℚ ↦ (fun i ↦ (r i : ℝ))) :=
    DenseRange.piMap (fun _ ↦ Rat.denseRange_cast)
  exact ae_forall_measurePreserving_condKernel_of_joint_dense
    (Qfull : Measure ((ι → ℝ) × OriginalIIDMaskedMacroInputScene ι))
    originalIIDMaskedMacroInputSceneReroot
    (fun v ↦ (continuous_originalIIDMaskedMacroInputSceneReroot v).measurable)
    continuous_originalIIDMaskedMacroInputSceneReroot_parameter _ hdense
    (fun r ↦ hjoint (fun i ↦ (r i : ℝ)))

end OTSelector.Reconstruction
