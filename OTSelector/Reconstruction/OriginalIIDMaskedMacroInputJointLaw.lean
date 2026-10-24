import OTSelector.Probability.IndependentRootReadoutKernel
import OTSelector.Reconstruction.OriginalIIDMaskedBipartiteMacroScene
import OTSelector.Reconstruction.OriginalIIDFullSeedInputKernel

/-!
# The actual original masked macro input law as a root/kernel product

The existing masked macro optimizer observation retains the same n+1 iid observations in
each color, original endpoint masks and multiplicities, and microscopic spatial root z.
Its two input coordinates have the exact already-defined fixed-root input law as fibers.
The macroscopic tag scale does not change the input readout; no tag rescaling is used here.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000

variable {M ι : Type*} [MeasurableSpace M] [Fintype ι]

local instance iidMaskedMacroInputJointPointStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance

local instance iidMaskedMacroInputJointConfigurationTopology (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) :=
  LocalConfiguration.vagueTopology base

/-- The two literal endpoint-masked original clouds observed at the original microscopic root.
This is the input projection of the existing optimizer/macro observation. -/
def originalIIDMaskedMacroInputReadout (base : (ι → ℝ) × ℝ)
    (n : ℕ) (H : Set M) (coord : M → (ι → ℝ)) (u : M → ℝ)
    (v : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) × (ι → ℝ)) :
    LocalFiniteMeasure ((ι → ℝ) × ℝ) × LocalFiniteMeasure ((ι → ℝ) × ℝ) :=
  (LocalConfiguration.toLocalFiniteMeasure
      (physicalSceneRootedMaskedInputConfiguration base H coord u (fun ξ ↦ ξ.1) v),
    LocalConfiguration.toLocalFiniteMeasure
      (physicalSceneRootedMaskedInputConfiguration base H coord u (fun ξ ↦ ξ.2) v))

/-- Original input coordinates of the SAME masked macro optimizer are exactly this readout;
its tag scale and matching cost do not alter either input cloud. -/
theorem originalIIDMaskedBipartiteMacroObservation_input_readout
    (base : (ι → ℝ) × ℝ) (cost : M → M → ℝ) (k : ℝ) (n : ℕ)
    (H : Set M) (coord : M → (ι → ℝ)) (u : M → ℝ) (scale : ℝ)
    (v : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) × (ι → ℝ)) :
    let s := originalIIDMaskedBipartiteMacroObservation base cost k n H coord u scale v
    (LocalConfiguration.toLocalFiniteMeasure s.1.2.2,
      LocalConfiguration.toLocalFiniteMeasure s.2.2.2) =
      originalIIDMaskedMacroInputReadout base n H coord u v := rfl

/-- Root and original iid arrays jointly measurably determine the unchanged masked input pair. -/
theorem measurable_originalIIDMaskedMacroInputReadout
    (base : (ι → ℝ) × ℝ) (n : ℕ) {H : Set M} (hH : MeasurableSet H)
    {coord : M → (ι → ℝ)} (hcoord : Measurable coord)
    {u : M → ℝ} (hu : Measurable u) :
    Measurable (originalIIDMaskedMacroInputReadout base n H coord u) := by
  have hs := measurable_physicalSceneRootedMaskedInputConfiguration base H hH
    coord hcoord u hu (fun ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M) ↦ ξ.1)
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
  have ht := measurable_physicalSceneRootedMaskedInputConfiguration base H hH
    coord hcoord u hu (fun ξ : (Fin (n + 1) → M) × (Fin (n + 1) → M) ↦ ξ.2)
    (fun j ↦ (measurable_pi_apply j).comp measurable_snd)
  exact ((measurable_originalConfigurationLocalFinite base).comp hs).prodMk
    ((measurable_originalConfigurationLocalFinite base).comp ht)

/-- Conditional original masked input law given the SAME microscopic spatial root. -/
def originalIIDMaskedMacroInputKernel (base : (ι → ℝ) × ℝ)
    (μ ν : Measure M) (n : ℕ) (H : Set M) (coord : M → (ι → ℝ)) (u : M → ℝ) :
    Kernel (ι → ℝ)
      (LocalFiniteMeasure ((ι → ℝ) × ℝ) × LocalFiniteMeasure ((ι → ℝ) × ℝ)) :=
  originalIndependentRootReadoutKernel
    ((Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))
    (originalIIDMaskedMacroInputReadout base n H coord u)

/-- Each fixed-root fiber is exactly the already-defined actual original iid input-pair law,
with n+1 original observations in each color and the original endpoint mask. -/
theorem originalIIDMaskedMacroInputKernel_apply
    (base : (ι → ℝ) × ℝ) (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    {H : Set M} (hH : MeasurableSet H)
    {coord : M → (ι → ℝ)} (hcoord : Measurable coord)
    {u : M → ℝ} (hu : Measurable u) (z : ι → ℝ) :
    originalIIDMaskedMacroInputKernel base μ ν n H coord u z =
      originalIidMaskedLocalInputPairMeasure μ ν (n + 1) base H H
        (fun x ↦ (coord x - z, u x)) (fun x ↦ (coord x - z, u x)) := by
  rw [originalIIDMaskedMacroInputKernel, originalIndependentRootReadoutKernel_apply _
    (measurable_originalIIDMaskedMacroInputReadout base n hH hcoord hu)]
  exact (originalIidMaskedLocalInputPairMeasure_eq_map μ ν (n + 1) base hH hH
    ((hcoord.sub measurable_const).prodMk hu)
    ((hcoord.sub measurable_const).prodMk hu)).symm

/-- The conditional masked input law is Markov at every original root. -/
theorem isMarkovKernel_originalIIDMaskedMacroInputKernel
    (base : (ι → ℝ) × ℝ) (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ)
    {H : Set M} (hH : MeasurableSet H)
    {coord : M → (ι → ℝ)} (hcoord : Measurable coord)
    {u : M → ℝ} (hu : Measurable u) :
    IsMarkovKernel (originalIIDMaskedMacroInputKernel base μ ν n H coord u) := by
  apply isMarkovKernel_originalIndependentRootReadoutKernel
  exact measurable_originalIIDMaskedMacroInputReadout base n hH hcoord hu

/-- The original optimizer's two masked input coordinates and unchanged root have the exact
root/kernel factorization. No optimizer, iid sample, mask, or root is resampled. -/
theorem originalIIDMaskedMacroInputJointLaw_eq_compProd
    (base : (ι → ℝ) × ℝ) (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (ρ : Measure (ι → ℝ)) [SFinite ρ]
    (cost : M → M → ℝ) (k : ℝ) (n : ℕ)
    {H : Set M} (hH : MeasurableSet H)
    {coord : M → (ι → ℝ)} (hcoord : Measurable coord)
    {u : M → ℝ} (hu : Measurable u) (scale : ℝ) :
    (((Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (n + 1) ↦ ν))).prod ρ).map
      (fun v ↦ (v.2,
        (LocalConfiguration.toLocalFiniteMeasure
          (originalIIDMaskedBipartiteMacroObservation base cost k n H coord u scale v).1.2.2,
          LocalConfiguration.toLocalFiniteMeasure
          (originalIIDMaskedBipartiteMacroObservation base cost k n H coord u scale v).2.2.2))) =
      ρ ⊗ₘ originalIIDMaskedMacroInputKernel base μ ν n H coord u := by
  exact map_prod_root_readout_eq_compProd _ ρ
    (measurable_originalIIDMaskedMacroInputReadout base n hH hcoord hu)

/-- Forget the original optimizer and macro tags, retaining the actual two masked input measures. -/
def originalIIDMaskedMacroInputProjection (base : (ι → ℝ) × ℝ)
    (s : (((ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ×
      LocalConfiguration base)) ×
      ((ι → ℝ) × (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ×
      LocalConfiguration base)))) :
    LocalFiniteMeasure ((ι → ℝ) × ℝ) × LocalFiniteMeasure ((ι → ℝ) × ℝ) :=
  (LocalConfiguration.toLocalFiniteMeasure s.1.2.2,
    LocalConfiguration.toLocalFiniteMeasure s.2.2.2)

/-- Reading the original two masked input measures is a measurable marginal map. -/
theorem measurable_originalIIDMaskedMacroInputProjection (base : (ι → ℝ) × ℝ) :
    Measurable (originalIIDMaskedMacroInputProjection base) := by
  exact ((measurable_originalConfigurationLocalFinite base).comp
    (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk
    ((measurable_originalConfigurationLocalFinite base).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))

/-- The actual two-input marginal map is continuous for the existing vague configuration
and compact-test locally finite measure topologies. -/
theorem continuous_originalIIDMaskedMacroInputProjection (base : (ι → ℝ) × ℝ) :
    Continuous (originalIIDMaskedMacroInputProjection base) := by
  exact (LocalConfiguration.continuous_toLocalFiniteMeasure.comp
    (continuous_snd.comp (continuous_snd.comp continuous_fst))).prodMk
    (LocalConfiguration.continuous_toLocalFiniteMeasure.comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd)))

/-- The INPUT marginal of the already-defined original Haar-rooted masked macro optimizer law
is the integrated actual fixed-root input kernel. The same n+1 iid samples and Haar root law
are used literally on both sides. -/
theorem originalIIDMaskedBipartiteMacroLaw_input_marginal_eq
    (base : (ι → ℝ) × ℝ) (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hq : 0 < Fintype.card ι)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost)) (k : ℝ) (n : ℕ)
    {H : Set M} (hH : MeasurableSet H)
    {coord : M → (ι → ℝ)} (hcoord : Measurable coord)
    {u : M → ℝ} (hu : Measurable u) :
    let R := haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)
    let ρ := cavityRootMeasure volume (haarRootCube ι R) ((n : ℝ) + 1)
    (originalIIDMaskedBipartiteMacroLaw base μ ν hq cost hcost k n H hH
      coord hcoord u hu : Measure _).map (originalIIDMaskedMacroInputProjection base) =
      (ρ ⊗ₘ originalIIDMaskedMacroInputKernel base μ ν n H coord u).map Prod.snd := by
  let R := haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)
  let ρ := cavityRootMeasure volume (haarRootCube ι R) ((n : ℝ) + 1)
  have : SFinite ρ := by dsimp [ρ, cavityRootMeasure]; infer_instance
  let P := (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
  have hf := measurable_originalIIDMaskedMacroInputReadout base n hH hcoord hu
  have hm := measurable_originalIIDMaskedBipartiteMacroObservation base
    cost hcost k n H hH coord hcoord u hu (2 * R)
  have hjoint : (P.prod ρ).map
      (fun v ↦ (v.2, originalIIDMaskedMacroInputReadout base n H coord u v)) =
      ρ ⊗ₘ originalIIDMaskedMacroInputKernel base μ ν n H coord u :=
    map_prod_root_readout_eq_compProd P ρ hf
  change ((P.prod ρ).map
    (originalIIDMaskedBipartiteMacroObservation base cost k n H coord u (2 * R))).map
    (originalIIDMaskedMacroInputProjection base) = _
  rw [Measure.map_map (measurable_originalIIDMaskedMacroInputProjection base) hm,
    ← hjoint, Measure.map_map measurable_snd (measurable_snd.prodMk hf)]
  rfl

end OTSelector.Reconstruction
