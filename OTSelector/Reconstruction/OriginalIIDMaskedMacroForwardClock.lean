import OTSelector.Reconstruction.OriginalIIDMaskedMacroTailReadout
import OTSelector.Reconstruction.OriginalIIDFixedSeedCompactPartnerTails
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitClock
import OTSelector.Reconstruction.OriginalIIDSupportedSpatialEnergy

/-!
# Forward clock gaps in the same original masked macro weak law

The exact original macro-law scene projection is the existing source-restricted rooted
physical-scene law. A finite index shift consumes an eventual actual original iid energy
bound, retaining the same weak subsequence and original optimizer. Original support
carriers and the existing clock-limit theorem then give its positive forward gap.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess OTSelector.PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 20000

variable {M ι : Type*} [MeasurableSpace M] [Fintype ι]
variable (base : (ι → ℝ) × ℝ)
local instance iidMaskedMacroForwardPointStandardBorel :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance iidMaskedMacroForwardConfigurationTopology :
    TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance iidMaskedMacroForwardConfigurationBorel :
    BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance iidMaskedMacroForwardConfigurationPolish :
    PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance iidMaskedMacroForwardPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
set_option quotPrecheck false
local notation "Point" => (ι → ℝ) × ℝ
local notation "Edge" => Point × Point
local notation "PairScene" => CavityLocalScene Point Point
local notation "Macro" => (ι → ℝ) × (PairScene × LocalConfiguration base)

/-- The original two physical plans retained by the first macro record. -/
def originalIIDMaskedMacroSceneProjection (s : Macro × Macro) : PairScene := s.1.2.1

/-- Forgetting only the tag and input cloud is continuous. -/
theorem continuous_originalIIDMaskedMacroSceneProjection :
    Continuous (originalIIDMaskedMacroSceneProjection base) := continuous_fst.snd.fst

/-- The original pair-scene marginal is measurable. -/
theorem measurable_originalIIDMaskedMacroSceneProjection :
    Measurable (originalIIDMaskedMacroSceneProjection base) := measurable_fst.snd.fst

/-- The actual macro law's scene marginal is exactly the existing original restricted
physical-scene law, with its same iid arrays, optimizer, source mask and Haar root. -/
theorem originalIIDMaskedMacroLaw_scene_projection_eq
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι) (cost : M → M → ℝ)
    (hcost : Measurable (Function.uncurry cost)) (k : ℝ) (n : ℕ)
    {H : Set M} (hH : MeasurableSet H) {coord : M → (ι → ℝ)} (hcoord : Measurable coord)
    {u : M → ℝ} (hu : Measurable u) :
    (originalIIDMaskedBipartiteMacroLaw base μ ν hq cost hcost k n H hH
      coord hcoord u hu).map (measurable_originalIIDMaskedMacroSceneProjection base).aemeasurable =
      physicalSceneRestrictedRootedLocalSceneLaw
        ((Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν)))
        (originalIIDOptimalPhysicalPlan cost k) (originalIIDOptimalPhysicalPlan cost k)
        (measurable_originalIIDOptimalPhysicalPlan cost hcost k)
        (measurable_originalIIDOptimalPhysicalPlan cost hcost k)
        H hH coord hcoord u hu ((n : ℝ) + 1) (by positivity)
        (haarRootCube ι (haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)))
        (volume_haarRootCube_radius ι hq (by positivity)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.map _ _).map (originalIIDMaskedMacroSceneProjection base) = _
  rw [Measure.map_map (measurable_originalIIDMaskedMacroSceneProjection base)
    (measurable_originalIIDMaskedBipartiteMacroObservation base cost hcost k n H hH
      coord hcoord u hu (2 * haarRootRadius (Fintype.card ι) ((n : ℝ) + 1)))]
  rfl

section ActualLimit
variable [MetricSpace M] [BorelSpace M]

/-- An eventual true energy bound of the SAME original iid optimizer gives a positive clock
gap in every actual masked macro weak subsequence. Only a finite prefix is dropped to make
the already-proved energy bound uniform; the weak limit and original experiment are retained. -/
theorem ae_originalIIDMaskedMacro_weak_limit_clock_gap
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι) {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hdist : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (selectionScale : ℕ → ℝ) (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (energyScale : ℕ → ℝ) (henergyScale : ∀ n, 0 < energyScale n)
    (henergyTop : Tendsto energyScale atTop atTop)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal
        (energyScale n * (dist p.1 p.2 - u p.2 + u p.1))
        ∂originalIIDOptimalPhysicalPlan (cost n) (selectionScale n) ξ
        ∂(Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n + 1) ↦ ν))) ≤ C)
    (m : ℕ → ℕ) (hm : StrictMono m) (Q : ProbabilityMeasure (Macro × Macro))
    (hweak : Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν hq
      (cost (m n)) (hcost (m n)) (selectionScale (m n)) (m n) (H (m n)) (hH (m n))
      (coord (m n)) (hcoord (m n)) u hu.continuous.measurable) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (Macro × Macro)),
      (∀ᵐ e ∂(s.1.2.1.1 : Measure Edge), gap / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(s.1.2.1.2 : Measure Edge), gap / 2 ≤ e.2.2 - e.1.2) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hm.tendsto_atTop.eventually henergy)
  let index := fun n ↦ m (n + N₀)
  let Penv := fun n ↦ (Measure.pi (fun _ : Fin (index n + 1) ↦ μ)).prod
    (Measure.pi (fun _ : Fin (index n + 1) ↦ ν))
  let Γ : ∀ n, ((Fin (index n + 1) → M) × (Fin (index n + 1) → M)) →
      Measure (M × M) := fun n ↦
    originalIIDOptimalPhysicalPlan (n := index n + 1) (cost (index n)) (selectionScale (index n))
  have hΓ (n : ℕ) : Measurable (Γ n) :=
    measurable_originalIIDOptimalPhysicalPlan (cost (index n)) (hcost (index n))
      (selectionScale (index n))
  have hcarried (n : ℕ) : ∀ᵐ ξ ∂Penv n, ∀ᵐ p ∂Γ n ξ, p.1 ∈ A ∧ p.2 ∈ B :=
    ae_originalIIDOptimalPhysicalPlan_carried μ ν (cost (index n)) (hcost (index n))
      (selectionScale (index n)) hμ hν
  have hbound (n : ℕ) : (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal
      (energyScale (index n) * (dist p.1 p.2 - u p.2 + u p.1)) ∂Γ n ξ ∂Penv n) ≤ C :=
    hN₀ (n + N₀) (Nat.le_add_left N₀ n)
  have hindex : Tendsto index atTop atTop :=
    hm.tendsto_atTop.comp (tendsto_add_atTop_nat N₀)
  have hwshift := hweak.comp (tendsto_add_atTop_nat N₀)
  let Qscene := Q.map (measurable_originalIIDMaskedMacroSceneProjection base).aemeasurable
  have hwscene := ((ProbabilityMeasure.continuous_map
    (continuous_originalIIDMaskedMacroSceneProjection base)).tendsto Q).comp hwshift
  have hmap (n : ℕ) := originalIIDMaskedMacroLaw_scene_projection_eq base μ ν hq
    (cost (index n)) (hcost (index n)) (selectionScale (index n)) (index n)
    (hH (index n)) (hcoord (index n)) hu.continuous.measurable
  have hwphysical : Tendsto (fun n ↦ physicalSceneRestrictedRootedLocalSceneLaw (Penv n)
      (Γ n) (Γ n) (hΓ n) (hΓ n) (H (index n)) (hH (index n))
      (coord (index n)) (hcoord (index n)) u hu.continuous.measurable
      ((index n : ℝ) + 1) (by positivity)
      (haarRootCube ι (haarRootRadius (Fintype.card ι) ((index n : ℝ) + 1)))
      (volume_haarRootCube_radius ι hq (by positivity))) atTop (𝓝 Qscene) := by
    simpa only [Function.comp_def, index, hmap] using hwscene
  have hlegal := ae_physicalSceneRootedLocalScene_limit_clock_legal Penv Γ Γ hΓ hΓ
    hgap hdist hcarried hcarried (fun n ↦ H (index n)) (fun n ↦ hH (index n))
    (fun n ↦ coord (index n)) (fun n ↦ hcoord (index n)) hu
    (fun n ↦ energyScale (index n)) (fun n ↦ henergyScale (index n))
    (henergyTop.comp hindex) (fun n ↦ (index n : ℝ) + 1) (fun _ ↦ by positivity)
    (fun n ↦ haarRootCube ι (haarRootRadius (Fintype.card ι) ((index n : ℝ) + 1)))
    (fun n ↦ volume_haarRootCube_radius ι hq (by positivity)) C hC hbound hbound
    Qscene hwphysical
  exact ae_of_ae_map (measurable_originalIIDMaskedMacroSceneProjection base).aemeasurable hlegal

end ActualLimit
end OTSelector.Reconstruction

namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess OTSelector.PointProcess.LocalConfiguration
open Metric Module Manifold OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped ContDiff CompactlySupported BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 20000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure]
  {μ ν : ProbabilityMeasure M} {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ}
  {b : (ℚ → M) × ℝ → M} {r : ℝ} {δ loss : ℝ≥0∞}

variable (j : ℕ) (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local instance iidMaskedMacroForwardSupportedPointStandardBorel : StandardBorelSpace
    ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) := inferInstance
local instance iidMaskedMacroForwardSupportedConfigurationTopology :
    TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance iidMaskedMacroForwardSupportedConfigurationBorel :
    BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance iidMaskedMacroForwardSupportedConfigurationPolish :
    PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance iidMaskedMacroForwardSupportedPlanPolish : PolishSpace (LocalFiniteMeasure
    (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ×
      ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
set_option quotPrecheck false
local notation "Point" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ
local notation "Macro" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) ×
  (CavityLocalScene Point Point × LocalConfiguration base)

/-- The proved original supported pressure data themselves supply the eventual true energy
budget, so the SAME actual supported-optimizer macro weak subsequence has its original
positive forward clock gap. No energy-budget, forward-law, or legality callback is assumed. -/
theorem PopulationLocalPressureCore.ae_originalIID_supported_masked_macro_clock_gap
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A) (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ ((μ : Measure M).map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (bins : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ)
    (Ksupport : Set M) (hK : IsCompact Ksupport)
    (hμK : ∀ᵐ x ∂(μ : Measure M), x ∈ Ksupport)
    (hνK : ∀ᵐ y ∂(ν : Measure M), y ∈ Ksupport)
    (f : (Ksupport × Ksupport) →ᵇ ℝ) (g : (M × M) →ᵇ ℝ) (ε probeError : ℝ)
    (hdata : D.originalSupportedWeightUnitDensityPressureData γ originalGap bins U
      retentionError splitError Ksupport hK hμK hνK f g ε probeError
      (fun n ↦ canonicalLaw μ ν n) (fun n ↦ canonicalX n) (fun n ↦ canonicalY n))
    (t : ℝ) (spatialScale : ℕ → ℝ) (hsp : ∀ n, 0 < spatialScale n)
    (hscale : Tendsto (fun n ↦ spatialScale n ^ 2) atTop atTop)
    (hnorm : ∀ n, spatialScale n ^ 2 = finslerMeanScale E n)
    (hq : 0 < finrank ℝ (P j).seed.covector.ker) :
    let supportedCost := fun n x y ↦ finslerMeanScale E n *
      ((F.lengthEDist x y).toReal - u y + u x) +
        t * finslerCarrierProbe μ ν Ksupport hK.measurableSet hμK hνK f x y
    ∀ m : ℕ → ℕ, StrictMono m → ∀ Q : ProbabilityMeasure (Macro × Macro),
      Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw base μ ν (by simpa using hq)
        (supportedCost (m n))
        (measurable_originalIID_supported_tilt_cost hcomplete μ ν
          Ksupport hK.measurableSet hμK hνK u hu f (finslerMeanScale E (m n)) t)
        1 (m n)
        (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
          (lambda := (μ : Measure M).map a) j)
        (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
        (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale (m n)))
        (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j
          (spatialScale (m n))) u
        (by let _inst : MetricSpace M := F.metricSpace; exact hu.continuous.measurable))
        atTop (𝓝 Q) →
      ∀ᵐ s ∂(Q : Measure (Macro × Macro)),
        (∀ᵐ e ∂(s.1.2.1.1 : Measure (Point × Point)), gap / 2 ≤ e.2.2 - e.1.2) ∧
        (∀ᵐ e ∂(s.1.2.1.2 : Measure (Point × Point)), gap / 2 ≤ e.2.2 - e.1.2) := by
  let _inst : MetricSpace M := F.metricSpace
  let supportedCost := fun n x y ↦ finslerMeanScale E n *
    ((F.lengthEDist x y).toReal - u y + u x) +
      t * finslerCarrierProbe μ ν Ksupport hK.measurableSet hμK hνK f x y
  have hcost (n : ℕ) : Measurable (Function.uncurry (supportedCost n)) :=
    measurable_originalIID_supported_tilt_cost hcomplete μ ν
      Ksupport hK.measurableSet hμK hνK u hu f (finslerMeanScale E n) t
  obtain ⟨C, hC, hbudget⟩ := D.exists_eventually_originalIID_supported_spatial_energy_bound
    hcomplete hu γ originalGap bins U retentionError splitError Ksupport hK hμK hνK
    f g ε probeError hdata t spatialScale hnorm
  have hmask : MeasurableSet (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := (μ : Measure M).map a) j) :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  have hcoord (n : ℕ) : Measurable
      (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n)) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j
      (spatialScale n)
  dsimp only
  intro m hm Q hweak
  exact ae_originalIIDMaskedMacro_weak_limit_clock_gap base (μ : Measure M) (ν : Measure M)
    (by simpa using hq) hgap hdist hμA hνB supportedCost hcost (fun _ ↦ 1)
    (fun _ ↦ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := (μ : Measure M).map a) j) (fun _ ↦ hmask)
    (fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (spatialScale n))
    hcoord hu (fun n ↦ spatialScale n ^ 2) (fun n ↦ sq_pos_of_pos (hsp n)) hscale
    C hC hbudget m hm Q hweak

end OTSelector.Reconstruction
