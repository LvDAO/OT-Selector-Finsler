import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedClockCoreOffset
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalOtherCoreCarrier
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreCarrierOpen
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRetainedMacroCarrier
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedJoint

/-!
# The actual selected original macro core carries both retained clock laws

Clock pairs outside a selected original closed pair window are carried by
other disjoint original macro cores before rooting. Open-mask concentration
then removes that bad clock mass at every selected macro label, through both
original weak stages and on the same actual joint scene.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

local instance originalClockCarrierConcentrationStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalClockCarrierConcentrationConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalClockCarrierConcentrationConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalClockCarrierConcentrationConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalClockCarrierConcentrationPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)

variable (j : ℕ)
set_option quotPrecheck false
local notation "Edge" => (((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) × ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ))
variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ) ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "MacroScene" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The actual original retained plans vanish outside the finite original
compact label union in their SAME prescribed sample and tilt weak limits.
Only literal source membership and the actual original coordinate are used;
there is no finite-n shrinking-offset or limiting carrier oracle. -/
theorem ae_original_retained_plans_clock_carrier_of_iterated
    (i : Fin D.haar.continuous.count)
    (hseed : (D.haar.continuous.coefficient i).seedIndex = j)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (A B : Set M) (hA : MeasurableSet A) (hB : MeasurableSet B) (nearRadius : ℝ)
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (Penv : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (Penv n)]
    (ap am : ∀ (_ℓ n : ℕ), Ωn n → M → Fin (n + 1) → ℝ)
    (hpm : ∀ ℓ n k, Measurable (fun z : Ωn n × M ↦ ap ℓ n z.1 z.2 k))
    (hmm : ∀ ℓ n k, Measurable (fun z : Ωn n × M ↦ am ℓ n z.1 z.2 k))
    (Y : ∀ n, Ωn n → Fin (n + 1) → M)
    (hY : ∀ n k, Measurable (fun w ↦ Y n w k))
    (scale : ℕ → ℝ) (hscalePos : ∀ n, 0 < scale n)
    (hscale : Tendsto scale atTop atTop)
    (rootDomain : ℕ → Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ))
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((n : ℝ) + 1)) :
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
    let laws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦ actualAllocationRootedMaskedMacroscopicSceneLaw base (Penv n) μ
      (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (Y n) (hY n)
      H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
      (D.retainedNearCarrierEvent A B nearRadius)
      (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
      (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n))
      (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n))
      u (by
        let _inst : MetricSpace M := F.metricSpace
        exact hu.continuous.measurable) (scale n) (rootDomain n) (hrootDomain n)
    ∀ (Q : ℕ → ProbabilityMeasure JointScene) (Rlaw : ProbabilityMeasure JointScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) → ∀ ψ : ℕ → ℕ,
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 Rlaw) →
      (∀ ℓ, ∀ᵐ (s : JointScene) ∂(Q ℓ : Measure JointScene),
        s.1.1 ∈ (physicalSceneOriginalMacroLabel (P := P) (a := a) j '' (D.haar.continuous.coefficient i).roots) →
          ((s.2.1.1 : Measure Edge) {e : Edge | (e.1.2, e.2.2) ∉ (D.haar.continuous.coefficient i).window.region} = 0 ∧
            (s.2.1.2 : Measure Edge) {e : Edge | (e.1.2, e.2.2) ∉ (D.haar.continuous.coefficient i).window.region} = 0)) ∧
      ∀ᵐ (s : JointScene) ∂(Rlaw : Measure JointScene),
        s.1.1 ∈ (physicalSceneOriginalMacroLabel (P := P) (a := a) j '' (D.haar.continuous.coefficient i).roots) →
          ((s.2.1.1 : Measure Edge) {e : Edge | (e.1.2, e.2.2) ∉ (D.haar.continuous.coefficient i).window.region} = 0 ∧
            (s.2.1.2 : Measure Edge) {e : Edge | (e.1.2, e.2.2) ∉ (D.haar.continuous.coefficient i).window.region} = 0) := by
  let _inst : MetricSpace M := F.metricSpace
  dsimp only
  intro Q Rlaw φ hφ ψ hinner houter
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
  have hH : MeasurableSet H := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  let Egood := D.retainedNearCarrierEvent A B nearRadius
  have hEgood : MeasurableSet Egood :=
    D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius
  let coord := physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j
  have hcoord : Measurable coord := by
    have hc := measurable_physicalSceneOriginalSeedScaledPosition
      (P := P) (a := a) hF hcomplete hu ha hinj j 1
    change Measurable (fun x ↦ (1 : ℝ) • coord x) at hc
    simpa only [one_smul] using hc
  let laws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦ actualAllocationRootedMaskedMacroscopicSceneLaw base (Penv n) μ
    (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (Y n) (hY n) H hH Egood hEgood
    (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n))
    (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n))
    u hu.continuous.measurable (scale n) (rootDomain n) (hrootDomain n)
  let K := D.originalRetainedOtherMacroCarrier j i
  have hK : IsCompact K := D.isCompact_originalRetainedOtherMacroCarrier j i
  let clockBad : Set Edge := {e | (e.1.2, e.2.2) ∉ (D.haar.continuous.coefficient i).window.region}
  have hclockBad : IsOpen clockBad :=
    (D.haar.continuous.coefficient i).window.isCompact_region.isClosed.isOpen_compl.preimage
      (continuous_fst.snd.prodMk continuous_snd.snd)
  have hT : MeasurableSet (D.haar.continuous.coefficient i).window.regionᶜ :=
    (D.haar.continuous.coefficient i).window.isCompact_region.measurableSet.compl
  have hdisj := D.disjoint_originalMacroLabel_otherCarrier hF hcomplete hu ha hinj j i hseed
  have hfinite (ℓ n : ℕ) : ∀ᵐ (s : JointScene) ∂(laws ℓ n : Measure JointScene),
      (∀ᵐ e ∂(s.2.1.1 : Measure Edge), (e.1.2, e.2.2) ∈ (D.haar.continuous.coefficient i).window.regionᶜ → s.1.1 + (scale n)⁻¹ • e.1.1 ∈ K) ∧
      (∀ᵐ e ∂(s.2.1.2 : Measure Edge), (e.1.2, e.2.2) ∈ (D.haar.continuous.coefficient i).window.regionᶜ → s.1.1 + (scale n)⁻¹ • e.1.1 ∈ K) := by
    change ∀ᵐ (s : JointScene) ∂(physicalSceneRootedMaskedMacroscopicSceneLaw base (Penv n)
      (physicalSceneGlobalAllocationFamily μ (ap ℓ n) (Y n))
      (physicalSceneGlobalAllocationFamily μ (am ℓ n) (Y n))
      (measurable_physicalSceneGlobalAllocationFamily μ (ap ℓ n) (hpm ℓ n) (Y n) (hY n))
      (measurable_physicalSceneGlobalAllocationFamily μ (am ℓ n) (hmm ℓ n) (Y n) (hY n))
      H hH Egood hEgood (fun x ↦ scale n • coord x) (hcoord.const_smul (scale n))
      u hu.continuous.measurable (scale n) (Y n) (hY n) (rootDomain n) (hrootDomain n) :
        Measure JointScene),
      (∀ᵐ e ∂(s.2.1.1 : Measure Edge), (e.1.2, e.2.2) ∈ (D.haar.continuous.coefficient i).window.regionᶜ → s.1.1 + (scale n)⁻¹ • e.1.1 ∈ K) ∧
      (∀ᵐ e ∂(s.2.1.2 : Measure Edge), (e.1.2, e.2.2) ∈ (D.haar.continuous.coefficient i).window.regionᶜ → s.1.1 + (scale n)⁻¹ • e.1.1 ∈ K)
    exact ae_physicalSceneRootedMaskedMacroscopicSceneLaw_clockCoreOffset base (Penv n)
      (physicalSceneGlobalAllocationFamily μ (ap ℓ n) (Y n))
      (physicalSceneGlobalAllocationFamily μ (am ℓ n) (Y n))
      (measurable_physicalSceneGlobalAllocationFamily μ (ap ℓ n) (hpm ℓ n) (Y n) (hY n))
      (measurable_physicalSceneGlobalAllocationFamily μ (am ℓ n) (hmm ℓ n) (Y n) (hY n))
      H hH Egood hEgood coord hcoord u hu.continuous.measurable (hscalePos n).ne'
      (Y n) (hY n) (rootDomain n) (hrootDomain n) hT hK.measurableSet
      (fun w ↦ D.ae_original_retainedNear_badClock_source_mem_otherMacroCarrier hF hcomplete hu ha hinj j i
        (physicalSceneGlobalAllocationFamily μ (ap ℓ n) (Y n) w) A B hA hB nearRadius)
      (fun w ↦ D.ae_original_retainedNear_badClock_source_mem_otherMacroCarrier hF hcomplete hu ha hinj j i
        (physicalSceneGlobalAllocationFamily μ (am ℓ n) (Y n) w) A B hA hB nearRadius)
  have hp := ae_physicalSceneOpenCoreCarrier_of_iterated_weak laws Q Rlaw φ ψ hinner houter
    (fun s : JointScene ↦ s.1.1) continuous_fst.fst
    (fun s ↦ s.2.1.1) continuous_snd.fst.fst hK.isClosed hclockBad
    (fun ℓ n ↦ scale (φ ℓ n)) (fun ℓ n ↦ hscalePos (φ ℓ n))
    (fun ℓ ↦ hscale.comp (hφ ℓ))
    (fun ℓ n ↦ (hfinite ℓ (φ ℓ n)).mono fun _ hs ↦ hs.1)
  have hm := ae_physicalSceneOpenCoreCarrier_of_iterated_weak laws Q Rlaw φ ψ hinner houter
    (fun s : JointScene ↦ s.1.1) continuous_fst.fst
    (fun s ↦ s.2.1.2) continuous_snd.fst.snd hK.isClosed hclockBad
    (fun ℓ n ↦ scale (φ ℓ n)) (fun ℓ n ↦ hscalePos (φ ℓ n))
    (fun ℓ ↦ hscale.comp (hφ ℓ))
    (fun ℓ n ↦ (hfinite ℓ (φ ℓ n)).mono fun _ hs ↦ hs.2)
  have combine (L : ProbabilityMeasure JointScene)
      (hLp : ∀ᵐ (s : JointScene) ∂(L : Measure JointScene),
        s.1.1 ∈ K ∨ (s.2.1.1 : Measure Edge) clockBad = 0)
      (hLm : ∀ᵐ (s : JointScene) ∂(L : Measure JointScene),
        s.1.1 ∈ K ∨ (s.2.1.2 : Measure Edge) clockBad = 0) :
      ∀ᵐ (s : JointScene) ∂(L : Measure JointScene),
        s.1.1 ∈ (physicalSceneOriginalMacroLabel (P := P) (a := a) j '' (D.haar.continuous.coefficient i).roots) →
          ((s.2.1.1 : Measure Edge) clockBad = 0 ∧
            (s.2.1.2 : Measure Edge) clockBad = 0) := by
    filter_upwards [hLp, hLm] with s hs ht htag
    have hnot : s.1.1 ∉ K := fun hk ↦ Set.disjoint_left.mp hdisj htag hk
    exact ⟨hs.resolve_left hnot, ht.resolve_left hnot⟩
  exact ⟨fun ℓ ↦ combine (Q ℓ) (hp.1 ℓ) (hm.1 ℓ), combine Rlaw hp.2 hm.2⟩

end PopulationLocalPressureCore
end OTSelector.Reconstruction
