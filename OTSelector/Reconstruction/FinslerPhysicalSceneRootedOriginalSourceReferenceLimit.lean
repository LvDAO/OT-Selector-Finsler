import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRetainedSourceReference
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedSourceReferenceLaw
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedActualMaskedJoint

/-!
# Original allocation source references through both scene limits

Global feasibility identifies the actual original source law before rooting.
Its finite source references pass through the same fixed-tilt sample limit and
then the tilt limit, with the actual target cloud and restricted columns kept
jointly throughout. No source-readout or frozen-reference premise is supplied.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)



local instance originalSourceReferenceLimitStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalSourceReferenceLimitConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalSourceReferenceLimitConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalSourceReferenceLimitConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalSourceReferenceLimitPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

variable (j : ℕ)
set_option quotPrecheck false
local notation "V" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)
local notation "Point" => ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "Edge" => (Point × Point)
variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene Point Point
local notation "MacroScene" => V × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)
/-- The same original globally feasible families produce the retained source
reference on their actual joint scene, through the sample limit and then the
tilt limit. The caller supplies no frozen reference or source-readout bound. -/
theorem exists_original_allocation_retained_source_reference_of_iterated
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, (κ j).IsAddHaarMeasure]
    (U : Set V) (hU : IsOpen U) (hUfinite : volume U ≠ ⊤)
    (error : ℝ≥0∞) (herror : error ≠ 0)
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (Penv : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (Penv n)]
    (ap am : ∀ (_ℓ n : ℕ), Ωn n → M → Fin (m n + 1) → ℝ)
    (hpm : ∀ ℓ n k, Measurable (fun z : Ωn n × M ↦ ap ℓ n z.1 z.2 k))
    (hmm : ∀ ℓ n k, Measurable (fun z : Ωn n × M ↦ am ℓ n z.1 z.2 k))
    (Y : ∀ n, Ωn n → Fin (m n + 1) → M)
    (hY : ∀ n k, Measurable (fun w ↦ Y n w k))
    (weights : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (hfp : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation η₀ (weights n w) (ap ℓ n w))
    (hfm : ∀ ℓ n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation η₀ (weights n w) (am ℓ n w))
    (A B : Set M) (hA : MeasurableSet A) (hB : MeasurableSet B) (nearRadius : ℝ)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hnormalization : ∀ n, scale n ^ finrank ℝ (P j).seed.covector.ker = (m n : ℝ) + 1)
    (rootDomain : ℕ → Set V)
    (hrootDomain : ∀ n, volume (rootDomain n) = ENNReal.ofReal ((m n : ℝ) + 1)) :
    ∃ reference : Measure Point,
      IsFiniteMeasure reference ∧ reference.OuterRegular ∧
      reference ≪ (volume : Measure V).prod (volume : Measure ℝ) ∧
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
    let Egood := D.retainedNearCarrierEvent A B nearRadius
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let laws : ℕ → ℕ → ProbabilityMeasure JointScene := fun ℓ n ↦
      actualAllocationRootedMaskedMacroscopicSceneLaw base (Penv n) η₀
        (ap ℓ n) (am ℓ n) (hpm ℓ n) (hmm ℓ n) (Y n) (hY n)
        H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j)
        Egood (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
        (coord n) (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n))
        u (by let _inst : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)
        (scale n) (rootDomain n) (hrootDomain n)
    ∀ (Q : ℕ → ProbabilityMeasure JointScene) (R : ProbabilityMeasure JointScene)
      (φ : ℕ → ℕ → ℕ), (∀ ℓ, Tendsto (φ ℓ) atTop atTop) → ∀ ψ : ℕ → ℕ,
      (∀ ℓ, Tendsto (fun n ↦ laws ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ))) →
      Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R) →
      ∀ᵐ (s : JointScene) ∂(R : Measure JointScene),
        sourceOpenDominationDefectOn (s.2.1.1 : Measure Edge) (U ×ˢ univ) reference error ∧
        sourceOpenDominationDefectOn (s.2.1.2 : Measure Edge) (U ×ˢ univ) reference error ∧
        sourceOpenDominationDefectOn
          (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge) (U ×ˢ univ) reference error := by
  let _inst : MetricSpace M := F.metricSpace
  obtain ⟨reference, hfinite, hregular, hac, hbound⟩ :=
    D.exists_original_retained_source_window_reference_of_accuracy j hF hcomplete hu ha hinj
      U hU.measurableSet hUfinite error herror
  refine ⟨reference, hfinite, hregular, hac, ?_⟩
  dsimp only
  intro Q R φ hφ ψ hinner houter
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j
  let Egood := D.retainedNearCarrierEvent A B nearRadius
  let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
  have hH : MeasurableSet H := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
  have hE : MeasurableSet Egood :=
    D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n)
  let Γp := fun ℓ n ↦ physicalSceneGlobalAllocationFamily η₀ (ap ℓ n) (Y n)
  let Γm := fun ℓ n ↦ physicalSceneGlobalAllocationFamily η₀ (am ℓ n) (Y n)
  have hsp (ℓ n : ℕ) : ∀ᵐ w ∂Penv n, (Γp ℓ n w).fst = η₀ := by
    filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq (Penv n) η₀
      (ap ℓ n) (Y n) (weights n) (hfp ℓ n), hfp ℓ n] with w he hw
    dsimp only [Γp, Γm]
    rw [he, physicalSceneAllocationPlan_fst hw (Y n w)]
  have hsm (ℓ n : ℕ) : ∀ᵐ w ∂Penv n, (Γm ℓ n w).fst = η₀ := by
    filter_upwards [physicalSceneGlobalAllocationFamily_ae_eq (Penv n) η₀
      (am ℓ n) (Y n) (weights n) (hfm ℓ n), hfm ℓ n] with w he hw
    dsimp only [Γp, Γm]
    rw [he, physicalSceneAllocationPlan_fst hw (Y n w)]
  have hphysical (n : ℕ) (Γ : Measure (M × M)) (hfst : Γ.fst = η₀) (root : V) :
      sourceOpenDominationDefectOn
        (physicalSceneRootedPlan ((Γ.restrict Egood).restrict (H ×ˢ univ))
          (coord n) u ((m n : ℝ) + 1) root) (U ×ˢ univ) reference error := by
    intro O hO
    have hb := hbound (scale n) (hscale n) root Γ hfst A B nearRadius O hO.measurableSet
    rw [hnormalization n] at hb
    have heq : ((Γ.restrict Egood).restrict (H ×ˢ univ)) = Γ.restrict (Egood ∩ (H ×ˢ univ)) := by
      rw [Measure.restrict_restrict (hH.prod MeasurableSet.univ), inter_comm]
    rw [← heq, Measure.fst_apply (hO.measurableSet.inter (hU.measurableSet.prod MeasurableSet.univ))] at hb
    have htest : (Prod.fst : Edge → Point) ⁻¹' (O ∩ (U ×ˢ univ)) =
        (O ∩ (U ×ˢ univ)) ×ˢ univ := by
      ext e
      simp
    simpa only [htest, coord] using hb
  apply ae_sourceReference_of_iterated_physicalSceneRootedMaskedMacroscopicSceneLaw base m Penv Γp Γm
    (fun ℓ n ↦ measurable_physicalSceneGlobalAllocationFamily η₀ (ap ℓ n) (hpm ℓ n) (Y n) (hY n))
    (fun ℓ n ↦ measurable_physicalSceneGlobalAllocationFamily η₀ (am ℓ n) (hmm ℓ n) (Y n) (hY n))
    (fun _ ↦ H) (fun _ ↦ hH) Egood hE coord hcoord u hu.continuous.measurable scale Y hY
    rootDomain hrootDomain (U ×ˢ univ) (hU.prod isOpen_univ) reference error ?_
    Q R φ hφ ψ hinner houter
  intro ℓ
  exact Eventually.of_forall fun n ↦ by
    filter_upwards [hsp ℓ n, hsm ℓ n] with w hwp hwm root
    exact ⟨hphysical n (Γp ℓ n w) hwp root, hphysical n (Γm ℓ n w) hwm root⟩

end PopulationLocalPressureCore
end OTSelector.Reconstruction
