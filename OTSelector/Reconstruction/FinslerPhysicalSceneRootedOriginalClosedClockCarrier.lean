import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalCoreConcentration
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalClockCarrierConcentration

/-!
# Actual retained plans carry original closed calibration windows

The carrier uses the SAME fixed original macro frame and each actual original
core label image with its closed clock window. Existing original core and clock
concentration supply this carrier through the separate sample and tilt limits.
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

local instance originalClosedClockCarrierStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalClosedClockCarrierConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalClosedClockCarrierConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalClosedClockCarrierConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalClosedClockCarrierPlanPolish {ι : Type*} [Fintype ι] :
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

/-- The original finite core-label and closed-clock relation in one fixed seed frame. -/
def originalClosedClockCarrier : Set (MacroScene × Edge) :=
  {se | ∃ i : Fin D.haar.continuous.count,
    (D.haar.continuous.coefficient i).seedIndex = j ∧
    se.1.1 ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
      (D.haar.continuous.coefficient i).roots ∧
    (se.2.1.2, se.2.2.2) ∈ (D.haar.continuous.coefficient i).window.region}

/-- The relation is Borel using only compact original label images and closed windows. -/
theorem measurableSet_originalClosedClockCarrier :
    MeasurableSet (D.originalClosedClockCarrier j base) := by
  rw [originalClosedClockCarrier, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hs : (D.haar.continuous.coefficient i).seedIndex = j
  · simp only [hs, true_and]
    have hlabel : ContinuousOn (populationSeedRootLabelValue (P j).seed a)
        (D.haar.continuous.coefficient i).roots := by
      rw [← hs, ← D.haar.intensity_roots i]
      exact (D.haar.intensity i).continuous_label
    have hK : IsCompact (physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
        (D.haar.continuous.coefficient i).roots) :=
      (D.haar.continuous.coefficient i).roots_compact.image_of_continuousOn
        ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.continuous.comp_continuousOn
          hlabel)
    exact (hK.measurableSet.preimage measurable_fst.fst).inter
      ((D.haar.continuous.coefficient i).window.isCompact_region.measurableSet.preimage
        (measurable_snd.fst.snd.prodMk measurable_snd.snd.snd))
  · simpa only [hs, false_and, Set.ofPred_false] using MeasurableSet.empty

/-- Finite original core and clock concentration jointly carry the actual retained average. -/
theorem ae_retained_average_originalClosedClockCarrier_of_concentration
    (L : ProbabilityMeasure JointScene)
    (hzero : ∀ᵐ s ∂(L : Measure JointScene),
      s.1.1 ∈ D.originalRetainedMacroCarrier j ∨
        ((s.2.1.1 : Measure Edge) = 0 ∧ (s.2.1.2 : Measure Edge) = 0))
    (hclock : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).seedIndex = j →
      ∀ᵐ s ∂(L : Measure JointScene),
        s.1.1 ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
          (D.haar.continuous.coefficient i).roots →
        ((s.2.1.1 : Measure Edge)
          {e : Edge | (e.1.2, e.2.2) ∉ (D.haar.continuous.coefficient i).window.region} = 0 ∧
         (s.2.1.2 : Measure Edge)
          {e : Edge | (e.1.2, e.2.2) ∉ (D.haar.continuous.coefficient i).window.region} = 0)) :
    ∀ᵐ s ∂(L : Measure JointScene),
      ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge),
        (s.1, e) ∈ D.originalClosedClockCarrier j base := by
  have hall : ∀ᵐ s ∂(L : Measure JointScene), ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).seedIndex = j →
      s.1.1 ∈ physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
        (D.haar.continuous.coefficient i).roots →
      ((s.2.1.1 : Measure Edge)
        {e : Edge | (e.1.2, e.2.2) ∉ (D.haar.continuous.coefficient i).window.region} = 0 ∧
       (s.2.1.2 : Measure Edge)
        {e : Edge | (e.1.2, e.2.2) ∉ (D.haar.continuous.coefficient i).window.region} = 0) := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : (D.haar.continuous.coefficient i).seedIndex = j
    · exact (hclock i hi).mono fun _ hs _ ↦ hs
    · exact ae_of_all _ fun _ h ↦ False.elim (hi h)
  filter_upwards [hzero, hall] with s hsource hs
  have hbad : (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge)
      {e : Edge | (s.1, e) ∉ D.originalClosedClockCarrier j base} = 0 := by
    rcases hsource with htag | hzero
    · obtain ⟨i, hi⟩ := mem_iUnion.mp htag
      by_cases hseed : (D.haar.continuous.coefficient i).seedIndex = j
      · rw [ite_eq_left hseed] at hi
        have hc := hs i hseed hi
        apply measure_mono_null (t :=
          {e : Edge | (e.1.2, e.2.2) ∉ (D.haar.continuous.coefficient i).window.region})
        · intro e he heclock
          exact he ⟨i, hseed, hi, heclock⟩
        · rw [LocalFiniteMeasure.coe_cavityAverage, Measure.smul_apply, Measure.add_apply,
            hc.1, hc.2]
          simp
      · rw [ite_eq_right hseed] at hi
        exact False.elim hi
    · rw [LocalFiniteMeasure.coe_cavityAverage, hzero.1, hzero.2]
      simp
  simpa only [Set.mem_ofPred_eq, not_not] using measure_eq_zero_iff_ae_notMem.mp hbad

/-- The SAME actual masked original-family limits inherit the closed original carrier. -/
theorem ae_original_retained_average_closed_clock_carrier_of_iterated
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
      (∀ ℓ, ∀ᵐ s ∂(Q ℓ : Measure JointScene),
        ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge),
          (s.1, e) ∈ D.originalClosedClockCarrier j base) ∧
      ∀ᵐ s ∂(Rlaw : Measure JointScene),
        ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge),
          (s.1, e) ∈ D.originalClosedClockCarrier j base := by
  dsimp only
  intro Q Rlaw φ hφ ψ hinner houter
  have hcore := D.ae_original_retained_plans_zero_outside_macroCarrier_of_iterated j base
    hF hcomplete hu ha hinj A B hA hB nearRadius
    Penv ap am hpm hmm Y hY scale hscalePos hscale rootDomain hrootDomain
    Q Rlaw φ hφ ψ hinner houter
  have hclock (i : Fin D.haar.continuous.count)
      (hi : (D.haar.continuous.coefficient i).seedIndex = j) :=
    D.ae_original_retained_plans_clock_carrier_of_iterated j base i hi
      hF hcomplete hu ha hinj A B hA hB nearRadius
      Penv ap am hpm hmm Y hY scale hscalePos hscale rootDomain hrootDomain
      Q Rlaw φ hφ ψ hinner houter
  exact ⟨fun ℓ ↦ D.ae_retained_average_originalClosedClockCarrier_of_concentration j base
    (Q ℓ) (hcore.1 ℓ) (fun i hi ↦ (hclock i hi).1 ℓ),
    D.ae_retained_average_originalClosedClockCarrier_of_concentration j base
      Rlaw hcore.2 (fun i hi ↦ (hclock i hi).2)⟩

section CountableAccuracy
variable (rseq : ℕ → ℝ) (δseq lossseq : ℕ → ℝ≥0∞)
  (Dseq : ∀ m, PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good
    (rseq m) (δseq m) (lossseq m))

/-- One Borel relation contains every actual finite auxiliary-core carrier.
The original seed frame and macro scene remain fixed through the accuracy sequence. -/
def originalClosedClockCarrierUnion : Set (MacroScene × Edge) :=
  ⋃ m : ℕ, (Dseq m).originalClosedClockCarrier j base

/-- Countably many actual closed-window relations remain a joint Borel relation. -/
theorem measurableSet_originalClosedClockCarrierUnion :
    MeasurableSet (originalClosedClockCarrierUnion j base rseq δseq lossseq Dseq) :=
  MeasurableSet.iUnion fun m ↦ (Dseq m).measurableSet_originalClosedClockCarrier j base

/-- Every auxiliary accuracy uses the same countable-union carrier. -/
theorem originalClosedClockCarrier_subset_union (m : ℕ) :
    (Dseq m).originalClosedClockCarrier j base ⊆
      originalClosedClockCarrierUnion j base rseq δseq lossseq Dseq :=
  subset_iUnion (fun m ↦ (Dseq m).originalClosedClockCarrier j base) m

/-- The actual retained conclusion at any one accuracy enlarges to the fixed union. -/
theorem ae_retained_average_originalClosedClockCarrierUnion (m : ℕ)
    (L : ProbabilityMeasure JointScene)
    (hcar : ∀ᵐ s ∂(L : Measure JointScene),
      ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge),
        (s.1, e) ∈ (Dseq m).originalClosedClockCarrier j base) :
    ∀ᵐ s ∂(L : Measure JointScene),
      ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge),
        (s.1, e) ∈ originalClosedClockCarrierUnion j base rseq δseq lossseq Dseq :=
  hcar.mono fun _ hs ↦ hs.mono fun _ he ↦
    originalClosedClockCarrier_subset_union j base rseq δseq lossseq Dseq m he

end CountableAccuracy
end PopulationLocalPressureCore
end OTSelector.Reconstruction
