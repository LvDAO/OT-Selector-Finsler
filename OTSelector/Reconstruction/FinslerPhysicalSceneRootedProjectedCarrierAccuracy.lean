import OTSelector.Reconstruction.FinslerPhysicalSceneRootedProjectedCyclePairAccuracy
import OTSelector.MeasureTheory.ProjectedDominationDiscard
import OTSelector.Topology.ENNRealVanishingThresholds

/-!
# The same full projected scene inherits an actual retained Borel carrier

The actual locally finite plan kernel makes each joint Borel bad-fiber mass
measurable. Closed retained/lost decomposition supplies its scalar domination.
Discard thresholds and measurable good events are constructed internally, and
vanishing original lost-source tails remove every source-window violation on
the SAME full scene law.
-/

open Set Function Filter MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

section EventMass
variable {S X : Type*} [MeasurableSpace S]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [T2Space X]
  [LocallyCompactSpace X] [PseudoMetrizableSpace X] [SigmaCompactSpace X]

/-- Mass of the actual plan in a parameter-dependent Borel edge event. -/
def physicalScenePlanEventMass (plan : S → LocalFiniteMeasure X)
    (event : Set (S × X)) (s : S) : ℝ≥0∞ :=
  (plan s : Measure X) (Prod.mk s ⁻¹' event)

/-- The actual locally finite plan kernel supplies measurability of the
complete joint-event readout, without an extra evaluation premise. -/
theorem measurable_physicalScenePlanEventMass
    (plan : S → LocalFiniteMeasure X) (hplan : Measurable plan)
    {event : Set (S × X)} (hevent : MeasurableSet event) :
    Measurable (physicalScenePlanEventMass plan event) := by
  let κ : Kernel S X := localFiniteMeasureKernel.comap plan hplan
  have hm := κ.measurable_kernel_prodMk_left hevent
  change Measurable (fun s ↦ (plan s : Measure X) (Prod.mk s ⁻¹' event))
  simpa only [κ, Kernel.comap_apply, localFiniteMeasureKernel_apply] using hm
end EventMass

variable {ι : Type*} [Fintype ι] (base : (ι → ℝ) × ℝ)
local instance projectedCarrierAccuracyStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) :=
  inferInstance
local instance projectedCarrierAccuracyConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology _
local instance projectedCarrierAccuracyConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance projectedCarrierAccuracyConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance projectedCarrierAccuracyPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local notation "Edge" => (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)
local notation "MacroScene" => (ι → ℝ) × (PairScene × LocalConfiguration base)
local notation "JointScene" => MacroScene × (PairScene × PairScene)

/-- The actual closed decomposition bounds EVERY full edge set in the source
window by its actual retained mass and actual discarded source mass. -/
theorem physicalSceneMaskedDecomposition_measure_le_retained_add_lost
    (U : Set (ι → ℝ)) (B : Set Edge) (hBU : B ⊆ {e | e.1.1 ∈ U})
    (s : JointScene) (hs : s ∈ physicalSceneMaskedDecompositionCarrier base) :
    (LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure Edge) B ≤
      (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge) B +
        physicalSceneMaskedLostSourceMass base U s := by
  have hsplit : (LocalFiniteMeasure.cavityAverage s.1.2.1 : Measure Edge) =
      (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge) +
        (LocalFiniteMeasure.cavityAverage s.2.2 : Measure Edge) := by
    rw [show s.1.2.1 = physicalScenePairSum s.2 from hs,
      physicalScene_cavityAverage_pairSum]
  rw [hsplit, Measure.add_apply]
  exact add_le_add le_rfl (measure_mono hBU)

/-- An unchanged joint Borel carrier for the actual retained averages passes
to the SAME full law on one source window. The complete bad mass, its
measurability, split domination and threshold good events are all internal. -/
theorem ae_full_bad_mass_zero_of_actual_projected_carrier_accuracy
    (Rfull : ProbabilityMeasure MacroScene) (Raux : ℕ → ProbabilityMeasure JointScene)
    (hprojection : ∀ n,
      (Raux n).map (f := Prod.fst) measurable_fst.aemeasurable = Rfull)
    (Γ : Set (MacroScene × Edge)) (hΓ : MeasurableSet Γ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hdecomposition : ∀ n, ∀ᵐ s ∂(Raux n : Measure JointScene),
      s ∈ physicalSceneMaskedDecompositionCarrier base)
    (hretained : ∀ n, ∀ᵐ s ∂(Raux n : Measure JointScene),
      ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge), (s.1, e) ∈ Γ)
    (loss : ℕ → ℝ≥0∞) (hloss : Tendsto loss atTop (𝓝 0))
    (hlost : ∀ n (level : ℝ≥0∞), 0 < level → level ≠ ⊤ →
      (Raux n : Measure JointScene) {s | level < physicalSceneMaskedLostSourceMass base U s} ≤
        loss n / level) :
    ∀ᵐ s ∂(Rfull : Measure MacroScene),
      (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge)
        {e | (s, e) ∉ Γ ∧ e.1.1 ∈ U} = 0 := by
  let fullPlan : MacroScene → LocalFiniteMeasure Edge :=
    fun s ↦ LocalFiniteMeasure.cavityAverage s.2.1
  let bad : Set (MacroScene × Edge) := {p | p ∉ Γ ∧ p.2.1.1 ∈ U}
  have hbad : MeasurableSet bad :=
    hΓ.compl.inter (hU.preimage measurable_snd.fst.fst)
  let W : MacroScene → ℝ≥0∞ := physicalScenePlanEventMass fullPlan bad
  have hW : Measurable W := measurable_physicalScenePlanEventMass fullPlan
    (LocalFiniteMeasure.continuous_cavityAverage.measurable.comp measurable_snd.fst) hbad
  obtain ⟨threshold, hthresholdBounds, hthreshold, hratio⟩ :=
    exists_vanishing_discard_thresholds loss hloss
  let G : ℕ → Set MacroScene := fun n ↦ {s | W s ≤ threshold n}
  have hG (n : ℕ) : MeasurableSet (G n) := measurableSet_le hW measurable_const
  have hgood (n : ℕ) : ∀ᵐ s ∂(Raux n : Measure JointScene),
      physicalSceneMaskedLostSourceMass base U s ≤ threshold n → s.1 ∈ G n := by
    filter_upwards [hdecomposition n, hretained n] with s hs hr hsmall
    have hzero : (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge)
        (Prod.mk s.1 ⁻¹' bad) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hr] with e he heBad
      exact heBad.1 he
    have hsplit := physicalSceneMaskedDecomposition_measure_le_retained_add_lost base U
      (Prod.mk s.1 ⁻¹' bad) (fun _ h ↦ h.2) s hs
    change W s.1 ≤ _ at hsplit
    rw [hzero, zero_add] at hsplit
    exact hsplit.trans hsmall
  have hfailureBound (n : ℕ) : (Rfull : Measure MacroScene) (G n)ᶜ ≤ loss n / threshold n := by
    have hmap : (Raux n : Measure JointScene).map (Prod.fst : JointScene → MacroScene) =
        (Rfull : Measure MacroScene) :=
      congrArg (fun Q : ProbabilityMeasure MacroScene ↦ (Q : Measure MacroScene)) (hprojection n)
    exact measure_compl_le_of_projected_discard_tail (Rfull : Measure MacroScene)
      (Raux n : Measure JointScene) Prod.fst measurable_fst hmap (G n) (hG n)
      (physicalSceneMaskedLostSourceMass base U) (threshold n) (loss n / threshold n)
      (hgood n) (hlost n (threshold n) (hthresholdBounds n).1 (hthresholdBounds n).2)
  have hfailure : Tendsto (fun n ↦ (Rfull : Measure MacroScene) (G n)ᶜ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hratio
      (fun _ ↦ bot_le) hfailureBound
  change ∀ᵐ s ∂(Rfull : Measure MacroScene), W s = 0
  filter_upwards [ae_frequently_mem_of_compl_measure_tendsto_zero
    (Rfull : Measure MacroScene) G hfailure] with s hs
  apply le_antisymm _ bot_le
  apply le_of_tendsto_of_tendsto_of_frequently tendsto_const_nhds hthreshold
  exact hs.mono fun _ h ↦ h

/-- The mass conclusion gives actual source-window carrying by the same
joint Borel relation, without any finite-stage diffuse-plan shortcut. -/
theorem ae_full_carried_on_source_window_of_actual_projected_carrier_accuracy
    (Rfull : ProbabilityMeasure MacroScene) (Raux : ℕ → ProbabilityMeasure JointScene)
    (hprojection : ∀ n,
      (Raux n).map (f := Prod.fst) measurable_fst.aemeasurable = Rfull)
    (Γ : Set (MacroScene × Edge)) (hΓ : MeasurableSet Γ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hdecomposition : ∀ n, ∀ᵐ s ∂(Raux n : Measure JointScene),
      s ∈ physicalSceneMaskedDecompositionCarrier base)
    (hretained : ∀ n, ∀ᵐ s ∂(Raux n : Measure JointScene),
      ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge), (s.1, e) ∈ Γ)
    (loss : ℕ → ℝ≥0∞) (hloss : Tendsto loss atTop (𝓝 0))
    (hlost : ∀ n (level : ℝ≥0∞), 0 < level → level ≠ ⊤ →
      (Raux n : Measure JointScene) {s | level < physicalSceneMaskedLostSourceMass base U s} ≤
        loss n / level) :
    ∀ᵐ s ∂(Rfull : Measure MacroScene),
      ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge), e.1.1 ∈ U → (s, e) ∈ Γ := by
  filter_upwards [ae_full_bad_mass_zero_of_actual_projected_carrier_accuracy base Rfull Raux
    hprojection Γ hΓ U hU hdecomposition hretained loss hloss hlost] with s hs
  have hcar := measure_eq_zero_iff_ae_notMem.mp hs
  filter_upwards [hcar] with e he heU
  by_contra heΓ
  exact he ⟨heΓ, heU⟩

/-- Countably many spatial windows exhaust the full source while each may use
its own actual accuracy extensions over the SAME full law. -/
theorem ae_full_carried_of_countable_projected_carrier_accuracy
    (Rfull : ProbabilityMeasure MacroScene)
    (Raux : ℕ → ℕ → ProbabilityMeasure JointScene)
    (hprojection : ∀ k n,
      (Raux k n).map (f := Prod.fst) measurable_fst.aemeasurable = Rfull)
    (Γ : Set (MacroScene × Edge)) (hΓ : MeasurableSet Γ)
    (U : ℕ → Set (ι → ℝ)) (hU : ∀ k, MeasurableSet (U k))
    (hcover : ⋃ k, U k = univ)
    (hdecomposition : ∀ k n, ∀ᵐ s ∂(Raux k n : Measure JointScene),
      s ∈ physicalSceneMaskedDecompositionCarrier base)
    (hretained : ∀ k n, ∀ᵐ s ∂(Raux k n : Measure JointScene),
      ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge), (s.1, e) ∈ Γ)
    (loss : ℕ → ℕ → ℝ≥0∞) (hloss : ∀ k, Tendsto (loss k) atTop (𝓝 0))
    (hlost : ∀ k n (level : ℝ≥0∞), 0 < level → level ≠ ⊤ →
      (Raux k n : Measure JointScene) {s | level < physicalSceneMaskedLostSourceMass base (U k) s} ≤
        loss k n / level) :
    ∀ᵐ s ∂(Rfull : Measure MacroScene),
      ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge), (s, e) ∈ Γ := by
  have hall : ∀ᵐ s ∂(Rfull : Measure MacroScene), ∀ k : ℕ,
      ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge), e.1.1 ∈ U k → (s, e) ∈ Γ :=
    ae_all_iff.mpr fun k ↦
      ae_full_carried_on_source_window_of_actual_projected_carrier_accuracy base Rfull (Raux k)
        (hprojection k) Γ hΓ (U k) (hU k) (hdecomposition k) (hretained k)
        (loss k) (hloss k) (hlost k)
  filter_upwards [hall] with s hs
  filter_upwards [ae_all_iff.mpr hs] with e he
  have hmem : e.1.1 ∈ ⋃ k, U k := by rw [hcover]; trivial
  obtain ⟨k, hk⟩ := mem_iUnion.mp hmem
  exact he k hk

end OTSelector.Reconstruction
