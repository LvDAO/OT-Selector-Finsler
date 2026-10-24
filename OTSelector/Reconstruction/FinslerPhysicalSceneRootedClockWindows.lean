import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTightness
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMeanMarginals

/-! Actual clock-window masses are Haar readouts of the same physical plan. -/
open Set Function MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option linter.unusedSectionVars false
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
local notation "Edge" => (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))

/-- A spatial source window with the original two endpoint clocks in a fixed set. -/
def physicalSceneRootedClockWindow (U : Set (ι → ℝ)) (T : Set (ℝ × ℝ)) : Set Edge :=
  {e | e.1.1 ∈ U ∧ (e.1.2, e.2.2) ∈ T}

/-- Both original clocks remain measurable under the actual observation. -/
theorem measurableSet_physicalSceneRootedClockWindow
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) {T : Set (ℝ × ℝ)}
    (hT : MeasurableSet T) : MeasurableSet (physicalSceneRootedClockWindow U T) :=
  (hU.preimage measurable_fst.fst).inter
    (hT.preimage (measurable_fst.snd.prodMk measurable_snd.snd))

/-- Open original clock bands give open windows in the actual full edge space. -/
theorem isOpen_physicalSceneRootedClockWindow
    {U : Set (ι → ℝ)} (hU : IsOpen U) {T : Set (ℝ × ℝ)} (hT : IsOpen T) :
    IsOpen (physicalSceneRootedClockWindow U T) :=
  (hU.preimage continuous_fst.fst).inter
    (hT.preimage (continuous_fst.snd.prodMk continuous_snd.snd))

/-- Observing a clock band commutes exactly with restricting the SAME original plan. -/
theorem physicalSceneRootedPlan_clockWindow_eq_restrict
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) {T : Set (ℝ × ℝ)}
    (hT : MeasurableSet T) :
    physicalSceneRootedPlan Γ coord u N z (physicalSceneRootedClockWindow U T) =
      physicalSceneRootedPlan (Γ.restrict ((fun p : M × M ↦ (u p.1, u p.2)) ⁻¹' T))
        coord u N z {e | e.1.1 ∈ U} := by
  have hobs := measurable_physicalSceneRootedObservation coord hcoord u hu z
  have hsource : MeasurableSet {e : Edge | e.1.1 ∈ U} := hU.preimage measurable_fst.fst
  unfold physicalSceneRootedPlan
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    Measure.map_apply hobs (measurableSet_physicalSceneRootedClockWindow hU hT),
    Measure.map_apply hobs hsource, Measure.restrict_apply (hsource.preimage hobs)]
  congr 1

/-- Original clock-band mass controls its actual rooted readout, with the
original root normalization cancelling the physical mass scale. -/
theorem lintegral_physicalSceneRootedPlan_clockWindow_le
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (rootDomain : Set (ι → ℝ)) {U : Set (ι → ℝ)} (hU : MeasurableSet U)
    {T : Set (ℝ × ℝ)} (hT : MeasurableSet T) :
    (∫⁻ z, physicalSceneRootedPlan Γ coord u N z (physicalSceneRootedClockWindow U T)
      ∂cavityRootMeasure volume rootDomain N) ≤
      volume U * Γ ((fun p : M × M ↦ (u p.1, u p.2)) ⁻¹' T) := by
  simp_rw [physicalSceneRootedPlan_clockWindow_eq_restrict Γ coord hcoord u hu N _ hU hT]
  simpa only [Measure.restrict_apply_univ] using
    lintegral_physicalSceneRootedPlan_sourceWindow_le
      (Γ.restrict ((fun p : M × M ↦ (u p.1, u p.2)) ⁻¹' T))
      coord hcoord u hu N hN rootDomain U hU
end OTSelector.Reconstruction
