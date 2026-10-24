import OTSelector.Reconstruction.MarkedStationaryValuePalmEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTightness

/-!
# Actual Haar-rooted original energy controls its pair Palm readout

The same actual physical plan supplies the source-window energy. The root
translation cancels from both original clocks and the complete displacement.
Haar averaging therefore bounds this readout by the original global energy,
with its exact original mass normalization.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
local instance markedStationaryValuePalmRootedEnergyLocalPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

omit [Fintype ι] [MeasurableSpace M] in
/-- Actual root translation preserves both original scalar clocks and the
entire transverse displacement. -/
theorem physicalPairAnchor_rootedObservation (coord : M → (ι → ℝ)) (u : M → ℝ)
    (z : ι → ℝ) (p : M × M) :
    (physicalPairAnchor (physicalSceneRootedObservation coord u z p)).2 =
      ((u p.1, u p.2), coord p.2 - coord p.1) := by
  simp only [physicalPairAnchor, physicalSceneRootedObservation, sub_sub_sub_cancel_right]

omit [Fintype ι] in
/-- An actual rooted source-window energy is exactly the original physical
plan's weighted source readout. No new endpoint law or energy is substituted. -/
theorem setLIntegral_physicalSceneRootedPlan_energy
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    {f : PhysicalPairPalmMark ι → ℝ≥0∞} (hf : Measurable f)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U},
      f (physicalPairAnchor e).2 ∂physicalSceneRootedPlan Γ coord u N z) =
      ENNReal.ofReal N * cavityRootWindowReadout Γ (fun p ↦ coord p.1)
        (fun p ↦ f ((u p.1, u p.2), coord p.2 - coord p.1)) U z := by
  have hW : MeasurableSet {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U} :=
    hU.preimage measurable_fst.fst
  have hF : Measurable (fun e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) ↦
      f (physicalPairAnchor e).2) := hf.comp (measurable_physicalPairAnchor.snd)
  rw [← lintegral_indicator hW, physicalSceneRootedPlan, lintegral_smul_measure,
    lintegral_map (hF.indicator hW) (measurable_physicalSceneRootedObservation coord hcoord u hu z)]
  congr 1
  apply lintegral_congr
  intro p
  change ({e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U}.indicator
    (fun e ↦ f (physicalPairAnchor e).2) (physicalSceneRootedObservation coord u z p)) =
      U.indicator (fun _ ↦ f ((u p.1, u p.2), coord p.2 - coord p.1)) (coord p.1 - z)
  by_cases hx : coord p.1 - z ∈ U
  · have hp : physicalSceneRootedObservation coord u z p ∈
        {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U} := hx
    rw [indicator_of_mem hp, indicator_of_mem hx, physicalPairAnchor_rootedObservation]
  · have hp : physicalSceneRootedObservation coord u z p ∉
        {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U} := hx
    rw [indicator_of_notMem hp, indicator_of_notMem hx]

/-- Haar averaging converts the original full global paired-mark energy to
the actual rooted source-window energy with the original normalization. -/
theorem lintegral_physicalSceneRootedPlan_sourceEnergy_le
    (Γ : Measure (M × M)) [SFinite Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    {f : PhysicalPairPalmMark ι → ℝ≥0∞} (hf : Measurable f)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ z, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U},
      f (physicalPairAnchor e).2 ∂physicalSceneRootedPlan Γ coord u N z
      ∂cavityRootMeasure volume D N) ≤
      volume U * ∫⁻ p, f ((u p.1, u p.2), coord p.2 - coord p.1) ∂Γ := by
  simp_rw [setLIntegral_physicalSceneRootedPlan_energy Γ coord hcoord u hu N _ hf U hU]
  exact lintegral_cavityRoot_scaled_window_le volume Γ _ (hcoord.comp measurable_fst)
    _ (hf.comp (((hu.comp measurable_fst).prodMk (hu.comp measurable_snd)).prodMk
      ((hcoord.comp measurable_snd).sub (hcoord.comp measurable_fst)))) U hU D N hN

/-- A source-window energy is a measurable readout of the same original scene. -/
theorem measurable_physicalScene_sourceWindow_energy
    {f : PhysicalPairPalmMark ι → ℝ≥0∞} (hf : Measurable f)
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) :
    Measurable (fun scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) ↦
      ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U},
        f (physicalPairAnchor e).2 ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))) := by
  exact (hf.comp measurable_physicalPairAnchor.snd).lintegral_kernel
    (κ := physicalScenePlanKernel.restrict (hU.preimage measurable_fst.fst))

/-- The actual original environment and root retain the same energy estimate,
including every realized target in the original plan. -/
theorem lintegral_physicalSceneRootedLocalSceneLaw_sourceEnergy_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    {f : PhysicalPairPalmMark ι → ℝ≥0∞} (hf : Measurable f)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ scene, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U},
      f (physicalPairAnchor e).2 ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      ∂(physicalSceneRootedLocalSceneLaw P Γplus Γminus hplus hminus coord hcoord u hu N hN D hD :
        Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤
      volume U * ∫⁻ w, ∫⁻ p, f ((u p.1, u p.2), coord p.2 - coord p.1) ∂Γplus w ∂P := by
  rw [lintegral_physicalSceneRootedLocalSceneLaw P Γplus Γminus hplus hminus
    coord hcoord u hu N hN D hD _ (measurable_physicalScene_sourceWindow_energy hf hU)]
  apply (lintegral_mono (fun w ↦ lintegral_physicalSceneRootedPlan_sourceEnergy_le
    (Γplus w) coord hcoord u hu N hN hf D U hU)).trans_eq
  exact lintegral_const_mul _ ((Measure.measurable_lintegral
    (hf.comp (((hu.comp measurable_fst).prodMk (hu.comp measurable_snd)).prodMk
      ((hcoord.comp measurable_snd).sub (hcoord.comp measurable_fst))))).comp hplus)

/-- Shrinking actual open neighborhoods of the source unit cube remove the
window-volume enlargement exactly. This keeps the original global energy
constant in the limiting Palm estimate. -/
theorem lintegral_cubePalm_le_of_weak_energy_density_bound
    (P : ℕ → ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    {Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (hweak : Tendsto P atTop (𝓝 Q))
    (f : PhysicalPairPalmMark ι → ℝ) (hf : Continuous f) (hf0 : ∀ m, 0 ≤ f m)
    (E : ℝ≥0∞)
    (hbound : ∀ (U : Set (ι → ℝ)), IsOpen U → ∀ n,
      (∫⁻ scene, ∫⁻ e in {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.1.1 ∈ U},
        ENNReal.ofReal (f (physicalPairAnchor e).2)
        ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
        ∂(P n : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))) ≤ volume U * E) :
    (∫⁻ m, ENNReal.ofReal (f m) ∂cubePalm ι
      (physicalScenePairCampbell (Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))))) ≤ E := by
  let eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let center : ι → ℝ := fun _ ↦ 1 / 2
  let U (n : ℕ) := Metric.ball center (1 / 2 + eps n)
  have heps (n) : 0 < eps n := by dsimp [eps]; positivity
  have hrad (n) : 0 < 1 / 2 + eps n := by positivity
  have hsub (n) : palmUnitCube ι ⊆ U n := by
    intro x hx
    have hnorm : ‖x - center‖ ≤ (1 / 2 : ℝ) := by
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
      intro i
      change |x i - 1 / 2| ≤ 1 / 2
      exact abs_le.mpr ⟨by linarith [hx.1 i], by linarith [hx.2 i]⟩
    change dist x center < 1 / 2 + eps n
    rw [dist_eq_norm]
    exact hnorm.trans_lt (lt_add_of_pos_right _ (heps n))
  have hb (n) := lintegral_cubePalm_le_of_weak_sourceWindow_energy_bound P hweak
    f hf hf0 Metric.isOpen_ball (hsub n) (volume (U n) * E)
    (hbound (U n) Metric.isOpen_ball)
  have hepst : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hreal : Tendsto (fun n ↦ (2 * (1 / 2 + eps n)) ^ Fintype.card ι) atTop (𝓝 (1 : ℝ)) := by
    have hc : Tendsto (fun _ : ℕ ↦ (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := tendsto_const_nhds
    convert ((hc.add hepst).const_mul 2).pow (Fintype.card ι) using 1
    norm_num
  have hvol : Tendsto (fun n ↦ volume (U n)) atTop (𝓝 (1 : ℝ≥0∞)) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    simpa only [ENNReal.ofReal_one] using h.congr' (.of_forall (fun n ↦
      (Real.volume_pi_ball center (hrad n)).symm))
  have hlim := ENNReal.Tendsto.mul_const (b := E) hvol (Or.inl one_ne_zero)
  simpa only [one_mul] using ge_of_tendsto hlim (.of_forall hb)

end OTSelector.Reconstruction
