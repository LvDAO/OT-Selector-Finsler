import OTSelector.Reconstruction.OriginalStageResidualDensityWindowPorts
import OTSelector.Reconstruction.OriginalMarkedWindowCounts

/-! Exact actual port masses and one shared Campbell collar-and-mark-tail estimate. -/
open Set Function Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The literal source port plan has exactly the count of the same unused anchored edges. -/
theorem originalStageWindowSourcePortPlan_mass_eq_pairKernel {q : ℕ}
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (scene : LegalMarkedOptimalInputScene q) :
    (originalStageWindowSourcePortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)) univ =
      physicalScenePairKernel scene.1 ({a | a.1 ∈ K} \ A) := by
  change (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
    ({e | e.1.1 ∈ K} \ physicalPairAnchor ⁻¹' A) univ = _
  rw [Measure.restrict_apply_univ, physicalScenePairKernel_apply]
  rw [Measure.map_apply measurable_physicalPairAnchor
    (show MeasurableSet ({a | a.1 ∈ K} \ A) from (hK.preimage measurable_fst).diff hA)]
  rfl

/-- The literal target port plan counts the unchanged target of the same unused edges. -/
theorem originalStageWindowTargetPortPlan_mass_eq_pairKernel {q : ℕ}
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (scene : LegalMarkedOptimalInputScene q) :
    (originalStageWindowTargetPortPlan A K scene : Measure (LegalMarkedPhysicalEdge q)) univ =
      physicalScenePairKernel scene.1 ({a | a.1 + a.2.2 ∈ K} \ A) := by
  change (scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
    ({e | e.2.1 ∈ K} \ physicalPairAnchor ⁻¹' A) univ = _
  rw [Measure.restrict_apply_univ, physicalScenePairKernel_apply]
  rw [Measure.map_apply measurable_physicalPairAnchor
    (show MeasurableSet ({a | a.1+a.2.2 ∈ K} \ A) from
      (hK.preimage (measurable_fst.add measurable_snd.snd)).diff hA)]
  congr 1
  ext e
  change (e.2.1 ∈ K ∧ physicalPairAnchor e ∉ A) ↔
    (e.1.1 + (e.2.1-e.1.1) ∈ K ∧ physicalPairAnchor e ∉ A)
  rw [show e.1.1 + (e.2.1-e.1.1) = e.2.1 by abel]

/-- A measurable marked observation window pays for a selected edge count by its actual
spatial collar and true-Palm mark tail. The statement does not assign a law to selected edges. -/
theorem LegalWeightedStationaryPoissonMatching.lintegral_original_count_le_collar_and_markTail
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ) (hd : Measurable d)
    {W W₀ : Set (Fin q → ℝ)} (hW : MeasurableSet W) (hW₀ : MeasurableSet W₀)
    {B : Set (PhysicalPairPalmMark (Fin q))} (hB : MeasurableSet B)
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))}
    (hcover : ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ᵐ a ∂physicalScenePairKernel scene.1,
        a ∈ A → (a.1 + d a.2 ∈ W \ W₀) ∨ (a.1 + d a.2 ∈ W ∧ a.2 ∈ B)) :
    (∫⁻ scene, physicalScenePairKernel scene.1 A
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      volume (W \ W₀) + volume W * legalMarkedJointPalm q Q.law B := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q Q.law) := Q.palm_probability
  let A₀ := {a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) | a.1 + d a.2 ∈ W \ W₀}
  let A₁ := {a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) | a.1 + d a.2 ∈ W ∧ a.2 ∈ B}
  have hA₀ : MeasurableSet A₀ := (hW.diff hW₀).preimage (measurable_fst.add (hd.comp measurable_snd))
  have hmean₀ : (∫⁻ scene, physicalScenePairKernel scene.1 A₀
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) = volume (W \ W₀) := by
    simpa only [mem_univ, and_true, measure_univ, mul_one, A₀] using
      Q.lintegral_original_markedWindow_count d hd (hW.diff hW₀) MeasurableSet.univ
  have hmean₁ : (∫⁻ scene, physicalScenePairKernel scene.1 A₁
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) =
      volume W * legalMarkedJointPalm q Q.law B :=
    Q.lintegral_original_markedWindow_count d hd hW hB
  calc
    _ ≤ ∫⁻ scene, physicalScenePairKernel scene.1 A₀ + physicalScenePairKernel scene.1 A₁
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
      apply lintegral_mono_ae
      filter_upwards [hcover] with scene hs
      exact (measure_mono_ae hs).trans (measure_union_le A₀ A₁)
    _ = (∫⁻ scene, physicalScenePairKernel scene.1 A₀
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) +
        ∫⁻ scene, physicalScenePairKernel scene.1 A₁
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)) :=
      lintegral_add_left ((Kernel.measurable_coe physicalScenePairKernel hA₀).comp measurable_fst) _
    _ = _ := by rw [hmean₀, hmean₁]

end OTSelector.Reconstruction
