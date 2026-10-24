import OTSelector.Probability.CavitySemidiscreteLocalPlan
import OTSelector.Probability.CavitySemidiscreteSourceMassLaw

/-!
# Actual rooted mark events controlled by transport energy

Spatial translation preserves both original marks. A positive cost gap on a
forbidden mark event therefore bounds its source-window mass at the same Haar
root. This applies to interleaving mark laws without ordered separation.
-/

open MeasureTheory Set
open scoped ENNReal Classical

noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]

/-- The original marks satisfy a specified event, and the rooted source lies in `U`. -/
def cavityMarkWindow (U : Set (ι → ℝ)) (E : Set (A × B)) :
    Set (((ι → ℝ) × A) × ((ι → ℝ) × B)) :=
  {e | e.1.1 ∈ U ∧ (e.1.2, e.2.2) ∈ E}

omit [Fintype ι] in
theorem measurableSet_cavityMarkWindow {U : Set (ι → ℝ)} (hU : MeasurableSet U)
    {E : Set (A × B)} (hE : MeasurableSet E) :
    MeasurableSet (cavityMarkWindow U E) :=
  (hU.preimage measurable_fst.fst).inter
    (hE.preimage (measurable_fst.snd.prodMk measurable_snd.snd))

omit [Fintype ι] in
/-- The event is read exactly from the original allocation and both original marks. -/
theorem cavitySpatialRootedPlan_markWindow {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (z : ι → ℝ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (E : Set (A × B)) (hE : MeasurableSet E) :
    cavitySpatialRootedPlan μ a Y N z (cavityMarkWindow U E) =
      ENNReal.ofReal N * cavityRootWindowReadout (semidiscreteAllocationMeasure μ a)
        (fun e ↦ e.1.1) (fun e ↦ if (e.1.2, (Y e.2).2) ∈ E then 1 else 0) U z := by
  let f : (((ι → ℝ) × A) × Fin (m + 1)) → (((ι → ℝ) × A) × ((ι → ℝ) × B)) :=
    Prod.map (cavitySpatialTranslate z) (fun j ↦ cavitySpatialTranslate z (Y j))
  have hf : Measurable f :=
    (show Measurable (cavitySpatialTranslate z : ((ι → ℝ) × A) → ((ι → ℝ) × A)) from
      measurable_cavitySpatialTranslate.comp
        (measurable_const.prodMk measurable_id)).prodMap (measurable_of_finite _)
  change (ENNReal.ofReal N • (semidiscreteAllocationMeasure μ a).map f) _ = _
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply hf (measurableSet_cavityMarkWindow hU hE),
    ← lintegral_indicator_one ((measurableSet_cavityMarkWindow hU hE).preimage hf)]
  congr 1
  apply lintegral_congr
  rintro ⟨⟨x, s⟩, j⟩
  simp only [Set.indicator_apply, Set.mem_preimage, f, Prod.map_apply,
    cavityMarkWindow, Set.mem_ofPred_eq, cavitySpatialTranslate]
  change (if x - z ∈ U ∧ (s, (Y j).2) ∈ E then 1 else 0) =
    if x - z ∈ U then (if (s, (Y j).2) ∈ E then 1 else 0) else 0
  by_cases hx : x - z ∈ U <;> simp only [hx, ite_true, ite_false, true_and, false_and]

/-- An actual cost gap gives the exact inverse-gap bound on forbidden marked mass. -/
theorem lintegral_cavitySpatialRootedPlan_markWindow_le {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsFiniteMeasure μ] (p : Fin (m + 1) → ℝ)
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ) (ha : IsSemidiscreteAllocation μ p a)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (E : Set (A × B)) (hE : MeasurableSet E)
    (w : (((ι → ℝ) × A) × Fin (m + 1)) → ℝ≥0∞) (hw : Measurable w)
    (r : ℝ≥0∞) (hr0 : r ≠ 0) (hrt : r ≠ ⊤)
    (hgap : ∀ᵐ e ∂semidiscreteAllocationMeasure μ a,
      (e.1.2, (Y e.2).2) ∈ E → r ≤ w e) :
    (∫⁻ z, cavitySpatialRootedPlan μ a Y N z (cavityMarkWindow U E)
      ∂cavityRootMeasure volume D N) ≤
      (volume U * ∫⁻ e, w e ∂semidiscreteAllocationMeasure μ a) / r := by
  have := ha.isFiniteMeasure_allocationMeasure
  simp_rw [cavitySpatialRootedPlan_markWindow μ a Y N _ U hU E hE]
  apply le_trans _ (lintegral_cavityRoot_scaled_window_tail_le volume
    (semidiscreteAllocationMeasure μ a) (fun e ↦ e.1.1) measurable_fst.fst
    w hw U hU D N hN r hr0 hrt)
  apply lintegral_mono
  intro z
  refine mul_le_mul_right ?_ _
  apply lintegral_mono_ae
  filter_upwards [hgap] with e he
  by_cases hz : e.1.1 - z ∈ U
  · simp only [indicator_of_mem hz]
    by_cases heE : (e.1.2, (Y e.2).2) ∈ E
    · simp only [heE, he heE, ite_true, le_refl]
    · simp only [heE, ite_false, zero_le]
  · simp only [indicator_of_notMem hz, le_refl]

/-- The same estimate on the original random environment uses its actual expected
cost, without conditioning on a separately sampled or repaired allocation. -/
theorem lintegral_original_rootedPlan_markWindow_le
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ)
    (a : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (ham : ∀ j, Measurable (fun v ↦ a v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (N : ℝ) (hN : 0 < N) (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hUf : volume U ≠ ⊤) (E : Set (A × B)) (hE : MeasurableSet E)
    (w : Ω → (((ι → ℝ) × A) × Fin (m + 1)) → ℝ≥0∞)
    (hw : ∀ ω, Measurable (w ω)) (r : ℝ≥0∞) (hr0 : r ≠ 0) (hrt : r ≠ ⊤)
    (hgood : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ a (ω, s)) ∧
      ∀ᵐ e ∂semidiscreteAllocationMeasure μ (fun s ↦ a (ω, s)),
        (e.1.2, (Y ω e.2).2) ∈ E → r ≤ w ω e)
    (C : ℝ≥0∞)
    (henergy : (∫⁻ ω, ∫⁻ e, w ω e
      ∂semidiscreteAllocationMeasure μ (fun s ↦ a (ω, s)) ∂P) ≤ C) :
    (∫⁻ v : Ω × (ι → ℝ),
      cavitySpatialRootedPlan μ (fun s ↦ a (v.1, s)) (Y v.1) N v.2 (cavityMarkWindow U E)
      ∂P.prod (cavityRootMeasure volume D N)) ≤ volume U * C / r := by
  have hm : Measurable (fun v : Ω × (ι → ℝ) ↦
      cavitySpatialRootedPlan μ (fun s ↦ a (v.1, s)) (Y v.1) N v.2 (cavityMarkWindow U E)) :=
    (Measure.measurable_coe (measurableSet_cavityMarkWindow hU hE)).comp
      (measurable_joint_cavitySpatialRootedPlan μ a ham Y hY N)
  have : SFinite (cavityRootMeasure volume D N) := by
    unfold cavityRootMeasure
    infer_instance
  rw [lintegral_prod _ hm.aemeasurable]
  calc
    _ ≤ ∫⁻ ω, (volume U * ∫⁻ e, w ω e
        ∂semidiscreteAllocationMeasure μ (fun s ↦ a (ω, s))) / r ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hgood] with ω hω
      exact lintegral_cavitySpatialRootedPlan_markWindow_le μ (p ω)
        (fun s ↦ a (ω, s)) hω.1 (Y ω) N hN D U hU E hE
        (w ω) (hw ω) r hr0 hrt hω.2
    _ ≤ _ := by
      simp only [div_eq_mul_inv]
      rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hr0),
        lintegral_const_mul' _ _ hUf]
      gcongr

end OTSelector.Probability
