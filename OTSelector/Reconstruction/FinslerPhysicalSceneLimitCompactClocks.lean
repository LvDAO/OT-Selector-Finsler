import OTSelector.Reconstruction.FinslerPhysicalSceneLimitClock
import OTSelector.Probability.CavitySemidiscreteMarkLimit

/-!
# Compact original clock carriers in actual scene limits

The clock images of the original compact physical supports remain compact.
Every actual carried plan and both plans of any actual rooted weak limit keep
these same clock carriers.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M : Type*} [Fintype ι]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

local instance physicalSceneCompactClockLocalInst : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- An actual carried physical plan assigns zero rooted window mass to clocks
outside the compact images of its original physical carriers. -/
theorem physicalSceneRootedPlan_compactClockWindow_zero
    (Γ : Measure (M × M)) {A B : Set M}
    (hcarried : ∀ᵐ p ∂Γ, p.1 ∈ A ∧ p.2 ∈ B)
    (hA : IsCompact A) (hB : IsCompact B)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Continuous u) (H : Set M) (N : ℝ) (z : ι → ℝ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z
      (cavityMarkWindow U ((u '' A) ×ˢ (u '' B))ᶜ) = 0 := by
  let E : Set (ℝ × ℝ) := ((u '' A) ×ˢ (u '' B))ᶜ
  have hE : IsOpen E := ((hA.image hu).prod (hB.image hu)).isClosed.isOpen_compl
  have hwindow := measurableSet_cavityMarkWindow hU hE.measurableSet
  have hf := measurable_physicalSceneRootedObservation coord hcoord u hu.measurable z
  change (ENNReal.ofReal N • (Γ.restrict (H ×ˢ univ)).map
    (physicalSceneRootedObservation coord u z)) (cavityMarkWindow U E) = 0
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hf hwindow]
  have hzero : Γ.restrict (H ×ˢ univ)
      (physicalSceneRootedObservation coord u z ⁻¹' cavityMarkWindow U E) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [ae_restrict_of_ae hcarried] with p hp
    change ¬(coord p.1 - z ∈ U ∧ (u p.1, u p.2) ∈ E)
    intro he
    exact he.2 ⟨mem_image_of_mem u hp.1, mem_image_of_mem u hp.2⟩
  rw [hzero, mul_zero]

/-- Actual weak limits of the source-restricted original two-plan scene laws
retain the compact original source and target clock carriers in both plans. -/
theorem ae_physicalSceneRootedLocalScene_limit_compact_clock_carriers
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (Γplus Γminus : ∀ n, Ωn n → Measure (M × M))
    [∀ n env, IsFiniteMeasure (Γplus n env)]
    [∀ n env, IsFiniteMeasure (Γminus n env)]
    (hplus : ∀ n, Measurable (Γplus n)) (hminus : ∀ n, Measurable (Γminus n))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hcarriedplus : ∀ n, ∀ᵐ env ∂P n, ∀ᵐ e ∂Γplus n env, e.1 ∈ A ∧ e.2 ∈ B)
    (hcarriedminus : ∀ n, ∀ᵐ env ∂P n, ∀ᵐ e ∂Γminus n env, e.1 ∈ A ∧ e.2 ∈ B)
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Continuous u)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal (N n))
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (hweak : Tendsto (fun n ↦ physicalSceneRestrictedRootedLocalSceneLaw (P n)
      (Γplus n) (Γminus n) (hplus n) (hminus n) (H n) (hH n) (coord n) (hcoord n)
      u hu.measurable (N n) (hN n) (D n) (hD n)) atTop (𝓝 Q)) :
    IsCompact (u '' A) ∧ IsCompact (u '' B) ∧
      ∀ᵐ scene ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
        (∀ᵐ e ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
          e.1.2 ∈ u '' A ∧ e.2.2 ∈ u '' B) ∧
        (∀ᵐ e ∂(scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
          e.1.2 ∈ u '' A ∧ e.2.2 ∈ u '' B) := by
  let E : Set (ℝ × ℝ) := ((u '' A) ×ˢ (u '' B))ᶜ
  have hE : IsOpen E := ((hA.image hu).prod (hB.image hu)).isClosed.isOpen_compl
  let Qn := fun n ↦ physicalSceneRestrictedRootedLocalSceneLaw (P n)
    (Γplus n) (Γminus n) (hplus n) (hminus n) (H n) (hH n) (coord n) (hcoord n)
    u hu.measurable (N n) (hN n) (D n) (hD n)
  have hbound (n k : ℕ) :
      ((∫⁻ scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ),
        (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
          (cavityMarkWindow (Metric.ball 0 (k + 1)) E) ∂(Qn n : Measure _)) ≤
        volume (Metric.ball (0 : ι → ℝ) (k + 1)) * 0 / ⊤) ∧
      ((∫⁻ scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ),
        (scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
          (cavityMarkWindow (Metric.ball 0 (k + 1)) E) ∂(Qn n : Measure _)) ≤
        volume (Metric.ball (0 : ι → ℝ) (k + 1)) * 0 / ⊤) := by
    have hread := lintegral_physicalSceneRootedLocalSceneLaw_open (P n)
      (fun env ↦ (Γplus n env).restrict (H n ×ˢ univ))
      (fun env ↦ (Γminus n env).restrict (H n ×ˢ univ))
      (measurable_physicalPlan_sourceRestriction (Γplus n) (hplus n) (H n) (hH n))
      (measurable_physicalPlan_sourceRestriction (Γminus n) (hminus n) (H n) (hH n))
      (coord n) (hcoord n) u hu.measurable (N n) (hN n) (D n) (hD n)
      (E := cavityMarkWindow (Metric.ball (0 : ι → ℝ) (k + 1)) E)
      (isOpen_cavityMarkWindow Metric.isOpen_ball hE)
    have hpzero : (∫⁻ env, ∫⁻ z, physicalSceneRootedPlan
        ((Γplus n env).restrict (H n ×ˢ univ)) (coord n) u (N n) z
        (cavityMarkWindow (Metric.ball 0 (k + 1)) E)
        ∂cavityRootMeasure volume (D n) (N n) ∂P n) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hcarriedplus n] with env henv
      have hz (z) := physicalSceneRootedPlan_compactClockWindow_zero
        (Γplus n env) henv hA hB (coord n) (hcoord n) u hu (H n) (N n) z
        (Metric.ball 0 (k + 1)) Metric.isOpen_ball.measurableSet
      exact lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall hz)
    have hmzero : (∫⁻ env, ∫⁻ z, physicalSceneRootedPlan
        ((Γminus n env).restrict (H n ×ˢ univ)) (coord n) u (N n) z
        (cavityMarkWindow (Metric.ball 0 (k + 1)) E)
        ∂cavityRootMeasure volume (D n) (N n) ∂P n) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hcarriedminus n] with env henv
      have hz (z) := physicalSceneRootedPlan_compactClockWindow_zero
        (Γminus n env) henv hA hB (coord n) (hcoord n) u hu (H n) (N n) z
        (Metric.ball 0 (k + 1)) Metric.isOpen_ball.measurableSet
      exact lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall hz)
    exact ⟨by simpa only [Qn, physicalSceneRestrictedRootedLocalSceneLaw,
        hpzero, mul_zero, ENNReal.zero_div] using hread.1.le,
      by simpa only [Qn, physicalSceneRestrictedRootedLocalSceneLaw,
        hmzero, mul_zero, ENNReal.zero_div] using hread.2.le⟩
  have hno := ae_no_mark_event_of_weak_window_bounds Q Qn hweak E hE
    (fun _ ↦ ⊤) tendsto_const_nhds 0 (by simp) hbound
  refine ⟨hA.image hu, hB.image hu, ?_⟩
  simpa only [E, mem_compl_iff, mem_prod, not_not] using hno

end OTSelector.Reconstruction
