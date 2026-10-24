import OTSelector.Reconstruction.FinslerPhysicalSceneRootedLaw
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedLegality
import OTSelector.Probability.CavitySemidiscreteMarkLimit

/-!
# Legal clocks in actual physical scene limits

The actual global physical plans retain their original slack energy after source
restriction and spatial rooting.  The positive original support gap makes the
rooted bad-clock window mass vanish as the original energy scale diverges.
Weak limits of these actual two-plan scene laws consequently have forward clock
separation in both plans, with no prescribed target column law.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

section Restriction

variable {M Ω : Type*} [MeasurableSpace M] [MeasurableSpace Ω]

/-- A measurable original physical-plan family has a measurable actual source
restriction, retaining all realized restricted column masses. -/
theorem measurable_physicalPlan_sourceRestriction
    (Γ : Ω → Measure (M × M)) (hΓ : Measurable Γ)
    (H : Set M) (hH : MeasurableSet H) :
    Measurable (fun env ↦ (Γ env).restrict (H ×ˢ univ)) := by
  apply Measure.measurable_of_measurable_coe
  intro E hE
  simp only [Measure.restrict_apply hE]
  exact (Measure.measurable_coe (hE.inter (hH.prod MeasurableSet.univ))).comp hΓ

end Restriction

variable {ι M Ω : Type*} [Fintype ι] [MeasurableSpace M] [MeasurableSpace Ω]

local instance physicalSceneLimitClockLocalInst : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The actual rooted two-plan law after the same original physical source
restriction, using its actual environment and normalized Haar root. -/
def physicalSceneRestrictedRootedLocalSceneLaw
    (Penv : Measure Ω) [IsProbabilityMeasure Penv]
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ env, IsFiniteMeasure (Γplus env)] [∀ env, IsFiniteMeasure (Γminus env)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N) :
    ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) :=
  physicalSceneRootedLocalSceneLaw Penv
    (fun env ↦ (Γplus env).restrict (H ×ˢ univ))
    (fun env ↦ (Γminus env).restrict (H ×ˢ univ))
    (measurable_physicalPlan_sourceRestriction Γplus hplus H hH)
    (measurable_physicalPlan_sourceRestriction Γminus hminus H hH)
    coord hcoord u hu N hN D hD

section Limit

variable [MetricSpace M] [BorelSpace M]

/-- Actual global physical energy and the original support-distance gap force
both weak limiting plans to have a forward clock gap of at least `gap / 2`. -/
theorem ae_physicalSceneRootedLocalScene_limit_clock_legal
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (Γplus Γminus : ∀ n, Ωn n → Measure (M × M))
    [∀ n env, IsFiniteMeasure (Γplus n env)]
    [∀ n env, IsFiniteMeasure (Γminus n env)]
    (hplus : ∀ n, Measurable (Γplus n)) (hminus : ∀ n, Measurable (Γminus n))
    {A B : Set M} {gap : ℝ} (hgap : 0 < gap)
    (hdist : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hcarriedplus : ∀ n, ∀ᵐ env ∂P n, ∀ᵐ e ∂Γplus n env, e.1 ∈ A ∧ e.2 ∈ B)
    (hcarriedminus : ∀ n, ∀ᵐ env ∂P n, ∀ᵐ e ∂Γminus n env, e.1 ∈ A ∧ e.2 ∈ B)
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop)
    (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal (N n))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergyplus : ∀ n, (∫⁻ env, ∫⁻ e, ENNReal.ofReal
      (scale n * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γplus n env ∂P n) ≤ C)
    (henergyminus : ∀ n, (∫⁻ env, ∫⁻ e, ENNReal.ofReal
      (scale n * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γminus n env ∂P n) ≤ C)
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)))
    (hweak : Tendsto (fun n ↦ physicalSceneRestrictedRootedLocalSceneLaw (P n)
      (Γplus n) (Γminus n) (hplus n) (hminus n) (H n) (hH n) (coord n) (hcoord n)
      u hu.continuous.measurable (N n) (hN n) (D n) (hD n)) atTop (𝓝 Q)) :
    ∀ᵐ scene ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
      (∀ᵐ e ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
        gap / 2 ≤ e.2.2 - e.1.2) ∧
      (∀ᵐ e ∂(scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))),
        gap / 2 ≤ e.2.2 - e.1.2) := by
  let E : Set (ℝ × ℝ) := {t | t.2 - t.1 < gap / 2}
  have hE : IsOpen E := isOpen_lt (continuous_snd.sub continuous_fst) continuous_const
  let Qn := fun n ↦ physicalSceneRestrictedRootedLocalSceneLaw (P n)
    (Γplus n) (Γminus n) (hplus n) (hminus n) (H n) (hH n) (coord n) (hcoord n)
    u hu.continuous.measurable (N n) (hN n) (D n) (hD n)
  have hr : Tendsto (fun n ↦ ENNReal.ofReal (scale n * (gap / 2))) atTop (𝓝 ⊤) :=
    ENNReal.tendsto_ofReal_nhds_top.mpr (hscaleTop.atTop_mul_const (half_pos hgap))
  have hbound (n k : ℕ) :
      ((∫⁻ scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ),
        (scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
          (cavityMarkWindow (Metric.ball 0 (k + 1)) E) ∂(Qn n : Measure _)) ≤
        volume (Metric.ball (0 : ι → ℝ) (k + 1)) * C /
          ENNReal.ofReal (scale n * (gap / 2))) ∧
      ((∫⁻ scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ),
        (scene.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
          (cavityMarkWindow (Metric.ball 0 (k + 1)) E) ∂(Qn n : Measure _)) ≤
        volume (Metric.ball (0 : ι → ℝ) (k + 1)) * C /
          ENNReal.ofReal (scale n * (gap / 2))) := by
    have hread := lintegral_physicalSceneRootedLocalSceneLaw_open (P n)
      (fun env ↦ (Γplus n env).restrict (H n ×ˢ univ))
      (fun env ↦ (Γminus n env).restrict (H n ×ˢ univ))
      (measurable_physicalPlan_sourceRestriction (Γplus n) (hplus n) (H n) (hH n))
      (measurable_physicalPlan_sourceRestriction (Γminus n) (hminus n) (H n) (hH n))
      (coord n) (hcoord n) u hu.continuous.measurable (N n) (hN n) (D n) (hD n)
      (E := cavityMarkWindow (Metric.ball (0 : ι → ℝ) (k + 1)) E)
      (isOpen_cavityMarkWindow Metric.isOpen_ball hE)
    have hsub : cavityMarkWindow (Metric.ball (0 : ι → ℝ) (k + 1)) E ⊆
        physicalSceneClockBadWindow (Metric.ball 0 (k + 1)) gap := by
      intro e he
      exact ⟨he.1, he.2.le⟩
    constructor
    · refine le_trans hread.1.le ?_
      refine le_trans (lintegral_mono fun env ↦ lintegral_mono fun z ↦
        measure_mono hsub) ?_
      exact lintegral_restricted_physicalSceneRootedPlan_clockBad_expectation_ae_le
        (P n) (Γplus n) (hscale n) hgap hdist (hcarriedplus n) (coord n) (hcoord n)
        hu (H n) (N n) (hN n) (D n) (Metric.ball 0 (k + 1))
        Metric.isOpen_ball.measurableSet measure_ball_lt_top.ne C (henergyplus n)
    · refine le_trans hread.2.le ?_
      refine le_trans (lintegral_mono fun env ↦ lintegral_mono fun z ↦
        measure_mono hsub) ?_
      exact lintegral_restricted_physicalSceneRootedPlan_clockBad_expectation_ae_le
        (P n) (Γminus n) (hscale n) hgap hdist (hcarriedminus n) (coord n) (hcoord n)
        hu (H n) (N n) (hN n) (D n) (Metric.ball 0 (k + 1))
        Metric.isOpen_ball.measurableSet measure_ball_lt_top.ne C (henergyminus n)
  have hno := ae_no_mark_event_of_weak_window_bounds Q Qn hweak E hE
    (fun n ↦ ENNReal.ofReal (scale n * (gap / 2))) hr C hC hbound
  simpa only [E, mem_ofPred_eq, not_lt] using hno

end Limit
end OTSelector.Reconstruction
