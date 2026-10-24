import OTSelector.Reconstruction.FinslerPhysicalSceneClockEnergy
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedClock

/-!
# Legal-clock tails of the same actual rooted physical plan

Source restriction, physical clock energy and Haar root averaging are composed
on one original plan.  The original mass normalization cancels at the root; the
bound uses the global original slack energy and the actual support-distance
gap.  The two target-mass vectors may be the realized restricted column masses.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {ι M : Type*} [Fintype ι] [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The same globally carried physical plan gives a rooted bad-clock bound on
every measurable source restriction, using its global original slack energy. -/
theorem lintegral_restricted_physicalSceneRootedPlan_clockBad_le
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
    {A B : Set M} {gap scale : ℝ} (hscale : 0 < scale) (hgap : 0 < gap)
    (hdist : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hcarried : ∀ᵐ e ∂Γ, e.1 ∈ A ∧ e.2 ∈ B)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (H : Set M) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ z, physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z
      (physicalSceneClockBadWindow U gap) ∂cavityRootMeasure volume D N) ≤
      volume U * (∫⁻ e, ENNReal.ofReal
        (scale * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γ) /
          ENNReal.ofReal (scale * (gap / 2)) := by
  have hr := lintegral_physicalSceneRootedPlan_clockBadWindow_le
    (Γ.restrict (H ×ˢ univ)) coord hcoord u hu.continuous.measurable N hN D U hU gap
  have hm := originalClockBadEvent_mass_le_lintegral_div
    (Γ.restrict (H ×ˢ univ)) hscale hgap hdist (ae_restrict_of_ae hcarried) hu
  calc
    _ ≤ volume U * ((∫⁻ e, ENNReal.ofReal
        (scale * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γ.restrict (H ×ˢ univ)) /
          ENNReal.ofReal (scale * (gap / 2))) := by
      exact hr.trans (by gcongr)
    _ ≤ volume U * ((∫⁻ e, ENNReal.ofReal
        (scale * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γ) /
          ENNReal.ofReal (scale * (gap / 2))) := by
      gcongr
      exact Measure.restrict_le_self
    _ = _ := by simp only [div_eq_mul_inv, mul_assoc]

/-- The original environment energy controls the actual rooted source-cell
bad-clock expectation.  The spatial window is the only finite-volume input. -/
theorem lintegral_restricted_physicalSceneRootedPlan_clockBad_expectation_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Γ : Ω → Measure (M × M)) [∀ w, IsFiniteMeasure (Γ w)]
    {A B : Set M} {gap scale : ℝ} (hscale : 0 < scale) (hgap : 0 < gap)
    (hdist : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hcarried : ∀ w, ∀ᵐ e ∂Γ w, e.1 ∈ A ∧ e.2 ∈ B)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (H : Set M) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) (hUf : volume U ≠ ⊤)
    (C : ℝ≥0∞)
    (henergy : (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γ w ∂P) ≤ C) :
    (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
      (physicalSceneClockBadWindow U gap) ∂cavityRootMeasure volume D N ∂P) ≤
      volume U * C / ENNReal.ofReal (scale * (gap / 2)) := by
  let r := ENNReal.ofReal (scale * (gap / 2))
  have hr : r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hscale (half_pos hgap))
  have hfactor : volume U / r ≠ ⊤ := ENNReal.div_ne_top hUf hr
  calc
    _ ≤ ∫⁻ w, volume U * (∫⁻ e, ENNReal.ofReal
        (scale * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γ w) / r ∂P :=
      lintegral_mono fun w ↦ lintegral_restricted_physicalSceneRootedPlan_clockBad_le
        (Γ w) hscale hgap hdist (hcarried w) coord hcoord hu H N hN D U hU
    _ = (volume U / r) * (∫⁻ w, ∫⁻ e, ENNReal.ofReal
        (scale * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γ w ∂P) := by
      simp_rw [div_eq_mul_inv, mul_right_comm (volume U)]
      exact lintegral_const_mul' _ _ hfactor
    _ ≤ (volume U / r) * C := by gcongr
    _ = _ := by simp only [r, div_eq_mul_inv]; ac_rfl

/-- The same original environment bound needs carrying only almost surely,
as supplied by actual sampled targets and actual allocation optimizers. -/
theorem lintegral_restricted_physicalSceneRootedPlan_clockBad_expectation_ae_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Γ : Ω → Measure (M × M)) [∀ w, IsFiniteMeasure (Γ w)]
    {A B : Set M} {gap scale : ℝ} (hscale : 0 < scale) (hgap : 0 < gap)
    (hdist : ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hcarried : ∀ᵐ w ∂P, ∀ᵐ e ∂Γ w, e.1 ∈ A ∧ e.2 ∈ B)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (H : Set M) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) (hUf : volume U ≠ ⊤)
    (C : ℝ≥0∞)
    (henergy : (∫⁻ w, ∫⁻ e, ENNReal.ofReal
      (scale * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γ w ∂P) ≤ C) :
    (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (H ×ˢ univ)) coord u N z
      (physicalSceneClockBadWindow U gap) ∂cavityRootMeasure volume D N ∂P) ≤
      volume U * C / ENNReal.ofReal (scale * (gap / 2)) := by
  let r := ENNReal.ofReal (scale * (gap / 2))
  have hr : r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hscale (half_pos hgap))
  have hfactor : volume U / r ≠ ⊤ := ENNReal.div_ne_top hUf hr
  calc
    _ ≤ ∫⁻ w, volume U * (∫⁻ e, ENNReal.ofReal
        (scale * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γ w) / r ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hcarried] with w hw
      exact lintegral_restricted_physicalSceneRootedPlan_clockBad_le
        (Γ w) hscale hgap hdist hw coord hcoord hu H N hN D U hU
    _ = (volume U / r) * (∫⁻ w, ∫⁻ e, ENNReal.ofReal
        (scale * (dist e.1 e.2 - u e.2 + u e.1)) ∂Γ w ∂P) := by
      simp_rw [div_eq_mul_inv, mul_right_comm (volume U)]
      exact lintegral_const_mul' _ _ hfactor
    _ ≤ (volume U / r) * C := by gcongr
    _ = _ := by simp only [r, div_eq_mul_inv]; ac_rfl

end OTSelector.Reconstruction
