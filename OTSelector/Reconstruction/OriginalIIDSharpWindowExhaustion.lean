import OTSelector.Reconstruction.MarkedStationaryValuePalmCube

/-!
# Sharp exhaustion of the original unit spatial cube by bounded open windows

Explicit sup-norm balls contain the same closed unit cube, are uniformly
bounded by norm two, and have volumes tending to one in every dimension,
including dimension zero. Consequently a bound with the physical window
volume as a factor loses that factor in the limit.
-/

open Set Function Filter MeasureTheory Topology
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- Radius of the nth explicit open neighborhood of the closed unit cube. -/
def originalIIDSharpPalmWindowRadius (n : ℕ) : ℝ :=
  1/2 + (((n+1 : ℕ) : ℝ))⁻¹

/-- An actual bounded open spatial window around the original closed unit
cube, using the standard coordinate sup norm. -/
def originalIIDSharpPalmWindow (q n : ℕ) : Set (Fin q → ℝ) :=
  Metric.ball (fun _ ↦ (1/2 : ℝ)) (originalIIDSharpPalmWindowRadius n)

theorem originalIIDSharpPalmWindowRadius_pos (n : ℕ) :
    0 < originalIIDSharpPalmWindowRadius n := by
  unfold originalIIDSharpPalmWindowRadius
  positivity

/-- Every window is open in the actual q-dimensional coordinate space. -/
theorem isOpen_originalIIDSharpPalmWindow (q n : ℕ) :
    IsOpen (originalIIDSharpPalmWindow q n) := Metric.isOpen_ball

/-- The full closed physical unit cube, including its boundary, lies in every
member of the same explicit open window family. -/
theorem palmUnitCube_subset_originalIIDSharpPalmWindow (q n : ℕ) :
    palmUnitCube (Fin q) ⊆ originalIIDSharpPalmWindow q n := by
  intro x hx
  have hd : ‖x-(fun _ : Fin q ↦ (1/2 : ℝ))‖ ≤ (1/2 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)).mpr
    intro i
    change |x i-1/2| ≤ (1/2 : ℝ)
    have hlo : 0 ≤ x i := hx.1 i
    have hhi : x i ≤ 1 := hx.2 i
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  apply Metric.mem_ball.mpr
  rw [dist_eq_norm]
  exact hd.trans_lt (lt_add_of_pos_right _ (by positivity))

/-- One fixed norm bound works for all window indices and every dimension. -/
theorem norm_le_two_of_mem_originalIIDSharpPalmWindow (q n : ℕ)
    {x : Fin q → ℝ} (hx : x ∈ originalIIDSharpPalmWindow q n) : ‖x‖ ≤ 2 := by
  have hc : ‖(fun _ : Fin q ↦ (1/2 : ℝ))‖ ≤ (1/2 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)).mpr
    intro i
    norm_num
  have he : (((n+1 : ℕ) : ℝ))⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity : (0 : ℝ) < ((n+1 : ℕ) : ℝ))).mpr (by norm_cast; omega)
  have hx' : ‖x-(fun _ : Fin q ↦ (1/2 : ℝ))‖ <
      1/2 + (((n+1 : ℕ) : ℝ))⁻¹ := by
    simpa only [originalIIDSharpPalmWindow,originalIIDSharpPalmWindowRadius,
      Metric.mem_ball,dist_eq_norm] using hx
  have ht := norm_add_le (x-(fun _ : Fin q ↦ (1/2 : ℝ))) (fun _ : Fin q ↦ (1/2 : ℝ))
  rw [sub_add_cancel] at ht
  linarith

/-- The explicit original open window is bounded. -/
theorem isBounded_originalIIDSharpPalmWindow (q n : ℕ) :
    Bornology.IsBounded (originalIIDSharpPalmWindow q n) := Metric.isBounded_ball

/-- No extra local-finiteness hypothesis is needed for these actual windows. -/
theorem volume_originalIIDSharpPalmWindow_ne_top (q n : ℕ) :
    (volume : Measure (Fin q → ℝ)) (originalIIDSharpPalmWindow q n) ≠ ⊤ :=
  ne_top_of_le_ne_top
    (isCompact_closedBall (fun _ : Fin q ↦ (1/2 : ℝ))
      (originalIIDSharpPalmWindowRadius n)).measure_ne_top
    (measure_mono Metric.ball_subset_closedBall)

/-- The physical open-window volume is computed exactly in the full
coordinate dimension, without a boundary-null premise. -/
theorem volume_originalIIDSharpPalmWindow (q n : ℕ) :
    (volume : Measure (Fin q → ℝ)) (originalIIDSharpPalmWindow q n) =
      ENNReal.ofReal ((2 * originalIIDSharpPalmWindowRadius n)^q) := by
  simpa only [originalIIDSharpPalmWindow,Fintype.card_fin] using
    Real.volume_pi_ball (fun _ : Fin q ↦ (1/2 : ℝ)) (originalIIDSharpPalmWindowRadius_pos n)

/-- These genuine bounded open windows have volume tending to the original
unit-cube volume one, including when q is zero. -/
theorem tendsto_volume_originalIIDSharpPalmWindow (q : ℕ) :
    Tendsto (fun n ↦ (volume : Measure (Fin q → ℝ)) (originalIIDSharpPalmWindow q n))
      atTop (𝓝 1) := by
  have he : Tendsto (fun n : ℕ ↦ (((n+1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [Nat.cast_add,Nat.cast_one,one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ)+1)) atTop (𝓝 0))
  have hr : Tendsto originalIIDSharpPalmWindowRadius atTop (𝓝 (1/2 : ℝ)) := by
    change Tendsto (fun n : ℕ ↦ (1/2 : ℝ)+(((n+1 : ℕ) : ℝ))⁻¹) atTop (𝓝 (1/2 : ℝ))
    simpa only [add_zero] using
      (tendsto_const_nhds.add he : Tendsto (fun n ↦ (1/2 : ℝ)+(((n+1 : ℕ) : ℝ))⁻¹)
        atTop (𝓝 ((1/2 : ℝ)+0)))
  have hp : Tendsto (fun n ↦ (2 * originalIIDSharpPalmWindowRadius n)^q) atTop (𝓝 (1 : ℝ)) := by
    convert ((tendsto_const_nhds.mul hr).pow q) using 1
    norm_num
  simpa only [volume_originalIIDSharpPalmWindow,ENNReal.ofReal_one,Function.comp_def] using
    ENNReal.continuous_ofReal.tendsto (1 : ℝ) |>.comp hp

/-- Bounds for the explicit true open windows alone suffice to recover the
sharp unit spatial factor. Both A and L may be infinite. -/
theorem le_of_sharp_palm_window_bounds (q : ℕ) (A L : ℝ≥0∞)
    (h : ∀ n, A ≤ (volume : Measure (Fin q → ℝ)) (originalIIDSharpPalmWindow q n) * L) :
    A ≤ L := by
  have ht := ENNReal.Tendsto.mul_const (b := L) (tendsto_volume_originalIIDSharpPalmWindow q)
    (Or.inl (one_ne_zero : (1 : ℝ≥0∞) ≠ 0))
  simpa only [one_mul] using le_of_tendsto_of_tendsto' tendsto_const_nhds ht h

/-- Every bounded-open-window bound containing the original physical unit
cube implies the sharp bound with volume one. -/
theorem le_of_bounded_open_palm_window_bounds (q : ℕ) (A L : ℝ≥0∞)
    (h : ∀ U : Set (Fin q → ℝ), IsOpen U → Bornology.IsBounded U →
      palmUnitCube (Fin q) ⊆ U → A ≤ (volume : Measure (Fin q → ℝ)) U * L) : A ≤ L := by
  apply le_of_sharp_palm_window_bounds q A L
  intro n
  exact h _ (isOpen_originalIIDSharpPalmWindow q n) (isBounded_originalIIDSharpPalmWindow q n)
    (palmUnitCube_subset_originalIIDSharpPalmWindow q n)

/-- The form consumed by physical window estimates: one may request open
and measurable windows, the original cube inclusion, finite volume, and an
explicit uniform norm bound before applying the same sharp scalar limit. -/
theorem le_of_open_palm_window_physical_bounds (q : ℕ) (A L : ℝ≥0∞)
    (h : ∀ U : Set (Fin q → ℝ), IsOpen U → MeasurableSet U →
      palmUnitCube (Fin q) ⊆ U → (volume : Measure (Fin q → ℝ)) U ≠ ⊤ →
      ∀ W : ℝ, 0 < W → (∀ x ∈ U, ‖x‖ ≤ W) → A ≤ (volume : Measure (Fin q → ℝ)) U * L) : A ≤ L := by
  apply le_of_sharp_palm_window_bounds q A L
  intro n
  exact h _ (isOpen_originalIIDSharpPalmWindow q n) (isOpen_originalIIDSharpPalmWindow q n).measurableSet
    (palmUnitCube_subset_originalIIDSharpPalmWindow q n) (volume_originalIIDSharpPalmWindow_ne_top q n)
    2 (by norm_num) (fun x hx ↦ norm_le_two_of_mem_originalIIDSharpPalmWindow q n hx)

end OTSelector.Reconstruction
