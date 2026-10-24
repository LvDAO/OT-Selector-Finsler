import OTSelector.Reconstruction.FinslerOriginalClockSplitting
import OTSelector.Geometry.FinslerComparisonIntrinsicHessian
import OTSelector.Geometry.FinslerSeedActiveJacobian

/-!
# Actual flow analytic data for the constructed clock splitting

This file supplies the actual analytic data that the constructed Finsler momentum clock
splitting uses: the honest manifold-to-chart derivative bridges for the actual label
family, the nonzero actual chart velocity, the actual momentum normality along the actual
label directions, and the transversality (linear independence) of those label images.

The actual label-family differentials of the clock construction are the honest manifold
derivatives of the joint actual family; composing them gives the ordinary chart
differential of the actual chart readout. The chart readout differential is the momentum
family's position part, so the comparison normal field and the comparison's nonzero joint
time derivative transfer to the actual chart velocity, momentum and label images.
-/
open Set Function Filter MeasureTheory Manifold Matrix Module Metric Bundle
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The intrinsic fiber model of an actual point is the identity linear equivalence on the
model space, so the intrinsic label differential is the honest manifold differential. -/
theorem familyLabelVelocityDifferential_eq_mfderiv (Γ : W × ℝ → M) (q : W × ℝ) :
    familyLabelVelocityDifferential (E := E) Γ q =
      mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q := by
  rw [familyLabelVelocityDifferential]
  have hid : (tangentFiberModelEquiv (Γ q)).symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, E) (Γ q)) := by
    ext v
    rfl
  rw [hid, ContinuousLinearMap.id_comp]

/-- The genuine chart differential is the differential of the actual chart chart. -/
theorem familyChartVelocityDifferential_eq_mfderiv (old : M) (Γ : W × ℝ → M) (q : W × ℝ) :
    familyChartVelocityDifferential (E := E) old Γ q =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Γ q) := by
  rw [familyChartVelocityDifferential]
  have hid : (tangentFiberModelEquiv (Γ q)).toContinuousLinearMap =
      ContinuousLinearMap.id ℝ E := by
    ext v
    rfl
  rw [hid, ContinuousLinearMap.comp_id]

/-- The actual chart differential of the actual joint label family is the ordinary chart
differential of the actual chart readout. -/
theorem familyChartVelocityDifferential_comp_familyLabelVelocityDifferential
    (old : M) {Γ : W × ℝ → M} {q : W × ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
    (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    (familyChartVelocityDifferential (E := E) old Γ q).comp
        (familyLabelVelocityDifferential (E := E) Γ q) =
      fderiv ℝ (fun q' : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ q')) q := by
  rw [familyChartVelocityDifferential_eq_mfderiv,
    familyLabelVelocityDifferential_eq_mfderiv]
  have hg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun y : M ↦ extChartAt 𝓘(ℝ, E) old y) (Γ q) :=
    mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E))
      (by simpa only [extChartAt_source] using hx)
  have h := mfderiv_comp q hg hΓ
  rw [mfderiv_eq_fderiv] at h
  exact h.symm

/-- The actual joint time velocity of the label family is the chart readout time derivative. -/
theorem chartClockVelocity_eq_fderiv {old : M} {Γ : W × ℝ → M} {q : W × ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
    (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    chartClockVelocity F old Γ q =
      fderiv ℝ (fun q' : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ q')) q
        ((0 : W), (1 : ℝ)) := by
  rw [show chartClockVelocity F old Γ q =
      (familyChartVelocityDifferential (E := E) old Γ q)
        (familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ))) from rfl]
  rw [← ContinuousLinearMap.comp_apply,
    familyChartVelocityDifferential_comp_familyLabelVelocityDifferential (E := E) old hΓ hx]

/-- The actual joint label image of the label family is the chart readout label derivative. -/
theorem chartClockLabelVelocity_eq_fderiv (bW : Basis ι ℝ W) {old : M} {Γ : W × ℝ → M}
    {q : W × ℝ} (hΓ : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
    (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source) (i : ι) :
    chartClockLabelVelocity F bW old Γ q i =
      fderiv ℝ (fun q' : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ q')) q
        (bW i, (0 : ℝ)) := by
  rw [show chartClockLabelVelocity F bW old Γ q i =
      (familyChartVelocityDifferential (E := E) old Γ q)
        (familyLabelVelocityDifferential (E := E) Γ q (bW i, (0 : ℝ))) from rfl]
  rw [← ContinuousLinearMap.comp_apply,
    familyChartVelocityDifferential_comp_familyLabelVelocityDifferential (E := E) old hΓ hx]

/-- The actual chart readout is differentiable whenever the joint actual family is. -/
theorem mdifferentiableAt_chartReadout_of_chartFamily {old : M} {Γ : W × ℝ → M} {q : W × ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
    (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E)
      (fun q' : W × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ q')) q :=
  (mdifferentiableAt_extChartAt (I := 𝓘(ℝ, E))
    (by simpa only [extChartAt_source] using hx)).comp q hΓ

/-- The label image is the ordinary partial label derivative of the chart readout. -/
theorem chartClockLabelVelocity_eq_partial_fderiv (bW : Basis ι ℝ W) {old : M}
    {Γ : W × ℝ → M} {q : W × ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
    (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source) (i : ι) :
    chartClockLabelVelocity F bW old Γ q i =
      fderiv ℝ (fun z : W ↦ extChartAt 𝓘(ℝ, E) old (Γ (z, q.2))) q.1 (bW i) := by
  let f : W × ℝ → E := fun q' ↦ extChartAt 𝓘(ℝ, E) old (Γ q')
  have hf : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) f q :=
    mdifferentiableAt_chartReadout_of_chartFamily hΓ hx
  have hd : DifferentiableAt ℝ f q := hf.differentiableAt
  have hline : HasFDerivAt (fun z : W ↦ (z, q.2)) (ContinuousLinearMap.inl ℝ W ℝ) q.1 :=
    (hasFDerivAt_id (𝕜 := ℝ) q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have hline_d : DifferentiableAt ℝ (fun z : W ↦ (z, q.2)) q.1 := hline.differentiableAt
  have hkey : fderiv ℝ (fun z : W ↦ f (z, q.2)) q.1 =
      (fderiv ℝ f q).comp (ContinuousLinearMap.inl ℝ W ℝ) := by
    have hlinef : fderiv ℝ (fun z : W ↦ (z, q.2)) q.1 = ContinuousLinearMap.inl ℝ W ℝ :=
      hline.fderiv
    have h := fderiv_comp (𝕜 := ℝ) (g := f) (f := fun z : W ↦ (z, q.2)) (x := q.1)
      hd hline_d
    rw [hlinef] at h
    exact h
  rw [chartClockLabelVelocity_eq_fderiv bW hΓ hx i]
  change (fderiv ℝ f q) ((bW i), (0 : ℝ)) =
    (fderiv ℝ (fun z : W ↦ f (z, q.2)) q.1) (bW i)
  rw [hkey, ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.inl_apply]

/-- The actual chart velocity is the ordinary partial time derivative of the chart readout. -/
theorem chartClockVelocity_eq_partial_fderiv {old : M} {Γ : W × ℝ → M} {q : W × ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
    (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    chartClockVelocity F old Γ q =
      fderiv ℝ (fun s : ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ (q.1, s))) q.2 (1 : ℝ) := by
  let f : W × ℝ → E := fun q' ↦ extChartAt 𝓘(ℝ, E) old (Γ q')
  have hf : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) f q :=
    mdifferentiableAt_chartReadout_of_chartFamily hΓ hx
  have hd : DifferentiableAt ℝ f q := hf.differentiableAt
  have hline : HasFDerivAt (fun s : ℝ ↦ (q.1, s)) (ContinuousLinearMap.inr ℝ W ℝ) q.2 :=
    (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) q.2)
  have hline_d : DifferentiableAt ℝ (fun s : ℝ ↦ (q.1, s)) q.2 := hline.differentiableAt
  have hkey : fderiv ℝ (fun s : ℝ ↦ f (q.1, s)) q.2 =
      (fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ W ℝ) := by
    have hlinef : fderiv ℝ (fun s : ℝ ↦ (q.1, s)) q.2 = ContinuousLinearMap.inr ℝ W ℝ :=
      hline.fderiv
    have h := fderiv_comp (𝕜 := ℝ) (g := f) (f := fun s : ℝ ↦ (q.1, s)) (x := q.2)
      hd hline_d
    rw [hlinef] at h
    exact h
  rw [chartClockVelocity_eq_fderiv hΓ hx]
  change (fderiv ℝ f q) ((0 : W), (1 : ℝ)) =
    (fderiv ℝ (fun s : ℝ ↦ f (q.1, s)) q.2) (1 : ℝ)
  rw [hkey, ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.inr_apply]

/-- The actual chart velocity is the ordinary derivative of the actual chart curve. -/
theorem chartClockVelocity_eq_deriv {old : M} {Γ : W × ℝ → M} {q : W × ℝ}
    (hΓ : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
    (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    chartClockVelocity F old Γ q =
      deriv (fun s : ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γ (q.1, s))) q.2 := by
  rw [chartClockVelocity_eq_partial_fderiv hΓ hx, fderiv_apply_one_eq_deriv]


/-! ## Actual analytic data: nonzero velocity, momentum normality, transversality -/

/-- The actual chart velocity is the chart differential of the exact intrinsic time
derivative of the actual joint label family. -/
theorem chartClockVelocity_eq_mfderiv_chart {old : M} {Γ : W × ℝ → M} {q : W × ℝ} :
    chartClockVelocity F old Γ q =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Γ q)
        (mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q ((0 : W), (1 : ℝ))) := by
  rw [chartClockVelocity, familyLabelVelocityDifferential_eq_mfderiv,
    familyChartVelocityDifferential_eq_mfderiv]
  rfl

/-- A nonzero intrinsic time derivative of the actual joint family gives a nonzero
actual chart velocity. -/
theorem chartClockVelocity_ne_zero_of_time_mfderiv {old : M} {Γ : W × ℝ → M} {q : W × ℝ}
    (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (htime : mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q ((0 : W), (1 : ℝ)) ≠ 0) :
    chartClockVelocity F old Γ q ≠ 0 := by
  have hinj : Function.Injective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Γ q)) :=
    (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E)) (x := old) hx).bijective.1
  rw [chartClockVelocity_eq_mfderiv_chart]
  intro hzero
  exact htime (hinj (by rw [hzero, _root_.map_zero]))

/-- The intrinsic time differential of the actual joint family, in its own right. -/
theorem familyLabelVelocityDifferential_time_eq_mfderiv {Γ : W × ℝ → M} {q : W × ℝ} :
    familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ)) =
      mfderiv 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q ((0 : W), (1 : ℝ)) :=
  congrArg (fun T : (W × ℝ) →L[ℝ] E ↦ T ((0 : W), (1 : ℝ)))
    (familyLabelVelocityDifferential_eq_mfderiv Γ q)

/-- The intrinsic time differential is nonzero whenever the chart velocity is. -/
theorem familyLabelVelocityDifferential_time_ne_zero_of_chartVelocity_ne_zero
    {old : M} {Γ : W × ℝ → M} {q : W × ℝ}
    (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hvel : chartClockVelocity F old Γ q ≠ 0) :
    familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ)) ≠ 0 := by
  rw [familyLabelVelocityDifferential_time_eq_mfderiv]
  intro hzero
  apply hvel
  rw [chartClockVelocity_eq_mfderiv_chart, hzero, _root_.map_zero]

/-- A covector vanishing on a vector puts that vector in the kernel of the clock,
with zero clock coordinate. -/
theorem covectorClock_apply_of_eq_zero (p : E →L[ℝ] ℝ) (v : E) (hv : p v ≠ 0)
    {u : E} (hu : p u = 0) :
    covectorClock p v hv u = (0, (⟨u, hu⟩ : p.ker)) := by
  apply Prod.ext
  · rw [covectorClock_fst, hu, zero_div]
  · apply Subtype.ext
    change (((covectorSplitting p v hv).symm u).1 : E) = u
    rw [covectorSplitting_symm_fst, hu]
    simp

/-- The actual momentum annihilates the actual label images: momentum normality in
the actual chart. -/
theorem chartClockCovector_apply_labelVelocity_eq_zero (bW : Basis ι ℝ W) {old : M}
    {Γ : W × ℝ → M} {q : W × ℝ}
    (hmd : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
    (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hnormal : ∀ i, (F.chartMomentumFamily old (fun z s ↦ Γ (z, s)) q).2
      (fderiv ℝ (fun z : W ↦ extChartAt 𝓘(ℝ, E) old (Γ (z, q.2))) q.1 (bW i)) = 0)
    (i : ι) :
    chartClockCovector F old Γ q (chartClockLabelVelocity F bW old Γ q i) = 0 := by
  rw [chartClockCovector]
  rw [show (familyChartVelocityDifferential (E := E) old Γ q)
        (familyLabelVelocityDifferential (E := E) Γ q ((0 : W), (1 : ℝ))) =
      chartClockVelocity F old Γ q from rfl]
  rw [chartClockVelocity_eq_deriv hmd hx,
    chartClockLabelVelocity_eq_partial_fderiv bW hmd hx i]
  simpa only [chartMomentumFamily, eulerLagrangePhaseLift, fiberLegendre,
    Function.comp_def] using hnormal i

/-- Injective joint differential at a point restricts to the label direction. -/
theorem fderiv_label_injective_of_joint_injective {Φ : ℝ → W → E} {t₀ : ℝ} {w₀ : W}
    (hd : DifferentiableAt ℝ (fun q : ℝ × W ↦ Φ q.1 q.2) (t₀, w₀))
    (hinj : Function.Injective
      (fderiv ℝ (fun q : ℝ × W ↦ Φ q.1 q.2) (t₀, w₀))) :
    Function.Injective (fderiv ℝ (fun z : W ↦ Φ t₀ z) w₀) := by
  have hline : HasFDerivAt (fun z : W ↦ (t₀, z)) (ContinuousLinearMap.inr ℝ ℝ W) w₀ :=
    (hasFDerivAt_const t₀ w₀).prodMk (hasFDerivAt_id (𝕜 := ℝ) w₀)
  have hcomp : HasFDerivAt (fun z : W ↦ Φ t₀ z)
      ((fderiv ℝ (fun q : ℝ × W ↦ Φ q.1 q.2) (t₀, w₀)).comp
        (ContinuousLinearMap.inr ℝ ℝ W)) w₀ :=
    HasFDerivAt.comp (f := fun z : W ↦ (t₀, z)) (g := fun q : ℝ × W ↦ Φ q.1 q.2)
      (x := w₀) (f' := ContinuousLinearMap.inr ℝ ℝ W)
      (g' := fderiv ℝ (fun q : ℝ × W ↦ Φ q.1 q.2) (t₀, w₀))
      hd.hasFDerivAt hline
  rw [hcomp.fderiv]
  intro x y hxy
  have h1 : ContinuousLinearMap.inr ℝ ℝ W x = ContinuousLinearMap.inr ℝ ℝ W y :=
    hinj (by simpa only [ContinuousLinearMap.comp_apply] using hxy)
  simpa only [ContinuousLinearMap.inr_apply, Prod.mk.injEq, eq_self_iff_true,
    true_and] using h1

/-- Linear algebra: the splitting maps independent transverse kernel directions to
independent kernel coordinates. -/
theorem linearIndependent_covectorClock_images (bW : Basis ι ℝ W) (p : E →L[ℝ] ℝ)
    (v : E) (hv : p v ≠ 0) {T : W →L[ℝ] E} (hT : Function.Injective T)
    (hker : ∀ i, p (T (bW i)) = 0) :
    LinearIndependent ℝ (fun i ↦ (covectorClock p v hv (T (bW i))).2) := by
  have hLI : LinearIndependent ℝ (fun i ↦ T (bW i)) :=
    bW.linearIndependent.map' (T : W →ₗ[ℝ] E) (LinearMap.ker_eq_bot.mpr hT)
  have hLI2 : LinearIndependent ℝ
      (fun i ↦ (⟨T (bW i), hker i⟩ : p.ker)) :=
    LinearIndependent.of_comp (f := (p.ker.subtypeL : p.ker →ₗ[ℝ] E))
      (v := fun i ↦ (⟨T (bW i), hker i⟩ : p.ker))
      (show LinearIndependent ℝ (fun i ↦ T (bW i)) from hLI)
  have hfam : (fun i ↦ (covectorClock p v hv (T (bW i))).2) =
      fun i ↦ (⟨T (bW i), hker i⟩ : p.ker) := by
    funext i
    have h := congrArg Prod.snd (covectorClock_apply_of_eq_zero p v hv (hker i))
    simpa using h
  rw [hfam]
  exact hLI2

/-- Transversality of the actual label images in the actual momentum kernel. -/
theorem chartClockSplitting_labelVelocity_linearIndependent (hF : F.IsSmoothStronglyConvex)
    (bW : Basis ι ℝ W) {old : M} {Γ : W × ℝ → M} {q : W × ℝ}
    (hx : Γ q ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hmd : MDifferentiableAt 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) Γ q)
    (hvel : chartClockVelocity F old Γ q ≠ 0)
    (hker : ∀ i, chartClockCovector F old Γ q
      (chartClockLabelVelocity F bW old Γ q i) = 0)
    (hT : Function.Injective
      (fderiv ℝ (fun z : W ↦ extChartAt 𝓘(ℝ, E) old (Γ (z, q.2))) q.1))
    (hTlabel : ∀ i, fderiv ℝ (fun z : W ↦ extChartAt 𝓘(ℝ, E) old (Γ (z, q.2))) q.1 (bW i) =
      chartClockLabelVelocity F bW old Γ q i) :
    LinearIndependent ℝ (fun i ↦ (chartClockSplitting F old Γ q
      (ne_of_gt (chartClockCovector_velocity_pos hF hx hvel))
      (chartClockLabelVelocity F bW old Γ q i)).2) := by
  have hpv : chartClockCovector F old Γ q (chartClockVelocity F old Γ q) ≠ 0 :=
    ne_of_gt (chartClockCovector_velocity_pos hF hx hvel)
  have hLI : LinearIndependent ℝ (fun i ↦
      (fderiv ℝ (fun z : W ↦ extChartAt 𝓘(ℝ, E) old (Γ (z, q.2))) q.1) (bW i)) :=
    bW.linearIndependent.map' _
      (LinearMap.ker_eq_bot.mpr hT)
  have hLI2 : LinearIndependent ℝ (fun i ↦
      (⟨(fderiv ℝ (fun z : W ↦ extChartAt 𝓘(ℝ, E) old (Γ (z, q.2))) q.1) (bW i),
        (by rw [hTlabel i]; exact hker i)⟩ :
        (chartClockCovector F old Γ q).ker)) :=
    LinearIndependent.of_comp
      (f := ((chartClockCovector F old Γ q).ker.subtypeL :
        (chartClockCovector F old Γ q).ker →ₗ[ℝ] E))
      (v := fun i ↦
        (⟨(fderiv ℝ (fun z : W ↦ extChartAt 𝓘(ℝ, E) old (Γ (z, q.2))) q.1) (bW i),
          (by rw [hTlabel i]; exact hker i)⟩ :
          (chartClockCovector F old Γ q).ker))
      (show LinearIndependent ℝ (fun i ↦
        (fderiv ℝ (fun z : W ↦ extChartAt 𝓘(ℝ, E) old (Γ (z, q.2))) q.1) (bW i)) from hLI)
  have hfam : (fun i ↦ (chartClockSplitting F old Γ q hpv
        (chartClockLabelVelocity F bW old Γ q i)).2) =
      fun i ↦ (⟨(fderiv ℝ (fun z : W ↦ extChartAt 𝓘(ℝ, E) old (Γ (z, q.2))) q.1) (bW i),
        (by rw [hTlabel i]; exact hker i)⟩ :
        (chartClockCovector F old Γ q).ker) := by
    funext i
    rw [chartClockSplitting]
    have h := congrArg Prod.snd
      (covectorClock_apply_of_eq_zero (chartClockCovector F old Γ q)
        (chartClockVelocity F old Γ q) hpv (hker i))
    rw [h]
    exact Subtype.ext (hTlabel i).symm
  rw [hfam]
  exact hLI2

/-! ## The actual analytic data of an original seed, in every legal chart and active time -/

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [PreconnectedSpace M]
  {u : M → ℝ}

/-- **Actual flow analytic data.** On a full-measure set of original labels, for every
legal chart and every active time, the actual momentum clock has nonzero velocity, it
annihilates the actual label images, and the actual intrinsic label Hessian is
invertible. The transversality of the actual label images in the actual momentum
kernel is used internally to invert the actual Hessian, so all three analytic-data
gaps of the constructed clock splitting are closed simultaneously. -/
theorem calibratedSeed_actualFlowData_isUnit_det
    (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instActualFlowLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure] :
    ∀ᵐ w ∂m.restrict S.labels, ∀ (terminal : M) (t : ℝ),
      t ∈ interior (S.calibrationTimes w) →
      S.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
      chartClockVelocity (F := F) terminal
          (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t) ≠ 0 ∧
        (∀ i, chartClockCovector (F := F) terminal
          (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t)
          (chartClockLabelVelocity (F := F) (bW := Module.finBasis ℝ S.covector.ker)
            terminal (fun q : S.covector.ker × ℝ ↦ S.curve q.1 q.2) (w, t) i) = 0) ∧
        IsUnit (F.familyLabelHessianMatrix (Module.finBasis ℝ S.covector.ker)
          (fun q ↦ S.curve q.1 q.2) (w, t)).det := by
  filter_upwards [S.ae_exists_comparison_active_jacobian D hF hcomplete hu m] with w hdata
  obtain ⟨hw, C, hsub, hcurve, hjet, hjac⟩ := hdata
  intro terminal t ht hlegal
  let Γ : S.covector.ker × ℝ → M := fun q ↦ S.curve q.1 q.2
  have hwU : w ∈ S.openLabels := S.labels_subset hw
  have hcont : ContinuousAt Γ (w, t) := S.continuousAt_joint_curve (q := (w, t)) hwU
  have hchart : DifferentiableAt ℝ
      (fun q : S.covector.ker × ℝ ↦ extChartAt 𝓘(ℝ, E) terminal (Γ q)) (w, t) :=
    (hjet terminal t hlegal).1.fst.differentiableAt
  have hmd : MDifferentiableAt 𝓘(ℝ, S.covector.ker × ℝ) 𝓘(ℝ, E) Γ (w, t) :=
    (mdifferentiableAt_iff_target_of_mem_source (I := 𝓘(ℝ, S.covector.ker × ℝ))
      (I' := 𝓘(ℝ, E)) (f := Γ) (x := ((w, t) : S.covector.ker × ℝ)) (y := terminal)
      (by simpa only [extChartAt_source] using hlegal)).mpr
      ⟨hcont, hchart.mdifferentiableAt⟩
  have htime : mfderiv 𝓘(ℝ, S.covector.ker × ℝ) 𝓘(ℝ, E) Γ (w, t)
      ((0 : S.covector.ker), (1 : ℝ)) ≠ 0 :=
    S.joint_time_mfderiv_ne_zero hw t hmd
  have hvel : chartClockVelocity (F := F) terminal Γ (w, t) ≠ 0 :=
    chartClockVelocity_ne_zero_of_time_mfderiv (F := F) hlegal htime
  have hD1 : familyLabelVelocityDifferential (E := E) Γ (w, t)
      ((0 : S.covector.ker), (1 : ℝ)) ≠ 0 :=
    familyLabelVelocityDifferential_time_ne_zero_of_chartVelocity_ne_zero (F := F)
      hlegal hvel
  have hline : HasFDerivAt (fun z : S.covector.ker ↦ (z, t))
      ((ContinuousLinearMap.id ℝ S.covector.ker).prod
        (0 : S.covector.ker →L[ℝ] ℝ)) w :=
    (hasFDerivAt_id (𝕜 := ℝ) w).prodMk (hasFDerivAt_const t w)
  have hs₁ := HasFDerivAt.comp (f := fun z : S.covector.ker ↦ (z, t))
    (g := fun q : S.covector.ker × ℝ ↦ (F.chartMomentumFamily terminal S.curve q).1)
    (x := w) (f' := (ContinuousLinearMap.id ℝ S.covector.ker).prod
      (0 : S.covector.ker →L[ℝ] ℝ))
    (g' := (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp
      (fderiv ℝ (F.chartMomentumFamily terminal C.curve) (w, t)))
    (hjet terminal t hlegal).1.fst hline
  have hs₂ := HasFDerivAt.comp (f := fun z : S.covector.ker ↦ (z, t))
    (g := fun q : S.covector.ker × ℝ ↦ (F.chartMomentumFamily terminal C.curve q).1)
    (x := w) (f' := (ContinuousLinearMap.id ℝ S.covector.ker).prod
      (0 : S.covector.ker →L[ℝ] ℝ))
    (g' := (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp
      (fderiv ℝ (F.chartMomentumFamily terminal C.curve) (w, t)))
    (hjet terminal t hlegal).2.fst hline
  have hlabelEq : fderiv ℝ (fun z : S.covector.ker ↦
        extChartAt 𝓘(ℝ, E) terminal (S.curve z t)) w =
      fderiv ℝ (fun z : S.covector.ker ↦
        extChartAt 𝓘(ℝ, E) terminal (C.curve z t)) w :=
    hs₁.fderiv.trans hs₂.fderiv.symm
  have hmomEq : F.chartMomentumFamily terminal S.curve (w, t) =
      F.chartMomentumFamily terminal C.curve (w, t) := by
    simp only [chartMomentumFamily, hcurve]
  have hcomparisonLegal : C.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source := by
    rw [show C.curve w t = S.curve w t from by rw [hcurve]]
    exact hlegal
  have hnormal : ∀ i, (F.chartMomentumFamily terminal (fun z s ↦ Γ (z, s)) (w, t)).2
      (fderiv ℝ (fun z : S.covector.ker ↦
        extChartAt 𝓘(ℝ, E) terminal (Γ (z, t))) w
        ((Module.finBasis ℝ S.covector.ker) i)) = 0 := by
    intro i
    have hC := C.normal terminal t hcomparisonLegal
      ((Module.finBasis ℝ S.covector.ker) i)
    rw [hlabelEq, hmomEq]
    exact hC
  have hker : ∀ i, chartClockCovector (F := F) terminal Γ (w, t)
      (chartClockLabelVelocity (F := F) (bW := Module.finBasis ℝ S.covector.ker)
        terminal Γ (w, t) i) = 0 :=
    chartClockCovector_apply_labelVelocity_eq_zero (F := F)
      (bW := Module.finBasis ℝ S.covector.ker) hmd hlegal hnormal
  have hdjoint : DifferentiableAt ℝ
      (fun q : ℝ × S.covector.ker ↦ extChartAt 𝓘(ℝ, E) terminal (S.curve q.2 q.1))
      (t, w) :=
    DifferentiableAt.comp
      (g := fun q : S.covector.ker × ℝ ↦ extChartAt 𝓘(ℝ, E) terminal (Γ q))
      (f := fun q : ℝ × S.covector.ker ↦ (q.2, q.1)) (x := (t, w)) hchart
      (differentiableAt_snd.prodMk differentiableAt_fst)
  have hjacpos : 0 < parameterizedJacobian
      (fun q : ℝ × S.covector.ker ↦ extChartAt 𝓘(ℝ, E) terminal (S.curve q.2 q.1))
      S.normalization (t, w) := hjac terminal t ht hlegal
  have hinjJoint : Function.Injective (fderiv ℝ
      (fun q : ℝ × S.covector.ker ↦
        extChartAt 𝓘(ℝ, E) terminal (S.curve q.2 q.1)) (t, w)) :=
    injective_fderiv_of_parameterizedJacobian_pos (ℓ := S.normalization) hjacpos
  have hT : Function.Injective (fderiv ℝ
      (fun z : S.covector.ker ↦ extChartAt 𝓘(ℝ, E) terminal (S.curve z t)) w) :=
    fderiv_label_injective_of_joint_injective
      (Φ := fun s (z : S.covector.ker) ↦ extChartAt 𝓘(ℝ, E) terminal (S.curve z s))
      hdjoint hinjJoint
  have hTlabel : ∀ i, fderiv ℝ (fun z : S.covector.ker ↦
        extChartAt 𝓘(ℝ, E) terminal (S.curve z t)) w
        ((Module.finBasis ℝ S.covector.ker) i) =
      chartClockLabelVelocity (F := F) (bW := Module.finBasis ℝ S.covector.ker)
        terminal Γ (w, t) i := by
    intro i
    exact (chartClockLabelVelocity_eq_partial_fderiv (F := F)
      (bW := Module.finBasis ℝ S.covector.ker) hmd hlegal i).symm
  have hli : LinearIndependent ℝ (fun i ↦ (chartClockSplitting (F := F) terminal Γ (w, t)
      (ne_of_gt (chartClockCovector_velocity_pos hF hlegal hvel))
      (chartClockLabelVelocity (F := F) (bW := Module.finBasis ℝ S.covector.ker)
        terminal Γ (w, t) i)).2) :=
    chartClockSplitting_labelVelocity_linearIndependent (F := F) hF
      (Module.finBasis ℝ S.covector.ker) hlegal hmd hvel hker hT hTlabel
  exact ⟨hvel, hker,
    OTSelector.Reconstruction.calibratedSeed_familyLabelHessianMatrix_isUnit_det hF hlegal
      hD1 hvel hker hli⟩


end OTSelector.Geometry.ContinuousFinslerNorm
