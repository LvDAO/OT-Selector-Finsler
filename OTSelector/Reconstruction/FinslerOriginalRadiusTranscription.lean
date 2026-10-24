import OTSelector.Reconstruction.FinslerOriginalF13Resolution
import OTSelector.Reconstruction.FinslerOriginalUniformBoundReconciliation
import OTSelector.Reconstruction.FinslerOriginalWeightedUpperLocalizationRestated
import OTSelector.Probability.FinslerMarkedAtlasIdentification

/-!
# F13 radius transcription: definitive settlement

## Verdict

The paper's frozen estimate uses the BLOCK COUNT
r = floor ((n + 1) / m^q), the number of marks in a block, NOT a bounded
per-cell radius.  The block count grows linearly in n; the frozen kernel is the
n-scale-normalized kernel r ^ (2/q) * kin, whose intrinsic bound is
r ^ (2/q) * Cb * q, growing like n ^ (2/q).  The repo's radius transcription is
therefore PAPER-FAITHFUL.  What is NOT paper-faithful is the localization
theorem's UNIFORM-in-n hypothesis hCbnd, which asks for one constant Cbnd
majorizing the raw frozen kernel at the growing block count.  We prove that
uniform bound is FALSE for the lane: it is equivalent to the bounded-radius
condition r ^ (2/q) <= 1, which fails, and no constant Cbnd exists (Section 4).
The corrected hypothesis, and the corrected hCbnd producer, is the intrinsic
bound (Sections 3 and 5), exactly the field hCbnd_intrinsic of the repaired
structure PopDataIntrinsic (FinslerOriginalPopDataIntrinsicBound.lean), consumed
by physicalWeightedLocalizationFamily_of_popDataIntrinsic.

## The definitional chain (with line numbers)

* frozenMarkedRadius w n c = ((Nat.floor (((n+1:Nat):Real) * (w c:Real)):Nat):Real)
  (FinslerFrozenBlockBridge.lean:345).  For the upper lane w = blockW q m hm,
  with (blockW q m hm c:Real) = 1 / m^q
  (FinslerOriginalWeightedUpperLocalizationRestated.lean:80), this is
  frozenMarkedRadius = floor ((n+1)/m^q): the BLOCK COUNT (proved as
  frozenMarkedRadius_blockW_chain below and in FinslerOriginalF13Resolution).
* markedKineticKernel r kin markS markT x y
    = r ^ (2/q) * kin (markS x).2 (markT y).2 (mDisplacement ...)
  (FinslerTileBlockLawComparison.lean:370): the RAW n-scale-normalized kernel.
* The localization theorem's hCbnd
  (FinslerOriginalIIDPressureUpperLocalization.lean:239) is
  forall n c x y, |markedKineticKernel (frozenMarkedRadius w n c) (kin c) ... x y|
    <= Cbnd,
  i.e. a uniform constant bound on the raw kernel at the block-count radius.
  Since r ^ (2/q) grows like ((n+1)/m^q) ^ (2/q), this is unprovable.

## Paper provenance

main.tex:134 defines the empirical pressure with the n ^ (2/q) cost
normalization, V_n(t) = min over gamma of
n^(2/q) integral e d gamma + t integral f d gamma; main.tex:1405 gives the
scaled calibration defect n^(2/q)(d_F(X_i,Y_j) - u(Y_j) + u(X_i)).  The frozen
reduction (main.tex:4890-5010) freezes each macroscopic cube at its intensity
lambda n theta_bar_j (growing with n) and uses the intensity scaling
lambda ^ (1 - 2/q) p (t lambda ^ (2/q))
(eq:highd-variable-intensity-scaling); the growing block-count normalization is
exactly r ^ (2/q).  No bounded per-cell radius appears in the frozen bound, and
a bounded per-cell radius could not reproduce the n ^ (2/q) factor of the
physical kernel.  Hence the paper-faithful hypothesis is the intrinsic one,
uniform in the block count but not in n.

## What is proved here

1. frozenMarkedRadius_apply, markedKineticKernel_apply: the definitional chain
   (definitional equalities).
2. frozenMarkedRadius_blockW_chain, frozenMarkedRadius_blockW_bounds: the radius
   is the block count floor((n+1)/m^q) and satisfies
   (n+1)/m^q - 1 <= r <= (n+1)/m^q (linear growth).
3. frozenMarkedRadius_tendsto_atTop, frozenMarkedRadius_blockW_tendsto_atTop,
   frozenMarkedRadius_blockW_rpow_tendsto_atTop: the radius and its intrinsic
   scale r^(2/q) tend to infinity.
4. hCbnd_intrinsic_of_hkin_bound and hCbnd_intrinsic_blockW_of_hkin_bound: the
   corrected hCbnd producer, proving the intrinsic bound
   |kernel| <= Cb * r^(2/q) * q from the per-pair quadratic bound hkin_bound;
   the second has exactly the type of PopDataIntrinsic.hCbnd_intrinsic.
5. markedKineticKernel_abs_eq, not_uniform_markedKineticKernel_bound,
   not_uniform_frozen_bound_blockW: the uniform hCbnd is FALSE -- for any
   nonvanishing kinetic value on the marked atlas image, every constant Cbnd is
   eventually exceeded.
6. cellBoundedness_false: the cell-boundedness input r^(2/q) <= 1 of
   popData_of_intrinsic (the only remaining hypothesis converting the repaired
   intrinsic interface back to the original PopData) is false for the lane.

## Residual gap (exact)

* The falsity results carry the non-degeneracy hypothesis
  exists c x y, kin c (labelS x) (labelT y) (mDisplacement (coordS x) (coordT y))
    != 0.
  This is supplied by the actual physical kinetic of the lane (the frozen
  physical cost is not identically zero) but no term of the lane's kin is
  constructed in the repo; that geometric instantiation is the standing
  remaining gap of the upper lane, not an F13 gap.
* The repaired interface PopDataIntrinsic replaces the false uniform field by
  hCbnd_intrinsic; its construction (geometric cell/atlas/mark data and the
  F14 small-n freezing guard hsmall) is unchanged and outside this module.
* The original PopData cannot be recovered in the limit: popData_of_intrinsic's
  cell-boundedness hr is false for the block count (cellBoundedness_false).

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory
open OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ENNReal NNReal

noncomputable section

namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. The definitional chain -/

/-- The frozen radius is definitionally the real block count. -/
theorem frozenMarkedRadius_apply {ι : Type*} (w : ι → unitInterval) (n : ℕ) (c : ι) :
    frozenMarkedRadius w n c =
      ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w c : ℝ)) : ℕ) : ℝ) := rfl

/-- The frozen kernel is definitionally the raw n-scale-normalized kernel. -/
theorem markedKineticKernel_apply {Xs Yt A B : Type*} {q : ℕ} (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (x : Xs) (y : Yt) :
    markedKineticKernel (q := q) r kin markS markT x y =
      r ^ (2 / (q : ℝ)) * kin (markS x).2 (markT y).2
        (mDisplacement (markS x).1 (markT y).1) :=
  markedKineticKernel_eq_scale_mul r kin markS markT x y

/-- At the block weights of the upper lane the frozen radius is the block count
floor ((n + 1) / m^q). -/
theorem frozenMarkedRadius_blockW_chain (q m : ℕ) (hm : 0 < m) (n : ℕ)
    (c : Fin q → Fin m) :
    frozenMarkedRadius (blockW q m hm) n c =
      (Nat.floor (((n + 1 : ℕ) : ℝ) / ((m ^ q : ℕ) : ℝ)) : ℝ) :=
  frozenMarkedRadius_blockW q m hm n c

/-- The block-count radius satisfies floor((n+1)/m^q) <= r < (n+1)/m^q + 1; in
particular it grows linearly in n. -/
theorem frozenMarkedRadius_blockW_bounds (q m : ℕ) (hm : 0 < m) (n : ℕ)
    (c : Fin q → Fin m) :
    ((n + 1 : ℕ) : ℝ) / ((m ^ q : ℕ) : ℝ) - 1 ≤
        frozenMarkedRadius (blockW q m hm) n c ∧
      frozenMarkedRadius (blockW q m hm) n c ≤
        ((n + 1 : ℕ) : ℝ) / ((m ^ q : ℕ) : ℝ) := by
  have hmq : (0 : ℝ) < ((m ^ q : ℕ) : ℝ) := by exact_mod_cast pow_pos hm q
  have hnonneg : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / ((m ^ q : ℕ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hmq.le
  constructor
  · rw [frozenMarkedRadius_blockW]
    have h := Nat.sub_one_lt_floor (((n + 1 : ℕ) : ℝ) / ((m ^ q : ℕ) : ℝ))
    linarith
  · rw [frozenMarkedRadius_blockW]
    exact Nat.floor_le hnonneg

/-! ## 2. The radius grows -/

/-- For any positive block weight the frozen radius tends to infinity. -/
theorem frozenMarkedRadius_tendsto_atTop {ι : Type*} (w : ι → unitInterval) (c : ι)
    (hw : 0 < (w c : ℝ)) :
    Tendsto (fun n : ℕ => frozenMarkedRadius w n c) atTop atTop := by
  refine tendsto_atTop_atTop.2 (fun B => ?_)
  obtain ⟨N, hN⟩ := exists_nat_gt (max 0 ((B + 1) / (w c : ℝ)))
  refine ⟨N, fun n hn => ?_⟩
  have hNpos : (0 : ℝ) < (N : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hN
  have hNdiv : (B + 1) / (w c : ℝ) < (N : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hN
  have hNreal : B + 1 < (N : ℝ) * (w c : ℝ) := by
    by_cases hB : B + 1 ≤ 0
    · have hpos : 0 < (N : ℝ) * (w c : ℝ) := mul_pos hNpos hw
      linarith
    · rw [div_lt_iff₀ hw] at hNdiv
      linarith
  have hNn : (N : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    have hn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hstep : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hstep : B + 1 < ((n + 1 : ℕ) : ℝ) * (w c : ℝ) :=
    lt_of_lt_of_le hNreal (mul_le_mul_of_nonneg_right hNn.le hw.le)
  have hfloor := Nat.lt_floor_add_one (((n + 1 : ℕ) : ℝ) * (w c : ℝ))
  show B ≤ frozenMarkedRadius w n c
  unfold frozenMarkedRadius
  linarith

/-- At the lane's block weights the frozen radius tends to infinity. -/
theorem frozenMarkedRadius_blockW_tendsto_atTop (q m : ℕ) (hm : 0 < m)
    (c : Fin q → Fin m) :
    Tendsto (fun n : ℕ => frozenMarkedRadius (blockW q m hm) n c) atTop atTop := by
  refine frozenMarkedRadius_tendsto_atTop (blockW q m hm) c ?_
  rw [show ((blockW q m hm c : unitInterval) : ℝ) = 1 / ((m ^ q : ℕ) : ℝ) from rfl]
  exact div_pos one_pos (by exact_mod_cast pow_pos hm q)

/-- The intrinsic scale r ^ (2/q) of the block-count radius also tends to
infinity: this is the growing normalization of the paper's frozen kernel. -/
theorem frozenMarkedRadius_blockW_rpow_tendsto_atTop (q m : ℕ) (hq : 0 < q)
    (hm : 0 < m) (c : Fin q → Fin m) :
    Tendsto (fun n : ℕ => (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)))
      atTop atTop := by
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hexp : (0 : ℝ) < 2 / (q : ℝ) := div_pos (by norm_num) hq'
  exact (tendsto_rpow_atTop hexp).comp (frozenMarkedRadius_blockW_tendsto_atTop q m hm c)

/-! ## 3. The corrected hCbnd producer: the intrinsic frozen bound -/

/-- **The corrected frozen bound producer.**  From the per-pair quadratic bound
on the kinetic mark kernel, the frozen kernel satisfies the intrinsic bound
|kernel| <= Cb * r ^ (2/q) * q at the frozen radius r = frozenMarkedRadius w n c.
This is the paper-faithful replacement of the uniform hCbnd. -/
theorem hCbnd_intrinsic_of_hkin_bound
    {Xs Yt A B : Type*} {q : ℕ} {Cb : ℝ} (hCb0 : 0 ≤ Cb) {ι : Type*}
    (w : ι → unitInterval)
    (kin : ι → A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (hkin : ∀ (c : ι) (a : A) (b : B) (v : Fin q → ℝ),
      |kin c a b v| ≤ Cb * ∑ l, v l ^ 2) :
    ∀ (n : ℕ) (c : ι) (x : Xs) (y : Yt),
      |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c) markS markT x y| ≤
        Cb * (frozenMarkedRadius w n c) ^ (2 / (q : ℝ)) * (q : ℝ) := by
  intro n c x y
  exact markedKineticKernel_abs_le_intrinsic (q := q) (Cb := Cb)
    (r := frozenMarkedRadius w n c) hCb0 (Nat.cast_nonneg _) (kin c) markS markT
    (hkin c) (fun _ _ => mDisplacement_sq_sum_le q _ _) x y

/-- **The corrected hCbnd producer in the exact shape of the lane's repaired
interface**: the intrinsic bound at the block weights and the atlas mark maps,
which is the field hCbnd_intrinsic of PopDataIntrinsic. -/
theorem hCbnd_intrinsic_blockW_of_hkin_bound
    {M Am Cm : Type*} (q m : ℕ) (hm : 0 < m)
    (kin : (Fin q → Fin m) → Am → Cm → (Fin q → ℝ) → ℝ) {Cb : ℝ} (hCb0 : 0 ≤ Cb)
    (hkin : ∀ (c : Fin q → Fin m) (a : Am) (b : Cm) (v : Fin q → ℝ),
      |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (coordS : M → Fin q → ℝ) (labelS : M → Am)
    (coordT : M → Fin q → ℝ) (labelT : M → Cm) :
    ∀ (n : ℕ) (c : Fin q → Fin m) (x y : M),
      |markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤
        Cb * (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) * (q : ℝ) :=
  hCbnd_intrinsic_of_hkin_bound (Cb := Cb) (Xs := M) (Yt := M) (A := Am) (B := Cm)
    hCb0 (blockW q m hm) kin (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
    hkin

/-! ## 4. The uniform hCbnd is FALSE -/

/-- The absolute value of the frozen kernel is the product of the per-pair
kinetic absolute value and the intrinsic scale r ^ (2/q). -/
theorem markedKineticKernel_abs_eq {Xs Yt A B : Type*} {q : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (x : Xs) (y : Yt) :
    |markedKineticKernel (q := q) r kin markS markT x y| =
      |kin (markS x).2 (markT y).2 (mDisplacement (markS x).1 (markT y).1)| *
        r ^ (2 / (q : ℝ)) := by
  rw [markedKineticKernel_eq_scale_mul (q := q) r kin markS markT x y, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hr _)]
  exact mul_comm _ _

/-- **No uniform constant bound exists** at a growing block-count radius, for any
nonvanishing kinetic value on the marked atlas image.  Hence the localization
theorem's uniform hCbnd is false for the lane. -/
theorem not_uniform_markedKineticKernel_bound
    {Xs Yt A B : Type*} {q : ℕ} (hq : 0 < q) {ι : Type*}
    (w : ι → unitInterval) (c₀ : ι) (hw : 0 < (w c₀ : ℝ))
    (kin : ι → A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (x₀ : Xs) (y₀ : Yt)
    (hne : kin c₀ (markS x₀).2 (markT y₀).2
      (mDisplacement (markS x₀).1 (markT y₀).1) ≠ 0) :
    ¬ ∃ Cbnd : ℝ, ∀ (n : ℕ) (c : ι) (x : Xs) (y : Yt),
      |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c) markS markT x y| ≤
        Cbnd := by
  rintro ⟨Cbnd, hb⟩
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hexp : (0 : ℝ) < 2 / (q : ℝ) := div_pos (by norm_num) hq'
  have hk0 : 0 < |kin c₀ (markS x₀).2 (markT y₀).2
      (mDisplacement (markS x₀).1 (markT y₀).1)| := abs_pos.2 hne
  obtain ⟨R, hR⟩ := tendsto_atTop_atTop.1 (tendsto_rpow_atTop hexp)
    (Cbnd / |kin c₀ (markS x₀).2 (markT y₀).2
      (mDisplacement (markS x₀).1 (markT y₀).1)| + 1)
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1
    (frozenMarkedRadius_tendsto_atTop w c₀ hw) R
  have hrN : R ≤ frozenMarkedRadius w N c₀ := hN N le_rfl
  have hpow := hR (frozenMarkedRadius w N c₀) hrN
  have hbound := hb N c₀ x₀ y₀
  have habs : |markedKineticKernel (q := q) (frozenMarkedRadius w N c₀) (kin c₀)
      markS markT x₀ y₀| =
      |kin c₀ (markS x₀).2 (markT y₀).2
        (mDisplacement (markS x₀).1 (markT y₀).1)| *
        (frozenMarkedRadius w N c₀) ^ (2 / (q : ℝ)) :=
    markedKineticKernel_abs_eq (Nat.cast_nonneg _) (kin c₀) markS markT x₀ y₀
  rw [habs] at hbound
  have hlt : Cbnd < |kin c₀ (markS x₀).2 (markT y₀).2
      (mDisplacement (markS x₀).1 (markT y₀).1)| *
        (frozenMarkedRadius w N c₀) ^ (2 / (q : ℝ)) := by
    have hdiv : Cbnd / |kin c₀ (markS x₀).2 (markT y₀).2
        (mDisplacement (markS x₀).1 (markT y₀).1)| <
        (frozenMarkedRadius w N c₀) ^ (2 / (q : ℝ)) := by linarith
    have h2 : Cbnd < (frozenMarkedRadius w N c₀) ^ (2 / (q : ℝ)) *
        |kin c₀ (markS x₀).2 (markT y₀).2
          (mDisplacement (markS x₀).1 (markT y₀).1)| :=
      (div_lt_iff₀ hk0).1 hdiv
    calc Cbnd < (frozenMarkedRadius w N c₀) ^ (2 / (q : ℝ)) *
          |kin c₀ (markS x₀).2 (markT y₀).2
            (mDisplacement (markS x₀).1 (markT y₀).1)| := h2
      _ = |kin c₀ (markS x₀).2 (markT y₀).2
            (mDisplacement (markS x₀).1 (markT y₀).1)| *
            (frozenMarkedRadius w N c₀) ^ (2 / (q : ℝ)) := mul_comm _ _
  linarith

/-- **The localization theorem's uniform hCbnd is false for the upper lane**, in
the exact shape of the hypothesis at
FinslerOriginalIIDPressureUpperLocalization.lean:239. -/
theorem not_uniform_frozen_bound_blockW
    {M : Type*} (q m : ℕ) (hq : 0 < q) (hm : 0 < m) {Am Cm : Type*}
    (kin : (Fin q → Fin m) → Am → Cm → (Fin q → ℝ) → ℝ)
    (coordS : M → Fin q → ℝ) (labelS : M → Am)
    (coordT : M → Fin q → ℝ) (labelT : M → Cm)
    (hne : ∃ (c : Fin q → Fin m) (x y : M),
      kin c (labelS x) (labelT y) (mDisplacement (coordS x) (coordT y)) ≠ 0) :
    ¬ ∃ Cbnd : ℝ, ∀ (n : ℕ) (c : Fin q → Fin m) (x y : M),
      |markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Cbnd := by
  obtain ⟨c₀, x₀, y₀, hne'⟩ := hne
  refine not_uniform_markedKineticKernel_bound (q := q) hq (blockW q m hm) c₀ ?_
    kin (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x₀ y₀ ?_
  · rw [show ((blockW q m hm c₀ : unitInterval) : ℝ) = 1 / ((m ^ q : ℕ) : ℝ) from rfl]
    exact div_pos one_pos (by exact_mod_cast pow_pos hm q)
  · simpa [atlasMarkMap] using hne'

/-- The cell-boundedness r ^ (2/q) <= 1 that converts the repaired intrinsic
interface back to the original PopData (popData_of_intrinsic's hr) is false for
the lane at large n. -/
theorem cellBoundedness_false (q m : ℕ) (hq : 0 < q) (hm : 0 < m) :
    ¬ ∀ (n : ℕ) (c : Fin q → Fin m),
      (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) ≤ 1 := by
  intro h
  have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hexp : (0 : ℝ) < 2 / (q : ℝ) := div_pos (by norm_num) hq'
  let c₀ : Fin q → Fin m := fun _ => ⟨0, hm⟩
  obtain ⟨R, hR⟩ := tendsto_atTop_atTop.1 (tendsto_rpow_atTop hexp) 2
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1
    (frozenMarkedRadius_blockW_tendsto_atTop q m hm c₀) R
  have h2 : (2 : ℝ) ≤ (frozenMarkedRadius (blockW q m hm) N c₀) ^ (2 / (q : ℝ)) :=
    hR _ (hN N le_rfl)
  have h1 := h N c₀
  linarith

end OTSelector.Reconstruction
