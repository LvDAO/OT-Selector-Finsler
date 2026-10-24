import OTSelector.Probability.FinslerTileBlockLawComparison
import OTSelector.Probability.MarkedPoissonCube
import OTSelector.Limit.FinslerFrozenBlockBridge
import OTSelector.Reconstruction.FinslerOriginalWeightedUpperLocalizationRestated

/-!
# F13 resolution: the frozen bound is a block-count scale, not a cell radius

## The repo definitions (verbatim)

* 'frozenMarkedRadius w n c' (FinslerFrozenBlockBridge.lean:345) is
  |Nat.floor (((n + 1 : Nat) : Real) * (w c : Real))| as a real number.  With the
  block weight |w c = 1 / m^q| of the upper localization lane this is
  |floor ((n + 1) / m^q)|: a **block count** (number of marks in the block of
  scale n), growing linearly in n -- not a bounded cell radius.  This is proved
  below as |frozenMarkedRadius_blockW|.
* 'markedKineticKernel r kin markS markT x y' (FinslerTileBlockLawComparison.lean:370)
  is |r ^ (2 / q) * kin (markS x).2 (markT y).2 (mDisplacement ...)|, i.e. the
  intrinsic marked cost of the frozen block at radius scale |r|.

So the audit's intrinsic bound |r ^ (2 / q) * Cb * q| is the cost of a block with
~|r| marks: its n-dependence is |((n + 1) / m^q) ^ (2 / q)|, i.e. proportional to
|n ^ (2 / q)| -- exactly the paper's normalization.  main.tex:134 writes the
pressure functional with the factor |n ^ (2 / q)|:
|n^{2/q} * integral e d gamma + t * integral f d gamma|, and main.tex:1405 writes
the scaled cost |n^{2/q} (d_F(X_i, Y_j) - u(Y_j) + u(X_i))|.  Hence the paper's
localization computation carries the |n ^ (2 / q)| growth: the paper's bound is
the intrinsic one, and the uniform-in-n |hCbnd| of the repo localization theorem
is the over-strong (transcription) hypothesis, not the paper's formula.

## Reconciliation proved here

1. |frozenMarkedRadius_blockW|: the frozen radius is the block count
   |floor ((n + 1) / m^q)|, growing with n.
2. |markedKineticKernel_abs_le_intrinsic|: from the repo's per-pair bound
   |kin a b v| <= Cb * sum_l v_l^2| and the bounded mark displacement
   |sum_l (mDisplacement ...)_l^2 <= q| (marks are truncated to the unit cube),
   the intrinsic bound |r^(2/q) * Cb * q| follows.
3. |markedKineticKernel_abs_le_uniform|: the uniform constant bound |Cb * q| is
   equivalent to the *bounded-radius* special case |r ^ (2/q) <= 1|, which fails
   for the growing block count |floor ((n + 1) / m^q)|.
4. |IntrinsicFrozenBound|: the exact paper-faithful replacement of the
   localization theorem's |hCbnd| hypothesis, isolated as a named Prop; and
   |intrinsicFrozenBound_of_hkin_bound| derives it from (2).

No 'sorry', 'admit' or added axiom occurs.
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

/-! ## 1. The frozen radius is the block count -/

/-- **The frozen marked radius at block weight |1 / m^q| is the block count
|floor ((n + 1) / m^q)|.**  This is the quantity that the intrinsic bound
|r ^ (2 / q) * Cb * q| is evaluated at; it grows linearly in n, so it is a block
count, not a bounded cell radius. -/
theorem frozenMarkedRadius_blockW (q m : ℕ) (hm : 0 < m) (n : ℕ)
    (c : Fin q → Fin m) :
    frozenMarkedRadius (blockW q m hm) n c =
      (Nat.floor (((n + 1 : ℕ) : ℝ) / ((m ^ q : ℕ) : ℝ)) : ℝ) := by
  unfold frozenMarkedRadius
  congr 1
  rw [show ((blockW q m hm c : unitInterval) : ℝ) = 1 / ((m ^ q : ℕ) : ℝ) from rfl]
  ring

/-! ## 2. The intrinsic bound from the per-pair bound -/

/-- **The intrinsic marked-kernel bound.**  If the per-pair kinetic is bounded by
|Cb * sum_l v_l^2| and the square marks of a frozen pair are bounded by |q| (the
marks live in the truncated unit cube), then the marked kinetic kernel obeys the
intrinsic bound |r ^ (2 / q) * Cb * q|. -/
theorem markedKineticKernel_abs_le_intrinsic
    {Xs Yt A B : Type*} {q : ℕ} {Cb r : ℝ} (hCb : 0 ≤ Cb) (hr : 0 ≤ r)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (hkin : ∀ (a : A) (b : B) (v : Fin q → ℝ), |kin a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hdisp : ∀ (x : Xs) (y : Yt),
      ∑ l, mDisplacement (markS x).1 (markT y).1 l ^ 2 ≤ (q : ℝ))
    (x : Xs) (y : Yt) :
    |markedKineticKernel (q := q) r kin markS markT x y| ≤
      Cb * r ^ (2 / (q : ℝ)) * (q : ℝ) := by
  have hrp : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
  have hk := hkin (markS x).2 (markT y).2
    (mDisplacement (markS x).1 (markT y).1)
  have hd := hdisp x y
  simp only [markedKineticKernel]
  rw [abs_mul, abs_of_nonneg hrp]
  calc
    r ^ (2 / (q : ℝ)) *
        |kin (markS x).2 (markT y).2 (mDisplacement (markS x).1 (markT y).1)|
        ≤ r ^ (2 / (q : ℝ)) *
            (Cb * ∑ l, mDisplacement (markS x).1 (markT y).1 l ^ 2) :=
          mul_le_mul_of_nonneg_left hk hrp
    _ = Cb * r ^ (2 / (q : ℝ)) *
          (∑ l, mDisplacement (markS x).1 (markT y).1 l ^ 2) := by ring
    _ ≤ Cb * r ^ (2 / (q : ℝ)) * (q : ℝ) :=
          mul_le_mul_of_nonneg_left hd (mul_nonneg hCb hrp)

/-- **The uniform constant bound is exactly the bounded-radius case.**  The
uniform bound |Cb * q| asked for by the localization theorem's |hCbnd| follows
from the intrinsic bound precisely when the radius scale is bounded,
|r ^ (2 / q) ≤ 1|.  For the lane's block count |r = floor ((n + 1) / m^q)| this
boundedness fails for large n. -/
theorem markedKineticKernel_abs_le_uniform
    {Xs Yt A B : Type*} {q : ℕ} {Cb r : ℝ} (hCb : 0 ≤ Cb) (hr : 0 ≤ r)
    (hr1 : r ^ (2 / (q : ℝ)) ≤ 1)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (hkin : ∀ (a : A) (b : B) (v : Fin q → ℝ), |kin a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hdisp : ∀ (x : Xs) (y : Yt),
      ∑ l, mDisplacement (markS x).1 (markT y).1 l ^ 2 ≤ (q : ℝ))
    (x : Xs) (y : Yt) :
    |markedKineticKernel (q := q) r kin markS markT x y| ≤ Cb * (q : ℝ) := by
  have h := markedKineticKernel_abs_le_intrinsic hCb hr kin markS markT hkin hdisp x y
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  calc
    |markedKineticKernel (q := q) r kin markS markT x y|
        ≤ Cb * r ^ (2 / (q : ℝ)) * (q : ℝ) := h
    _ ≤ Cb * 1 * (q : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr1 hCb) hq0
    _ = Cb * (q : ℝ) := by ring

/-! ## 3. The paper-faithful replacement of the localization hypothesis -/

/-- **The intrinsic frozen bound (the paper-faithful replacement of |hCbnd|).**
The localization theorem's uniform-in-n hypothesis |hCbnd| must be replaced by
this intrinsic form: for every pair of probes and every radius scale |R x y|, the
marked kinetic kernel is bounded by |Cb * (R x y) ^ (2 / q) * q|.  In the upper
localization lane the radius is |R n c = frozenMarkedRadius (blockW q m hm) n c|,
which by |frozenMarkedRadius_blockW| equals the block count
|floor ((n + 1) / m^q)|. -/
def IntrinsicFrozenBound {Xs Yt A B : Type*} (q : ℕ) (Cb : ℝ)
    (R : Xs → Yt → ℝ) (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B) : Prop :=
  ∀ (x : Xs) (y : Yt),
    |markedKineticKernel (q := q) (R x y) kin markS markT x y| ≤
      Cb * (R x y) ^ (2 / (q : ℝ)) * (q : ℝ)

/-- **The intrinsic frozen bound is derivable from the repo's per-pair bound and
cell-boundedness** (marks in the truncated unit cube give
|sum_l (mDisplacement)_l^2 <= q|), with nonnegative radius scales. -/
theorem intrinsicFrozenBound_of_hkin_bound
    {Xs Yt A B : Type*} {q : ℕ} {Cb : ℝ} (hCb : 0 ≤ Cb)
    (R : Xs → Yt → ℝ) (hR0 : ∀ (x : Xs) (y : Yt), 0 ≤ R x y)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (hkin : ∀ (a : A) (b : B) (v : Fin q → ℝ), |kin a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hdisp : ∀ (x : Xs) (y : Yt),
      ∑ l, mDisplacement (markS x).1 (markT y).1 l ^ 2 ≤ (q : ℝ)) :
    IntrinsicFrozenBound (q := q) Cb R kin markS markT :=
  fun x y => markedKineticKernel_abs_le_intrinsic hCb (hR0 x y) kin markS markT
    hkin hdisp x y

end OTSelector.Reconstruction
