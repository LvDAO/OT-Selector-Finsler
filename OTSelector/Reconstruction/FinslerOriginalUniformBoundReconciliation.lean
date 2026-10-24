import OTSelector.Probability.MarkedPressureLimit
import OTSelector.Reconstruction.FinslerOriginalF13Resolution

/-!
# F13 round 2: the repo's hCbnd is on the raw kernel, the pressures are normalized

## What the upper localization theorem assumes (verbatim)

From |FinslerOriginalIIDPressureUpperLocalization.lean| (the theorem
|finsler_originalIID_pressure_upper_localization|):

|{Cbnd Gbnd : R} (hCbnd0 : 0 <= Cbnd) (hGbnd0 : 0 <= Gbnd)
 (hCbnd : forall (n : Nat) (c : iota) (x y : M),
   |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| <= Cbnd)|

i.e. a **uniform-in-n constant bound on the raw frozen kernel**
|markedKineticKernel r kin markS markT x y = r ^ (2 / q) * kin ...| evaluated at
the radius |frozenMarkedRadius w n c| (FinslerFrozenBlockBridge.lean:345)

|frozenMarkedRadius w n c = (Nat.floor (((n + 1 : Nat) : R) * (w c : R)) : R)|.

For the upper lane |w c = 1 / m^q| this is the *block count*
|floor ((n + 1) / m^q)| (proved in |FinslerOriginalF13Resolution|), which grows
linearly in n.

## The pressures it bounds are normalized

* |markedScalePressure q A B alpha beta kin g R t| (MarkedPressureLimit.lean:25)
  is |if 0 < R then markedPressure q A B alpha beta (Real.toNNReal (R ^ q)) kin g t
  / R ^ q else 0|: the marked pressure of a cloud of intensity |R ^ q|, divided by
  the intensity scale |R ^ q| (normalized per unit scale).
* The physical pressure |finslerSupportedPressure| is
  |supportedDistancePressure| (SupportedEmpiricalSelector.lean:28), which scales
  the edge cost by |k| and divides by |n|:
  |perturbedAssignmentValue (fun i j => k * distanceSlackEdgeCost X Y phi i j) ...
  t / (n : R)|.  The localization theorem's own docstring states that the
  conclusion is the upper pressure bound "at the paper scale |(n+1)^(2/(d-1))|"
  (FinslerOriginalIIDPressureUpperLocalization.lean, section 5).

* main.tex:134: the pressure functional is
  |n^{2/q} * integral e d gamma + t * integral f d gamma|; main.tex:1405: the
  scaled cost is |n^{2/q} (d_F(X_i, Y_j) - u(Y_j) + u(X_i))|.  Hence the paper's
  scale factor |n^{2/q}| is exactly the normalization carried by both pressure
  functionals here.

## Verdict

**F13 is real: the uniform |hCbnd| is over-strong.**  It bounds the *raw*
(un-normalized) frozen kernel |r ^ (2/q) * kin| at a block count |r| that grows
with n, while every quantity the theorem actually estimates is normalized by the
scale (|/ R ^ q| for the marked pressure, |x k| with |k = (n+1)^(2/(d-1))| and
|/ n| for the physical one).  The paper-faithful hypothesis is the
scale-normalized one, |IntrinsicFrozenBound| (FinslerOriginalF13Resolution.lean):
|markedKineticKernel r ...| <= |Cb * r ^ (2/q) * q|.  The uniform |hCbnd| is
equivalent to its bounded-scale special case |r ^ (2/q) <= 1| (the reconciliation
lemmas of FinslerOriginalF13Resolution.lean), which fails for the growing block
count.  The repair is therefore to restate the localization theorem consuming
|IntrinsicFrozenBound|; the previous module |FinslerOriginalPopDataIntrinsicBound|
already provides that restated consumer (|PopDataIntrinsic| and
|physicalWeightedLocalizationFamily_of_popDataIntrinsic|).

## Bridge proved here

1. |markedScalePressure_normalized|: the marked pressure is the intensity-scale
   normalized pressure (the normalization identity).
2. |normalizedKernelBound_of_hkin|: the repo's per-pair bound together with the
   truncated unit-cube mark bound gives the *normalized* per-pair kernel bound
   |kin ... <= Cb * q| (this is the scale-free content of the paper's bound).
3. |intrinsicFrozenBound_of_normalizedKernelBound|: the normalized per-pair bound
   gives |IntrinsicFrozenBound| at every nonnegative scale |R| -- the exact
   hypothesis the restated localization theorem consumes.
4. |uniform_bound_imp_scaled_kin_bound|: conversely the uniform raw |hCbnd| forces
   the scaled per-pair kernel to decay like |r ^ (-2/q)|, which the constant
   per-pair bound does not; this is the precise sense in which |hCbnd| is
   over-strong.

No 'sorry', 'admit' or added axiom occurs.
-/

open Set Function Filter MeasureTheory
open OTSelector.Probability
open scoped Topology ENNReal NNReal

noncomputable section

namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. The normalization identity of the marked pressure -/

/-- **The marked scale pressure is the intensity-normalized pressure**: for a
positive scale |R| it is the marked pressure of the cloud of intensity |R ^ q|,
divided by |R ^ q|.  This is the normalization identity that makes the frozen
bound a normalized (scale-free) quantity in the paper. -/
theorem markedScalePressure_normalized (q : ℕ) (A B : Type*) [MeasurableSpace A]
    [MeasurableSpace B] (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) {R t : ℝ} (hR : 0 < R) :
    markedScalePressure q A B α β kin g R t =
      markedPressure q A B α β (Real.toNNReal (R ^ q)) kin g t / R ^ q := by
  unfold markedScalePressure
  split_ifs
  · rfl

/-! ## 2. The frozen kernel is the raw scaled kernel -/

/-- The frozen marked kernel is the raw product of the scale factor |r ^ (2 / q)|
with the per-pair kinetic at the marked displacement; it carries no division by
the scale. -/
theorem markedKineticKernel_eq_scale_mul {Xs Yt A B : Type*} {q : ℕ} (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (x : Xs) (y : Yt) :
    markedKineticKernel (q := q) r kin markS markT x y =
      r ^ (2 / (q : ℝ)) *
        kin (markS x).2 (markT y).2
          (mDisplacement (markS x).1 (markT y).1) := rfl

/-! ## 3. The normalized per-pair kernel bound -/

/-- **The scale-free content of the paper's frozen bound**: the repo's per-pair
bound |kin a b v <= Cb * sum_l v_l^2| together with the truncated unit-cube mark
bound |sum_l (mDisplacement ...)_l^2 <= q| gives the *normalized* (scale-free)
per-pair bound |kin ... <= Cb * q|. -/
theorem normalizedKernelBound_of_hkin
    {Xs Yt A B : Type*} {q : ℕ} {Cb : ℝ} (hCb : 0 ≤ Cb)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (hkin : ∀ (a : A) (b : B) (v : Fin q → ℝ), |kin a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hdisp : ∀ (x : Xs) (y : Yt),
      ∑ l, mDisplacement (markS x).1 (markT y).1 l ^ 2 ≤ (q : ℝ))
    (x : Xs) (y : Yt) :
    |kin (markS x).2 (markT y).2
        (mDisplacement (markS x).1 (markT y).1)| ≤ Cb * (q : ℝ) := by
  have hk := hkin (markS x).2 (markT y).2
    (mDisplacement (markS x).1 (markT y).1)
  have hd := hdisp x y
  exact le_trans hk (mul_le_mul_of_nonneg_left hd hCb)

/-! ## 4. The bridge: normalized per-pair bound gives IntrinsicFrozenBound -/

/-- **Bridge lemma.**  The normalized per-pair bound gives the
|IntrinsicFrozenBound| at every nonnegative scale |R| -- exactly the
scale-normalized frozen hypothesis that the restated localization theorem
consumes (FinslerOriginalF13Resolution.lean). -/
theorem intrinsicFrozenBound_of_normalizedKernelBound
    {Xs Yt A B : Type*} {q : ℕ} {Cb : ℝ} (hCb : 0 ≤ Cb)
    (R : Xs → Yt → ℝ) (hR0 : ∀ (x : Xs) (y : Yt), 0 ≤ R x y)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (hkin : ∀ (a : A) (b : B) (v : Fin q → ℝ), |kin a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hdisp : ∀ (x : Xs) (y : Yt),
      ∑ l, mDisplacement (markS x).1 (markT y).1 l ^ 2 ≤ (q : ℝ)) :
    IntrinsicFrozenBound (q := q) Cb R kin markS markT := by
  intro x y
  have hn := normalizedKernelBound_of_hkin hCb kin markS markT hkin hdisp x y
  have hrp : 0 ≤ R x y ^ (2 / (q : ℝ)) := Real.rpow_nonneg (hR0 x y) _
  simp only [markedKineticKernel, abs_mul, abs_of_nonneg hrp]
  calc
    R x y ^ (2 / (q : ℝ)) *
        |kin (markS x).2 (markT y).2
          (mDisplacement (markS x).1 (markT y).1)|
        ≤ R x y ^ (2 / (q : ℝ)) * (Cb * (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hn hrp
    _ = Cb * R x y ^ (2 / (q : ℝ)) * (q : ℝ) := by ring

/-! ## 5. The uniform raw bound forces the scaled per-pair decay -/

/-- **The precise over-strength of |hCbnd|.**  A uniform constant bound on the
raw frozen kernel at scale |r > 0| forces the per-pair kernel, multiplied by the
scale |r ^ (2 / q)|, to be bounded by the same constant: the per-pair kinetic is
then forced to decay like |r ^ (-2/q)|, which the paper's scale-free per-pair
bound |kin <= Cb * q| does not.  This is why the uniform-in-n |hCbnd| cannot be
the paper's normalized bound: on the upper lane |r| is the block count
|floor ((n + 1) / m^q)| and grows with n. -/
theorem uniform_bound_imp_scaled_kin_bound
    {Xs Yt A B : Type*} {q : ℕ} {Cbnd r : ℝ} (hr : 0 < r)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (h : ∀ (x : Xs) (y : Yt),
      |markedKineticKernel (q := q) r kin markS markT x y| ≤ Cbnd) :
    ∀ (x : Xs) (y : Yt),
      |kin (markS x).2 (markT y).2
          (mDisplacement (markS x).1 (markT y).1)| *
        r ^ (2 / (q : ℝ)) ≤ Cbnd := by
  intro x y
  have hrp : 0 ≤ r ^ (2 / (q : ℝ)) := le_of_lt (Real.rpow_pos_of_pos hr _)
  have hxy := h x y
  simp only [markedKineticKernel, abs_mul, abs_of_nonneg hrp] at hxy
  calc
    |kin (markS x).2 (markT y).2
        (mDisplacement (markS x).1 (markT y).1)| * r ^ (2 / (q : ℝ)) =
        r ^ (2 / (q : ℝ)) *
          |kin (markS x).2 (markT y).2
            (mDisplacement (markS x).1 (markT y).1)| := by ring
    _ ≤ Cbnd := hxy

end OTSelector.Reconstruction
