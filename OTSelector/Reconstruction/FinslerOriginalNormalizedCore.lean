import OTSelector.Reconstruction.FinslerOriginalFrozenEstimateScale

/-!
# F13 finished: the normalized frozen estimate with NO radius bound

## The result

The frozen estimate of the repo's upper localization theorem consumes the **raw**
kernel bound |hCbnd| (FinslerOriginalIIDPressureUpperLocalization.lean:237-240,
forwarded at 301, 432, 579).  The paper, however, normalizes by the intensity
scale |R ^ q|: |markedScalePressure = markedPressure (intensity R ^ q) / R ^ q|
(MarkedPressureLimit.lean:25), with the cost at the paper scale |(n+1)^(2/(d-1))|
(main.tex:134: |n^{2/q} integral e d gamma + t integral f d gamma|; main.tex:1405:
|n^{2/q}(d_F(X_i,Y_j) - u(Y_j) + u(X_i))|).

The frozen radius is an integer (|frozenMarkedRadius w n c = floor ((n+1) w c)|,
FinslerFrozenBlockBridge.lean:345).  Hence for the integer radius |k| there is **no
radius bound at all**:

* |k = 0|: the raw kernel vanishes and Lean's division by zero gives the estimate
  for free;
* |k >= 1|: |r ^ (2/q - q) <= 1| since |2/q <= q| for |q >= 2|,

so from the intrinsic bound |markedKineticKernel r ... <= Cb * r ^ (2/q) * q| the
intensity-normalized kernel obeys the uniform bound
|markedKineticKernel r ... / r ^ q <= Cb * q| for **every** |n| and |c|.

## Substitution at the three |hCbnd| uses

Each of the three occurrences (301, 432, 579) forwards the raw uniform bound to the
core frozen estimate; the core consumes it as a uniform constant bound.  The
normalized hypothesis |NormalizedFrozenEstimate| (FinslerOriginalFrozenEstimateScale)
is what the paper supplies, and |normalizedBound_of_rawBound| below shows the raw
bound implies the normalized one -- so replacing the raw hypothesis by the
normalized one is a *weakening* at the interface, exactly the substitution
performed at each use.  |normalizedFrozenKernelBound| puts the normalized bound
into the exact shape consumed by the estimate, with constant |Cb * q| and no radius
hypothesis.

The only residual input of the consumer chain is the small-|n| freezing estimate
|hsmall|; no |hcell| and no bounded-radius input is needed at the normalized
interface.

No 'sorry', 'admit' or added axiom occurs.
-/







open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction
  BigOperators

noncomputable section

set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-! ## 1. The intrinsic replacement of the uniform frozen-bound step -/

/-! ## 1. The paper's normalized estimate -/

/-! ## 1. The normalized frozen estimate, no radius bound -/

/-- **The normalized frozen-kernel bound with no radius bound.**  For an integer
radius |k| and |q >= 2|, the intrinsic frozen bound implies the intensity-normalized
bound |markedKineticKernel r ... / r ^ q <= Cb * q| for all marks.  No hypothesis on
|k| (no |r >= 1|, no cell bound, no boundedness) is needed: |k = 0| is the vanishing
raw kernel and |k >= 1| gives |r ^ (2/q - q) <= 1|. -/
theorem normalizedFrozenKernelBound
    {Xs Yt A B : Type*} {q : ℕ} {Cb : ℝ} (hCb : 0 ≤ Cb) (hq : 2 ≤ q)
    (k : ℕ) (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (h : ∀ (x : Xs) (y : Yt),
      |markedKineticKernel (q := q) ((k : ℕ) : ℝ) kin markS markT x y| ≤
        Cb * ((k : ℕ) : ℝ) ^ (2 / (q : ℝ)) * (q : ℝ)) :
    ∀ (x : Xs) (y : Yt),
      |markedKineticKernel (q := q) ((k : ℕ) : ℝ) kin markS markT x y| /
        ((k : ℕ) : ℝ) ^ (q : ℝ) ≤ Cb * (q : ℝ) := by
  intro x y
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hq)
    have hexp : (2 / (q : ℝ)) ≠ 0 := div_ne_zero (by norm_num) (ne_of_gt hq0)
    have hkern : |markedKineticKernel (q := q) ((0 : ℕ) : ℝ) kin markS markT x y| = 0 := by
      rw [Nat.cast_zero, markedKineticKernel, Real.zero_rpow hexp]
      simp
    have hden : ((0 : ℕ) : ℝ) ^ (q : ℝ) = 0 := by
      rw [Nat.cast_zero]
      exact Real.zero_rpow (ne_of_gt hq0)
    rw [hkern, hden, div_zero]
    exact mul_nonneg hCb (Nat.cast_nonneg q)
  · have hr : (1 : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk
    exact normalizedKernelBound_of_intrinsicBound hCb hr hq kin markS markT h x y

/-- **Lane form.**  The intensity-normalized frozen bound for the upper lane
(|w c = 1 / m^q|, frozen radius the block count), with **no radius hypothesis at
all**.  This is the exact statement to substitute for the raw |hCbnd| at each of
the three use sites of the localization theorem. -/
theorem normalizedFrozenBound_of_intrinsic
    {M E : Type*} [MetricSpace M] [NormedAddCommGroup E]
    (q m : ℕ) (hm : 0 < m) {Cb : ℝ} (hCb : 0 ≤ Cb) (hq : 2 ≤ q)
    {A B : Type*} (kin : (Fin q → Fin m) → A → B → (Fin q → ℝ) → ℝ)
    (markS : M → (Fin q → ℝ) × A) (markT : M → (Fin q → ℝ) × B)
    (h : ∀ (n : ℕ) (c : Fin q → Fin m) (x y : M),
      |markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (kin c)
        markS markT x y| ≤
        Cb * (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) * (q : ℝ)) :
    ∀ (n : ℕ) (c : Fin q → Fin m) (x y : M),
      |markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (kin c)
        markS markT x y| /
        (frozenMarkedRadius (blockW q m hm) n c) ^ (q : ℝ) ≤ Cb * (q : ℝ) := by
  intro n c x y
  simpa only [frozenMarkedRadius] using
    (normalizedFrozenKernelBound (q := q) (Cb := Cb) hCb hq
      (Nat.floor (((n + 1 : ℕ) : ℝ) * (blockW q m hm c : ℝ)))
      (kin c) markS markT (fun x y => h n c x y) x y)

/-! ## 2. The substitution lemma at each raw-bound use -/

/-- **Raw implies normalized.**  A uniform constant bound on the raw kernel at an
integer frozen radius implies the intensity-normalized bound at the same constant.
This is precisely the substitution available at each of the three |hCbnd| uses of
the localization theorem: the normalized hypothesis used there is *weaker* than the
raw one. -/
theorem normalizedBound_of_rawBound
    {Xs Yt A B : Type*} {q : ℕ} {Cbnd : ℝ} (hCbnd0 : 0 ≤ Cbnd) (hq : 2 ≤ q)
    (k : ℕ) (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (h : ∀ (x : Xs) (y : Yt),
      |markedKineticKernel (q := q) ((k : ℕ) : ℝ) kin markS markT x y| ≤ Cbnd) :
    ∀ (x : Xs) (y : Yt),
      |markedKineticKernel (q := q) ((k : ℕ) : ℝ) kin markS markT x y| /
        ((k : ℕ) : ℝ) ^ (q : ℝ) ≤ Cbnd := by
  intro x y
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hq)
    have hexp : (2 / (q : ℝ)) ≠ 0 := div_ne_zero (by norm_num) (ne_of_gt hq0)
    have hkern : |markedKineticKernel (q := q) ((0 : ℕ) : ℝ) kin markS markT x y| = 0 := by
      rw [Nat.cast_zero, markedKineticKernel, Real.zero_rpow hexp]
      simp
    have hden : ((0 : ℕ) : ℝ) ^ (q : ℝ) = 0 := by
      rw [Nat.cast_zero]
      exact Real.zero_rpow (ne_of_gt hq0)
    rw [hkern, hden, div_zero]
    exact hCbnd0
  · have hr : (1 : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk
    have hrq : 0 < ((k : ℕ) : ℝ) ^ (q : ℝ) :=
      Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hr) _
    have hrq1 : (1 : ℝ) ≤ ((k : ℕ) : ℝ) ^ (q : ℝ) :=
      Real.one_le_rpow hr (Nat.cast_nonneg q)
    rw [div_le_iff₀ hrq]
    calc
      |markedKineticKernel (q := q) ((k : ℕ) : ℝ) kin markS markT x y| ≤ Cbnd := h x y
      _ = Cbnd * 1 := by ring
      _ ≤ Cbnd * ((k : ℕ) : ℝ) ^ (q : ℝ) :=
            mul_le_mul_of_nonneg_left hrq1 hCbnd0

end OTSelector.Reconstruction
