import OTSelector.Reconstruction.FinslerOriginalLocalizationIntrinsic

/-!
# The frozen estimate at the paper's normalization scale (F13, frozen-estimate level)

## What the frozen estimate consumes

In the repo's upper localization theorem the frozen bound |hCbnd| is a **uniform
constant bound on the raw kernel** (FinslerOriginalIIDPressureUpperLocalization.lean,
lines 237-240, forwarded at 301, 432, 579):

|hCbnd : forall (n : Nat) (c : iota) (x y : M),
  |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
     (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| <= Cbnd|

with |markedKineticKernel r kin markS markT x y = r ^ (2 / q) * kin (...)| and
|frozenMarkedRadius w n c| the block count (FinslerFrozenBlockBridge.lean:345).

## Which side the paper normalizes

The paper normalizes on the **pressure (intensity) side**: the marked pressure used
in the localization hypothesis is (FinslerOriginalMarkedPressureLimit.lean:25)

|markedScalePressure q A B alpha beta kin g R t =
  markedPressure q A B alpha beta (Real.toNNReal (R ^ q)) kin g t / R ^ q|

i.e. the marked pressure of the cloud of intensity |R ^ q|, **divided by the
intensity scale |R ^ q|**.  On the physical side the cost carries the paper's
scale factor: |supportedDistancePressure| multiplies the edge cost by |k| and
divides by |n| (SupportedEmpiricalSelector.lean:28), and the localization
conclusion is at the paper scale |(n+1)^(2/(d-1))|
(FinslerOriginalIIDPressureUpperLocalization.lean, section 5).  main.tex:134
writes the pressure functional with |n^{2/q} integral e d gamma + t integral f
d gamma| and main.tex:1405 the scaled cost |n^{2/q}(d_F(X_i,Y_j)-u(Y_j)+u(X_i))|,
so the paper's normalization factor is the same scale, with |R^{2/q}| on the cost
and |R^q| on the intensity.

## The normalized estimate (proved below)

The raw kernel obeys the intrinsic bound (FinslerOriginalF13Resolution.lean)

|markedKineticKernel r ... <= Cb * r ^ (2/q) * q|.

Dividing by the intensity scale |R ^ q| with |R| equal to the same block radius
|r| gives the **normalized** kernel bound

|markedKineticKernel r ... / r ^ q <= Cb * q * (r ^ (2/q - q)) <= Cb * q|

for |r >= 1| and |q >= 2| (the paper's |q = d - 1 >= 5|).  So after the paper's
normalization the bound IS uniform in n, **with no cell-boundedness assumption**:
|hcell| (|r ^ (2/q) <= 1|) is an artifact of the repo's unnormalized raw
interface, not of the paper's estimate.  This is proved as
|normalizedKernelBound_of_intrinsicBound|.

## Residual input

The repo's frozen estimate still consumes the **raw** kernel, so the consumer
theorem below keeps |hcell| as its precise residual input; replacing it by the
normalized estimate requires restating the frozen-estimate core to consume the
intensity-normalized kernel (the named input |NormalizedFrozenEstimate| below
records exactly that statement).  No 'sorry', 'admit' or added axiom occurs.
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

/-- **The normalized frozen-kernel bound.**  If the raw frozen kernel obeys the
intrinsic bound |Cb * r ^ (2/q) * q| and the paper's pressure normalization divides
by the intensity scale |R ^ q| with |R| the same block radius |r >= 1|, then the
normalized kernel is bounded by the constant |Cb * q|, uniformly in |r|.  No
cell-boundedness (|r ^ (2/q) <= 1|) is needed: the normalization moves the growth
from the kernel into the (harmless) factor |r ^ (2/q - q) <= 1| for |q >= 2|. -/
theorem normalizedKernelBound_of_intrinsicBound
    {Xs Yt A B : Type*} {q : ℕ} {Cb r : ℝ} (hCb : 0 ≤ Cb) (hr : 1 ≤ r) (hq : 2 ≤ q)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (h : ∀ (x : Xs) (y : Yt),
      |markedKineticKernel (q := q) r kin markS markT x y| ≤
        Cb * r ^ (2 / (q : ℝ)) * (q : ℝ)) :
    ∀ (x : Xs) (y : Yt),
      |markedKineticKernel (q := q) r kin markS markT x y| / r ^ (q : ℝ) ≤
        Cb * (q : ℝ) := by
  intro x y
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hrq : 0 < r ^ (q : ℝ) := Real.rpow_pos_of_pos hr0 _
  have hrp : 0 < r ^ (2 / (q : ℝ)) := Real.rpow_pos_of_pos hr0 _
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hexp : 2 / (q : ℝ) ≤ (q : ℝ) := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (q : ℝ))]
    nlinarith
  have hrpow_le : r ^ (2 / (q : ℝ)) ≤ r ^ (q : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hr hexp
  have habs : |markedKineticKernel (q := q) r kin markS markT x y| =
      r ^ (2 / (q : ℝ)) *
        |kin (markS x).2 (markT y).2
          (mDisplacement (markS x).1 (markT y).1)| := by
    simp only [markedKineticKernel, abs_mul, abs_of_nonneg (Real.rpow_nonneg hr0.le _)]
  have hkin : |kin (markS x).2 (markT y).2
        (mDisplacement (markS x).1 (markT y).1)| ≤ Cb * (q : ℝ) := by
    have h2 := h x y
    rw [habs] at h2
    have h2' : r ^ (2 / (q : ℝ)) *
          |kin (markS x).2 (markT y).2
            (mDisplacement (markS x).1 (markT y).1)| ≤
        r ^ (2 / (q : ℝ)) * (Cb * (q : ℝ)) := by
      calc
        r ^ (2 / (q : ℝ)) *
            |kin (markS x).2 (markT y).2
              (mDisplacement (markS x).1 (markT y).1)|
            ≤ Cb * r ^ (2 / (q : ℝ)) * (q : ℝ) := h2
        _ = r ^ (2 / (q : ℝ)) * (Cb * (q : ℝ)) := by ring
    nlinarith [h2, hrp]
  rw [habs, div_le_iff₀ hrq]
  calc
    r ^ (2 / (q : ℝ)) *
        |kin (markS x).2 (markT y).2
          (mDisplacement (markS x).1 (markT y).1)|
        ≤ r ^ (2 / (q : ℝ)) * (Cb * (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hkin (Real.rpow_nonneg hr0.le _)
    _ ≤ r ^ (q : ℝ) * (Cb * (q : ℝ)) :=
          mul_le_mul_of_nonneg_right hrpow_le (mul_nonneg hCb hq0)
    _ = Cb * (q : ℝ) * r ^ (q : ℝ) := by ring

/-- **The named residual input for dropping |hcell| entirely.**  The repo's
frozen estimate consumes the raw kernel bound; the paper's estimate is uniform
only after dividing by the intensity scale |R ^ q|.  This predicate records the
restated frozen-estimate core that consumes the intensity-normalized kernel
(|R| the frozen block radius), which by
|normalizedKernelBound_of_intrinsicBound| is satisfied with the uniform constant
|Cb * q| without any cell-boundedness. -/
def NormalizedFrozenEstimate {Xs Yt A B : Type*} (q : ℕ) (Cb : ℝ)
    (R : Xs → Yt → ℝ) (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B) : Prop :=
  ∀ (x : Xs) (y : Yt),
    |markedKineticKernel (q := q) (R x y) kin markS markT x y| / R x y ^ (q : ℝ) ≤
      Cb * (q : ℝ)

/-! ## 2. The family theorem with the precise residual input -/

/-- **The upper localization family under the intrinsic frozen bound, named form.**
Same conclusion and telescope as
|physicalWeightedLocalizationFamily_of_intrinsicBound|; the residual input is
|hcell|, which the normalized estimate shows is needed only because the repo's
frozen estimate consumes the raw (unnormalized) kernel. -/
theorem physicalWeightedLocalizationFamily_of_intrinsicNormalized
    (F : ContinuousFinslerNorm E M) (φ : M → ℝ)
    (hφ : let _instIIDPotentialMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 φ)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ n j, (P n).map (Y n j) = ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (q m : ℕ) (hm : 0 < m) (radius : FinalRadiusField A B)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (hcell : ∀ (n : ℕ) (c : Fin q → Fin m),
      (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) ≤ 1)
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      PopDataIntrinsic F φ q m hm ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hsmall : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < radius f),
      ∀ (n : ℕ), n < m ^ q - 1 → ∀ (c : Fin q → Fin m)
        (ξ : canonicalOmega M n) (i j : Fin (n + 1)),
      (data f t hpert).cellS (canonicalX (M := M) n i ξ) = c →
      (data f t hpert).cellT (canonicalY (M := M) n j ξ) = c →
      |finslerTileKinetic F (fun i => canonicalX (M := M) n i ξ)
          (fun j => canonicalY (M := M) n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j -
          markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c)
            ((data f t hpert).kin c)
            (atlasMarkMap (data f t hpert).coordS (data f t hpert).labelS)
            (atlasMarkMap (data f t hpert).coordT (data f t hpert).labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| ≤
        2 * (data f t hpert).ε n *
          markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c)
            ((data f t hpert).kin c)
            (atlasMarkMap (data f t hpert).coordS (data f t hpert).labelS)
            (atlasMarkMap (data f t hpert).coordT (data f t hpert).labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < radius f)
      (c : Fin q → Fin m), (data f t hpert).p c t = pc f t c) :
    PhysicalWeightedLocalizationFamily F
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
      hA hB hμA hνB P X Y φ
      (fun c : Fin q → Fin m => ((blockW q m hm c : unitInterval) : ℝ)) pc radius
:= 
  physicalWeightedLocalizationFamily_of_intrinsicBound (F := F) (φ := φ) (hφ := hφ)
    (hcomplete := hcomplete) (hdim := hdim) (ωM := ωM) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
    (hA := hA) (hB := hB) (hAB := hAB) (hμA := hμA) (hνB := hνB)
    (P := P) (X := X) (Y := Y) (hX := hX) (hY := hY) (hXi := hXi) (hYi := hYi)
    (hXlaw := hXlaw) (hYlaw := hYlaw) (hXY := hXY)
    (q := q) (m := m) (hm := hm) (radius := radius) (pc := pc)
    (hcell := hcell) (data := data) (hsmall := hsmall) (hpc := hpc)

end OTSelector.Reconstruction
