import OTSelector.Reconstruction.FinslerOriginalHupperAssembly
import OTSelector.Reconstruction.FinslerSelectorFinalInputsWiringAudit

/-!
# Hupper lane wiring to the final-assembly consumer

This module wires the upper-pressure input 'hupper' of
'FinslerSelectorFinalInputs' (consumer shape 'FinalProbUpperData', defined in
'FinslerSelectorFinalInputsWiringAudit.lean') to the blockwise-stabilization
kernel-marked pressure lane.

## What is discharged (already proved in the lane)

* **hupper readout composition.**  'kernelScaleUpperData_of_twoRates' composes the
  matching-moment rate and the mark-modulus coupling rate with
  'QuantitativeBlockwiseStabilization' and the reference constant-kernel limit
  'href' into the named upper-readout predicate 'KernelScaleUpperData', citing
  'hupper_readout_of_matching_moment_and_mark_modulus'.
* **Constant-kernel case, unconditionally.**  'kernelScaleUpperData_const' derives
  'KernelScaleUpperData' at constant kernels from 'href' alone, citing
  'eventually_kernelMarkedScalePressure_le_const' (there the quantitative
  blockwise error vanishes identically: the block comparison/repair terms are
  exact, 'blockScalePressureError_const_eq_zero').
* **Block pressure limit identification.**  'kernelScaleUpperData_of_blockwiseLimit'
  derives 'KernelScaleUpperData' from the per-block limit family 'pc' and the
  average identity 'hpc', citing
  'eventually_kernelMarkedScalePressure_le_of_blockwise_limit_eq' (which is the
  repair-vanishing + block comparison + block pressure limit identification
  composition of FinslerOriginalBlockPressureLimitIdentification.lean).
* **Repair vanishing on the mark side.**  'markRate_kernelBlockRepair' supplies the
  mark-modulus rate as 'kernelBlockRepairRate q C G t', whose vanishing is
  'tendsto_kernelBlockRepairRate_zero'.

## The genuinely missing input (named, documented)

The consumer 'FinalProbUpperData' is a statement about the *physical empirical
pressure* 'finslerSupportedPressure' of the actual iid samples.  The kernel lane
controls the *kernel marked block pressure* 'kernelMarkedScalePressure'.  The
bridge between the two is the residual identification carried by
'PhysicalKernelUpperBridge': the empirical physical pressure is dominated, up to a
vanishing identification error, by the kernel marked scale pressure at the block
scale 'n + 1', for the probe-dependent kinetic mark and probe 'kin f t', 'g f t'.
No module of the lane currently proves this identification (it is exactly the
'o (L ^ q)' normalized coupling integral, the same missing rate as in the hupper
lane); it is therefore a named hypothesis, and 'finalProbUpperData_of_bridge'
shows that with it the consumer field 'hupper' is discharged.  Everything else is
reduced to the lane's proved lemmas.

No 'sorry', 'admit' or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction
  BigOperators

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

/-! ## 1. Kernel-scale upper readout data and its proved suppliers -/

variable {A₀ B₀ : Type*} [MeasurableSpace A₀] [MeasurableSpace B₀]

/-- **Kernel-scale upper readout data.**  The 'hupper'-shaped one-sided bound for
the kernel-marked scale pressure at the reference upper value 'p': for every
'eps > 0' the scale pressure is eventually at most 'p + eps'. -/
def KernelScaleUpperData (q : ℕ) (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (t p : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop,
    kernelMarkedScalePressure q A B Ks Kt kin g L t ≤ p + ε

/-- **From the two lane rates to the kernel-scale upper readout.**  Composes the
matching-moment rate and the mark-modulus coupling rate through the blockwise
stabilization into 'KernelScaleUpperData', citing the hupper assembly. -/
theorem kernelScaleUpperData_of_twoRates (q m J : ℕ) [NeZero m] (hq : 4 < q)
    (hm : 0 < m) (hJ : m ≤ 2 ^ J) (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A₀) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B₀) [IsMarkovKernel Kt]
    {C G t p : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A₀ → B₀ → (Fin q → ℝ) → ℝ} {g : A₀ → B₀ → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A₀ × B₀ => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {momentRate markRate : ℝ → ℝ}
    (hmoment : Tendsto momentRate atTop (𝓝 0))
    (hmark : Tendsto markRate atTop (𝓝 0))
    (hstab : QuantitativeBlockwiseStabilization q m Ks Kt kin g t
      (fun L => momentRate L + markRate L))
    (href : Tendsto (fun L : ℝ =>
      kernelMarkedScalePressure q A₀ B₀ Ks Kt kin g L t) atTop (𝓝 p)) :
    KernelScaleUpperData q A₀ B₀ Ks Kt kin g t p :=
  by
  obtain ⟨err, herr, hreadout⟩ :=
    hupper_readout_of_matching_moment_and_mark_modulus (q := q) (m := m) (J := J)
      hq hm hJ hJ2 Ks Kt hC0 hG0 hkin hkin_nonneg hkin_bound hkin_homog hg hgb
      hmoment hmark hstab href
  exact hreadout

/-- **Constant-kernel case, unconditionally closed.**  At constant kernels the
block comparison and repair terms are exact, so the hupper readout needs only the
reference limit 'href'. -/
theorem kernelScaleUpperData_const (q m J : ℕ) [NeZero m] (hq : 4 < q)
    (hm : 0 < m) (hJ : m ≤ 2 ^ J) (hJ2 : 2 ^ J ≤ 2 * m)
    (α : Measure A₀) [IsProbabilityMeasure α]
    (β : Measure B₀) [IsProbabilityMeasure β]
    {C G t p : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A₀ → B₀ → (Fin q → ℝ) → ℝ} {g : A₀ → B₀ → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A₀ × B₀ => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    (href : Tendsto (fun L : ℝ => kernelMarkedScalePressure q A₀ B₀
      (Kernel.const (Fin q → ℝ) α) (Kernel.const (Fin q → ℝ) β) kin g L t)
      atTop (𝓝 p)) :
    KernelScaleUpperData q A₀ B₀ (Kernel.const (Fin q → ℝ) α)
      (Kernel.const (Fin q → ℝ) β) kin g t p :=
  eventually_kernelMarkedScalePressure_le_const (q := q) (m := m) (J := J)
    hq hm hJ hJ2 α β hC0 hG0 hkin hkin_nonneg hkin_bound hkin_homog hg hgb href

/-- **Block pressure limit identification supplies the readout.**  From the
per-block limit family 'pc' and the block-average identity 'hpc', the
kernel-scale upper readout follows; this routes through the repair-vanishing and
block-comparison lemmas of the block pressure limit identification module. -/
theorem kernelScaleUpperData_of_blockwiseLimit (q m J : ℕ) [NeZero m] (hq : 4 < q)
    (hm : 0 < m) (hJ : m ≤ 2 ^ J) (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A₀) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B₀) [IsMarkovKernel Kt]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A₀ → B₀ → (Fin q → ℝ) → ℝ} {g : A₀ → B₀ → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A₀ × B₀ => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {p : ℝ} {pc : (Fin q → Fin m) → ℝ}
    (hlim : ∀ c : Fin q → Fin m,
      Tendsto (fun L : ℝ =>
        kernelMarkedScalePressure q A₀ B₀ (blockLocalKernel Ks c)
          (blockLocalKernel Kt c) kin g L t) atTop (𝓝 (pc c)))
    (hpc : (1 / (((m ^ q : ℕ) : ℝ))) * ∑ c : Fin q → Fin m, pc c = p) :
    KernelScaleUpperData q A₀ B₀ Ks Kt kin g t p :=
  eventually_kernelMarkedScalePressure_le_of_blockwise_limit_eq (q := q) (m := m)
    (J := J) hq hm hJ hJ2 Ks Kt hC0 hG0 hkin hkin_nonneg hkin_bound hkin_homog
    hg hgb hlim hpc

/-- **The mark-modulus rate is supplied by repair vanishing.**  The repair rate
'kernelBlockRepairRate q C G t' vanishes in the scale, giving the mark-side rate
of the hupper lane. -/
theorem markRate_kernelBlockRepair (q : ℕ) (hq : 4 < q) (C G t : ℝ) :
    Tendsto (fun L : ℝ => kernelBlockRepairRate q C G t L) atTop (𝓝 0) :=
  tendsto_kernelBlockRepairRate_zero q hq C G t

/-! ## 2. Consumer wiring: the physical empirical pressure

The final-assembly consumer 'FinalProbUpperData' bounds the empirical expectation
of the physical supported pressure.  The genuinely missing link between the
physical lane and the kernel lane is the residual identification below. -/

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {μ ν : ProbabilityMeasure M} {A B : Set M}
  {hA : IsCompact A} {hB : IsCompact B}
  {hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A}
  {hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B}
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  {P : ∀ n, Measure (Ω n)} {X Y : ∀ n, Fin (n + 1) → Ω n → M} {u : M → ℝ}

/-- **Named residual identification (the genuinely missing bridge).**

There is a vanishing identification error 'identErr' such that for every probe
'f' and tilt 't' in the interval of 'radius', the empirical expectation of the
physical supported pressure is eventually at most the kernel marked scale
pressure at the block scale 'n + 1', plus 'identErr n'.

Producing this identification is exactly the 'o (L ^ q)' normalized coupling
integral of the hupper lane (equivalently the physical-to-kernel block pressure
identification); it is not proved anywhere in the lane yet and is therefore a
named hypothesis. -/
def PhysicalKernelUpperBridge
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (q : ℕ) (Ks : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Kt]
    (kin : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → (Fin q → ℝ) → ℝ)
    (g : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → ℝ)
    (pressureUpper : FinalPressureField A B) (radius : FinalRadiusField A B) : Prop :=
  ∃ identErr : ℕ → ℝ, Tendsto identErr atTop (𝓝 0) ∧
    ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f → ∀ᶠ n in atTop,
      (∫ s, finslerSupportedPressure F μ ν
        (A ∪ B) (hA.union hB).measurableSet
        (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) u
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) ≤
      kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) Ks Kt (kin f t) (g f t)
        (((n + 1 : ℕ) : ℝ)) t + identErr n

/-- **The 'hupper' consumer field, wired.**  Given the kernel-scale upper
readout for every probe/tilt (supplied by the hupper lane, e.g. through
'kernelScaleUpperData_of_twoRates', 'kernelScaleUpperData_const' or
'kernelScaleUpperData_of_blockwiseLimit') and the named residual identification
'PhysicalKernelUpperBridge', the consumer 'FinalProbUpperData' holds. -/
theorem finalProbUpperData_of_bridge
    (q : ℕ) (Ks : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Kt]
    (kin : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → (Fin q → ℝ) → ℝ)
    (g : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → ℝ)
    (pressureUpper : FinalPressureField A B) (radius : FinalRadiusField A B)
    (hKernel : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      KernelScaleUpperData q ↥(A ∪ B) ↥(A ∪ B) Ks Kt (kin f t) (g f t) t
        (pressureUpper f t))
    (hbridge : PhysicalKernelUpperBridge F μ ν hA hB hμA hνB P X Y u q Ks Kt
      kin g pressureUpper radius) :
    FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius := by
  intro f t ε hpert hε
  obtain ⟨identErr, hident, hbound⟩ := hbridge
  have hε2 : 0 < ε / 2 := half_pos hε
  have hnat : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hk0 : ∀ᶠ L : ℝ in atTop,
      kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) Ks Kt (kin f t) (g f t)
        L t ≤ pressureUpper f t + ε / 2 :=
    hKernel f t hpert (ε / 2) hε2
  have hk : ∀ᶠ n : ℕ in atTop,
      kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) Ks Kt (kin f t) (g f t)
        (((n + 1 : ℕ) : ℝ)) t ≤ pressureUpper f t + ε / 2 :=
    Filter.Tendsto.eventually hnat hk0
  have hi : ∀ᶠ n : ℕ in atTop, identErr n ≤ ε / 2 := by
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hident) (ε / 2) hε2
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have habs : |identErr n| < ε / 2 := by
      simpa [Real.dist_eq] using hN n hn
    exact le_of_lt (lt_of_le_of_lt (le_abs_self (identErr n)) habs)
  have hb := hbound f t hpert
  filter_upwards [hb, hk, hi] with n hbn hkn hin
  calc ∫ s, finslerSupportedPressure F μ ν
        (A ∪ B) (hA.union hB).measurableSet
        (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) u
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n
      ≤ kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) Ks Kt (kin f t) (g f t)
          (((n + 1 : ℕ) : ℝ)) t + identErr n := hbn
    _ ≤ pressureUpper f t + ε := by linarith

end OTSelector.Reconstruction
