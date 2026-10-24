import OTSelector.Reconstruction.FinslerOriginalIIDPressureUpperLocalization
import OTSelector.Reconstruction.FinslerOriginalHupperWiring

/-!
# Physical-to-kernel pressure bridge: closing the hupper identification gap

This module closes the residual identification 'PhysicalKernelUpperBridge' left
open by 'FinslerOriginalHupperWiring.lean', in the strongest form the lane
supports, and produces the consumer field 'FinalProbUpperData' for the actual
iid lane.

## The physical localization input (discharged by the canonical-tile chain)

'PhysicalWeightedUpperLocalization' is exactly the conclusion shape of
'OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.finsler_originalIID_pressure_upper_localization'
(FinslerOriginalIIDPressureUpperLocalization.lean): for every probe 'f' and tilt
't' inside the common interval, the expected supported empirical Finsler
pressure at the paper scale is eventually bounded by the explicit block weighted
sum 'sum c, (1 / m^q) * pc c t' of the local marked pressure limits, plus any
'eps > 0'.  That theorem discharges all sample-level inputs (joint canonical
law, tile-count discrepancy, integrability) from the paper's sampling
hypotheses, leaving only population data (cell masses, cube/Haar laws, mark laws
and independence, kernel bounds, freezing and probe approximations, frozen model
bound, vanishing additive error).  We therefore take that conclusion as a named
input and prove the remaining identifications here.

## What is proved here

* 'physicalBlockPressureDomination_of_weightedLocalization': the physical
  expectation is dominated by the *block-averaged* kernel marked scale pressure
  at block scale 'n + 1', using the block pressure limit identification
  ('tendsto_blockAverageScalePressure_of_blockwise_limit_eq').  This is the
  physical block decomposition: no physical cost remainder or plan residual is
  left over, because the canonical-tile lane has already absorbed them into the
  vanishing error 'eps' of the localization.
* 'finalProbUpperData_of_physicalBlockPressureDomination': the consumer field
  'FinalProbUpperData' with 'pressureUpper' identified as the block weighted sum
  of the local limits.
* 'physicalKernelEpsilonDomination_of_blockDomination_reverse': the one-sided
  kernel form of the bridge, obtained from the block domination plus the reverse
  block comparison 'blockAverage <= kernelMarkedScalePressure + eps'.
* 'finalProbUpperData_of_kernelEpsilonDomination': the consumer field from the
  kernel-form bridge and the kernel-scale upper readout
  'KernelScaleUpperData' (which is supplied either by
  'kernelScaleUpperData_of_twoRates' or by
  'kernelScaleUpperData_of_blockwiseLimit' from
  'FinslerOriginalHupperWiring.lean').
* 'finalProbUpperData_of_weightedLocalization_twoRates': the composed end-to-end
  wiring of the hupper lane for the actual iid samples.

## The exact remaining input

The only input not proved in the lane is the *reverse* block comparison

  'blockAverageScalePressure q m Ks Kt kin g L t <= kernelMarkedScalePressure q A B Ks Kt kin g L t + eps'

(one-sided, eventually in 'L'), together with the two rates (matching moment and
mark-modulus coupling) if the kernel readout is obtained through
'kernelScaleUpperData_of_twoRates'.  The lane proves the opposite direction
('kernelMarkedScalePressure_le_blockAverageScalePressure_add_gridRepairError',
i.e. the grid repair bounds the original kernel from above), so the reverse
comparison is genuinely missing; it is named 'ReverseBlockComparison' below.
Nothing else remains: the physical remainder and the plan residual are inside
the localization error.

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

/-! ## 1. The physical localization input -/

/-- **Weighted physical upper localization (the canonical-tile chain output).**

For every probe 'f' and tilt 't' with '|t| < radius f', and every 'eps > 0', the
expected supported empirical Finsler pressure at the paper scale is eventually
at most the block weighted sum 'sum c, (1 / m^q) * pc c t' of the local marked
pressure limits, plus 'eps'.

This is the conclusion of
'finsler_originalIID_pressure_upper_localization' (with the block index set
'Fin q → Fin m', weights '1 / m^q', and local limits 'pc'), whose hypotheses are
the paper's population data; the physical cost remainder and the plan residual
are already absorbed in its vanishing error. -/
def PhysicalWeightedUpperLocalization
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (q m : ℕ) (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (radius : FinalRadiusField A B) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop,
      (∫ s, finslerSupportedPressure F μ ν
        (A ∪ B) (hA.union hB).measurableSet
        (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) u
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) ≤
      (∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c) + ε

/-- **The consumer field from the weighted localization and the identification
of 'pressureUpper' with the weighted sum of the local limits.** -/
theorem finalProbUpperData_of_weightedLocalization
    (hLoc : PhysicalWeightedUpperLocalization F μ ν hA hB hμA hνB P X Y u q m pc radius)
    (pressureUpper : FinalPressureField A B)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      pressureUpper f t =
        ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c) :
    FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius := by
  intro f t ε hpert hε
  filter_upwards [hLoc f t hpert ε hε] with n hn
  rw [hpc f t hpert]
  exact hn

/-! ## 2. The physical block decomposition -/

/-- **Physical domination by the block-averaged kernel marked scale pressure.**

The expected physical pressure at block scale 'n + 1' is eventually at most the
block-averaged scale pressure plus 'eps'.  This is the physical block
decomposition at the level of the actual iid samples. -/
def PhysicalBlockPressureDomination
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (q m : ℕ) (Ks : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Kt]
    (kin : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → (Fin q → ℝ) → ℝ)
    (g : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → ℝ)
    (radius : FinalRadiusField A B) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop,
      (∫ s, finslerSupportedPressure F μ ν
        (A ∪ B) (hA.union hB).measurableSet
        (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) u
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) ≤
      blockAverageScalePressure q m Ks Kt (kin f t) (g f t)
        (((n + 1 : ℕ) : ℝ)) t + ε

/-- **Physical block decomposition.**  The weighted localization bound upgrades
to domination by the block-averaged kernel marked scale pressure, using the
block pressure limit identification: the block average converges to the weighted
sum of the local limits. -/
theorem physicalBlockPressureDomination_of_weightedLocalization
    (hLoc : PhysicalWeightedUpperLocalization F μ ν hA hB hμA hνB P X Y u q m pc radius)
    (Ks : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Kt]
    (kin : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → (Fin q → ℝ) → ℝ)
    (g : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → ℝ)
    (hlim : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      ∀ c : Fin q → Fin m,
        Tendsto (fun L : ℝ =>
          kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) (blockLocalKernel Ks c)
            (blockLocalKernel Kt c) (kin f t) (g f t) L t) atTop (𝓝 (pc f t c))) :
    PhysicalBlockPressureDomination F μ ν hA hB hμA hνB P X Y u q m Ks Kt kin g radius := by
  intro f t hpert ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hconv := tendsto_blockAverageScalePressure_of_blockwise_limit_eq q m Ks Kt
    (t := t) (p := ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c)
    (pc := pc f t) (hlim f t hpert) (by rw [Finset.mul_sum])
  have hnat : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hconv.eventually (eventually_ge_nhds (by linarith :
      (∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c) - ε / 2 <
        ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c)))
  obtain ⟨M, hM⟩ := exists_nat_ge N
  have hnear : ∀ᶠ n : ℕ in atTop,
      (∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c) - ε / 2 ≤
        blockAverageScalePressure q m Ks Kt (kin f t) (g f t) (((n + 1 : ℕ) : ℝ)) t := by
    refine eventually_atTop.2 ⟨M, fun n hn => ?_⟩
    have hMle : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hsucc : (n : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by push_cast; linarith
    exact hN _ (by linarith : N ≤ (((n + 1 : ℕ) : ℝ)))
  filter_upwards [hLoc f t hpert (ε / 2) hε2, hnear] with n hn hb
  linarith

/-- **The consumer field from the physical block domination.**  The block
average converges to the block weighted sum (again by the block pressure limit
identification), so 'pressureUpper' becomes the weighted sum of the local
limits. -/
theorem finalProbUpperData_of_physicalBlockPressureDomination
    (Ks : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Kt]
    (kin : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → (Fin q → ℝ) → ℝ)
    (g : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → ℝ)
    {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    (pressureUpper : FinalPressureField A B)
    (hlim : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      ∀ c : Fin q → Fin m,
        Tendsto (fun L : ℝ =>
          kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) (blockLocalKernel Ks c)
            (blockLocalKernel Kt c) (kin f t) (g f t) L t) atTop (𝓝 (pc f t c)))
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      (1 / (((m ^ q : ℕ) : ℝ))) * (∑ c : Fin q → Fin m, pc f t c) = pressureUpper f t)
    (hdom : PhysicalBlockPressureDomination F μ ν hA hB hμA hνB P X Y u q m Ks Kt kin g radius) :
    FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius := by
  intro f t ε hpert hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hconv := tendsto_blockAverageScalePressure_of_blockwise_limit_eq q m Ks Kt
    (t := t) (p := pressureUpper f t) (pc := pc f t) (hlim f t hpert) (hpc f t hpert)
  have hnat : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hnear : ∀ᶠ n : ℕ in atTop,
      blockAverageScalePressure q m Ks Kt (kin f t) (g f t) (((n + 1 : ℕ) : ℝ)) t ≤
        pressureUpper f t + ε / 2 :=
    Filter.Tendsto.eventually hnat
      (hconv.eventually (eventually_le_nhds (by linarith : pressureUpper f t < pressureUpper f t + ε / 2)))
  filter_upwards [hdom f t hpert (ε / 2) hε2, hnear] with n hn hb
  linarith

/-! ## 3. The kernel form of the bridge -/

/-- **Reverse block comparison (the exact remaining input).**

The block-averaged scale pressure is one-sidedly dominated by the kernel marked
scale pressure, up to any 'eps > 0', eventually in the scale.  This is the
reverse of the grid repair inequality proved in the lane. -/
def ReverseBlockComparison
    (q m : ℕ) (Ks : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Kt]
    (kin : ↥(A ∪ B) → ↥(A ∪ B) → (Fin q → ℝ) → ℝ) (g : ↥(A ∪ B) → ↥(A ∪ B) → ℝ)
    (t : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ L : ℝ in atTop,
    blockAverageScalePressure q m Ks Kt kin g L t ≤
      kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) Ks Kt kin g L t + ε

/-- **Kernel form of the physical domination.**  From the physical block
domination and the reverse block comparison, the physical expectation is
one-sidedly dominated by the kernel marked scale pressure at block scale
'n + 1'.  This is the strongest true form of 'PhysicalKernelUpperBridge': the
identification error is arbitrary 'eps > 0' rather than a fixed vanishing
sequence (the bridge cannot be stated with a single vanishing 'identErr' because
the localization error is produced separately for every 'eps'). -/
theorem physicalKernelEpsilonDomination_of_blockDomination_reverse
    (Ks : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Kt]
    (kin : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → (Fin q → ℝ) → ℝ)
    (g : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → ℝ)
    (hrev : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      ReverseBlockComparison q m Ks Kt (kin f t) (g f t) t)
    (hdom : PhysicalBlockPressureDomination F μ ν hA hB hμA hνB P X Y u q m Ks Kt kin g radius) :
    ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        (∫ s, finslerSupportedPressure F μ ν
          (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) ≤
        kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) Ks Kt (kin f t) (g f t)
          (((n + 1 : ℕ) : ℝ)) t + ε := by
  intro f t hpert ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hnat : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hrevn : ∀ᶠ n : ℕ in atTop,
      blockAverageScalePressure q m Ks Kt (kin f t) (g f t) (((n + 1 : ℕ) : ℝ)) t ≤
        kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) Ks Kt (kin f t) (g f t)
          (((n + 1 : ℕ) : ℝ)) t + ε / 2 :=
    Filter.Tendsto.eventually hnat (hrev f t hpert (ε / 2) hε2)
  filter_upwards [hdom f t hpert (ε / 2) hε2, hrevn] with n hn hb
  linarith

/-- **The consumer field from the kernel-form domination and the kernel-scale
upper readout.**  'hKernel' is supplied by 'kernelScaleUpperData_of_twoRates'
(given the two rates) or by 'kernelScaleUpperData_of_blockwiseLimit'. -/
theorem finalProbUpperData_of_kernelEpsilonDomination
    (Ks : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Kt]
    (kin : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → (Fin q → ℝ) → ℝ)
    (g : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → ℝ)
    (pressureUpper : FinalPressureField A B)
    (hKernel : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      KernelScaleUpperData q ↥(A ∪ B) ↥(A ∪ B) Ks Kt (kin f t) (g f t) t
        (pressureUpper f t))
    (hdom : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        (∫ s, finslerSupportedPressure F μ ν
          (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) u
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) ≤
        kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) Ks Kt (kin f t) (g f t)
          (((n + 1 : ℕ) : ℝ)) t + ε) :
    FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius := by
  intro f t ε hpert hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hnat : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hkn : ∀ᶠ n : ℕ in atTop,
      kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) Ks Kt (kin f t) (g f t)
        (((n + 1 : ℕ) : ℝ)) t ≤ pressureUpper f t + ε / 2 :=
    Filter.Tendsto.eventually hnat (hKernel f t hpert (ε / 2) hε2)
  filter_upwards [hdom f t hpert (ε / 2) hε2, hkn] with n hn hb
  linarith

/-! ## 4. End-to-end wiring for the actual iid lane -/

/-- **The hupper consumer field for the actual lane, blocked route.**

The physical localization (canonical-tile chain) plus the block pressure limit
identification directly produce 'FinalProbUpperData' with 'pressureUpper' equal
to the block weighted sum of the local limits.  No rates are needed on this
route. -/
theorem finalProbUpperData_of_weightedLocalization_blockwiseLimit
    (hLoc : PhysicalWeightedUpperLocalization F μ ν hA hB hμA hνB P X Y u q m pc radius)
    (Ks : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Kt]
    (kin : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → (Fin q → ℝ) → ℝ)
    (g : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → ℝ)
    (pressureUpper : FinalPressureField A B)
    (hlim : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      ∀ c : Fin q → Fin m,
        Tendsto (fun L : ℝ =>
          kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) (blockLocalKernel Ks c)
            (blockLocalKernel Kt c) (kin f t) (g f t) L t) atTop (𝓝 (pc f t c)))
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      (1 / (((m ^ q : ℕ) : ℝ))) * (∑ c : Fin q → Fin m, pc f t c) = pressureUpper f t) :
    FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius :=
  finalProbUpperData_of_physicalBlockPressureDomination
    Ks Kt kin g pressureUpper hlim hpc
    (physicalBlockPressureDomination_of_weightedLocalization hLoc Ks Kt kin g hlim)

/-- **The hupper consumer field for the actual lane, two-rates route.**

The physical localization plus the reverse block comparison plus the
kernel-scale upper readout (supplied by 'kernelScaleUpperData_of_twoRates' from
the matching-moment and mark-modulus rates, or by
'kernelScaleUpperData_of_blockwiseLimit') produce 'FinalProbUpperData'. -/
theorem finalProbUpperData_of_weightedLocalization_twoRates
    (hLoc : PhysicalWeightedUpperLocalization F μ ν hA hB hμA hνB P X Y u q m pc radius)
    (Ks : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) ↥(A ∪ B)) [IsMarkovKernel Kt]
    (kin : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → (Fin q → ℝ) → ℝ)
    (g : FinalProbeSpace A B → ℝ → ↥(A ∪ B) → ↥(A ∪ B) → ℝ)
    (hlim : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      ∀ c : Fin q → Fin m,
        Tendsto (fun L : ℝ =>
          kernelMarkedScalePressure q ↥(A ∪ B) ↥(A ∪ B) (blockLocalKernel Ks c)
            (blockLocalKernel Kt c) (kin f t) (g f t) L t) atTop (𝓝 (pc f t c)))
    (pressureUpper : FinalPressureField A B)
    (hrev : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      ReverseBlockComparison q m Ks Kt (kin f t) (g f t) t)
    (hKernel : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      KernelScaleUpperData q ↥(A ∪ B) ↥(A ∪ B) Ks Kt (kin f t) (g f t) t
        (pressureUpper f t)) :
    FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius :=
  finalProbUpperData_of_kernelEpsilonDomination
    Ks Kt kin g pressureUpper hKernel
    (physicalKernelEpsilonDomination_of_blockDomination_reverse
      Ks Kt kin g hrev
      (physicalBlockPressureDomination_of_weightedLocalization hLoc Ks Kt kin g hlim))

end OTSelector.Reconstruction
