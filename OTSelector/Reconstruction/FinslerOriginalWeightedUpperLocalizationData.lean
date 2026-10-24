import OTSelector.Reconstruction.FinslerOriginalPhysicalKernelBridge

/-!
# Weighted upper localization data for the actual iid lane

This module finishes the hupper wiring: it takes the weighted-sum localization
conclusion produced by the canonical-tile chain
('finsler_originalIID_pressure_upper_localization', in
FinslerOriginalIIDPressureUpperLocalization.lean) in the exact family shape
needed by the consumer, converts it to 'PhysicalWeightedUpperLocalization' (the
named input of FinslerOriginalPhysicalKernelBridge.lean), and chains the end-to-end
consumer theorems.

## The instantiation dictionary (binder transfer)

'finsler_originalIID_pressure_upper_localization' is stated for one probe 'f' and
one tilt 't', with the following binders, and proves (writing K := A ∪ B,
mu := physicalSourceProbability omegaM rho0, nu := physicalTargetProbability omegaM
rho1, and scale n := ((n + 1 : R) ^ (2 / ((finrank R E : R) - 1))))

  integral finslerSupportedPressure F mu nu K ... (X n) (Y n) phi (scale n) f t dP n
    <= (sum c, (w c : R) * p c t) + eps'

for every 'eps' > 0 and eventually all 'n'.  The transfer to the block weighted
form used by the consumer is the instantiation

  iota      := Fin q -> Fin m,
  w c       := 1 / (m ^ q)   (the block weight, as a unitInterval),
  p c s     := pc f s c      (the local marked pressure limit for probe 'f' and
                              tilt 's', chosen per probe),
  K         := A ∪ B,  mu := physicalSourceProbability omegaM rho0,
  nu        := physicalTargetProbability omegaM rho1,
  phi       := u.

Then '(w c : R) * p c t = (1 / m^q) * pc f t c', so the localization bound is
exactly the block weighted bound 'sum c, (1 / m^q) * pc f t c + eps'.

## What is proved here

* 'PhysicalWeightedLocalizationFamily': the localization conclusion in family
  form, with *arbitrary* block index type 'iota' and arbitrary weights 'w' (the
  general shape of the canonical-tile theorem), plus
  'physicalWeightedUpperLocalization_of_family_block' specialising it to the
  block weights, which is exactly 'PhysicalWeightedUpperLocalization'.
* 'finalProbUpperData_actualLane': the end-to-end hupper consumer field
  'FinalProbUpperData' for the actual iid lane from the block weighted
  localization family plus the identification of 'pressureUpper' with the
  weighted sum of the local limits.
* 'finalProbUpperData_actualLane_blockwiseLimit': the same with the blockwise
  limit inputs 'hlim' / 'hpc' of
  'finalProbUpperData_of_weightedLocalization_blockwiseLimit'.

## Exact remaining named inputs

The localization family is *not* free data: it is the conclusion of
'finsler_originalIID_pressure_upper_localization', which is already proved in the
lane.  Restating that theorem as this family requires only its hypotheses:
(a) the sampling hypotheses: 'hcomplete', 'hdim : 6 <= finrank', the two physical
probability instances, compact 'A' 'B' with disjointness, membership a.e.
hypotheses, the space 'Omega n', probability measures 'P n', measurable iid
coordinate maps 'X' 'Y' with the prescribed marginals and cross independence, and
the 1-Lipschitz potential 'phi' ('u');
(b) the per-probe population data: cell maps 'cellS' 'cellT' with exact masses
'w' (= 1/m^q), measurable cube coordinates and mark labels with cube/Haar and
mark laws and independence, the mark-space measures 'alpha' 'beta' with Markov
limits 'p' (= the local limits 'pc'), the kinetic mark bounds 'Cb' 'G' and their
measurability/compatibility with the probe, the freezing and probe approximation
parameters 'eps' 'Berr' 'Gb' with their vanishings, the frozen model bound 'Bnd',
the eventual error bound 'hrel', the probe-near bound 'hprobe' and the vanishing
combined error 'hdelta', and the dimension identity 'q = finrank - 1'.
These are population-level (not sample-level) and are exactly the paper's model
assumptions; nothing else is missing on this route.
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

/-- **The weighted physical localization family.**

The exact conclusion shape of the canonical-tile localization theorem
('finsler_originalIID_pressure_upper_localization'), with an arbitrary finite
block index type 'iota' and arbitrary weights 'w': for every probe and tilt in
the common interval, the expected physical supported pressure at the paper scale
is eventually at most the weighted sum of the local marked pressure limits plus
any 'eps > 0'. -/
def PhysicalWeightedLocalizationFamily
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (pc : FinalProbeSpace A B → ℝ → ι → ℝ) (radius : FinalRadiusField A B) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop,
      (∫ s, finslerSupportedPressure F μ ν
        (A ∪ B) (hA.union hB).measurableSet
        (hμA.mono fun x hx ↦ Or.inl hx) (hνB.mono fun y hy ↦ Or.inr hy)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) u
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) ≤
      (∑ c, w c * pc f t c) + ε

/-- **Block-weight specialization.**  The block weighted family (index set
'Fin q → Fin m', weights '1 / m^q') is exactly the named input
'PhysicalWeightedUpperLocalization'. -/
theorem physicalWeightedUpperLocalization_of_family_block
    (q m : ℕ) {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    (radius : FinalRadiusField A B)
    (h : PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ)))
      (fun f t c => pc f t c) radius) :
    PhysicalWeightedUpperLocalization F μ ν hA hB hμA hνB P X Y u q m pc radius :=
  h

/-- **The hupper consumer field for the actual iid lane.**

From the block weighted localization family (whose local limits are 'pc') and the
identification of 'pressureUpper' with the block weighted sum of the local
limits, the consumer 'FinalProbUpperData' follows. -/
theorem finalProbUpperData_actualLane
    (q m : ℕ) {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    (radius : FinalRadiusField A B)
    (hLoc : PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ)))
      (fun f t c => pc f t c) radius)
    (pressureUpper : FinalPressureField A B)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      pressureUpper f t =
        ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c) :
    FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius :=
  finalProbUpperData_of_weightedLocalization
    (physicalWeightedUpperLocalization_of_family_block q m radius hLoc) pressureUpper hpc

/-- **The hupper consumer field with the blockwise limit inputs.**

Same as 'finalProbUpperData_actualLane', but the identification of
'pressureUpper' with the block weighted sum is factored through the blockwise
limit inputs 'hlim' (per-block kernel marked scale pressure limits) and 'hpc'
(the numerical block-average identification), exactly the inputs of
'finalProbUpperData_of_weightedLocalization_blockwiseLimit'. -/
theorem finalProbUpperData_actualLane_blockwiseLimit
    (q m : ℕ) {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
    (radius : FinalRadiusField A B)
    (hLoc : PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ)))
      (fun f t c => pc f t c) radius)
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
  finalProbUpperData_of_weightedLocalization_blockwiseLimit
    (physicalWeightedUpperLocalization_of_family_block q m radius hLoc) Ks Kt kin g
    pressureUpper hlim hpc

end OTSelector.Reconstruction
