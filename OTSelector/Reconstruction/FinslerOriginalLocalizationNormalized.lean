import OTSelector.Reconstruction.FinslerOriginalPopDataIntrinsicBound

/-!
# F13 closed at the normalized interface: the localization family with NO |hcell|

## What is delivered

|physicalWeightedLocalizationFamily_of_normalized|: the same full sampling
telescope as the upper localization theorem, consuming |PopDataIntrinsic| data
(the intrinsic frozen bound |markedKineticKernel r ... <= Cb * r ^ (2/q) * q|),
the small-|n| freezing input |hsmall| and the partition-consistency input |hpc|,
and producing the paper-scale |PhysicalWeightedLocalizationFamily|.

Unlike |physicalWeightedLocalizationFamily_of_intrinsicBound| it requires **no
|hcell|** uniform-in-n cell bound; the only residual radius input is the
*existential boundedness* |hB : exists B >= 0, forall n c,
(frozenMarkedRadius ...) ^ (2/q) <= B|, consumed once to build the uniform
constant |Cbnd = Cb * q * B| in |popData_of_intrinsicBounded|.

## Why this is the right normalized statement

The paper normalizes the pressure by the intensity scale |R ^ q|
(|markedScalePressure = markedPressure (intensity R ^ q) / R ^ q|,
MarkedPressureLimit.lean:25) and the physical cost carries |(n+1)^(2/q)|
(main.tex:134, main.tex:1405).  The normalized kernel bound
|normalizedKernelBound_of_intrinsicBound| (FinslerOriginalFrozenEstimateScale)
shows |markedKineticKernel r ... / r ^ q <= Cb * q| for |r >= 1|, |q >= 2|:
uniform in |n| with no cell bound.  The repo's frozen estimate, however, consumes
the **raw** kernel: |hCbnd| (FinslerOriginalIIDPressureUpperLocalization.lean,
lines 237-240, forwarded at 301, 432, 579) is an unnormalized uniform bound, and
an unnormalized uniform bound is equivalent to a bound on the effective radius
|r ^ (2/q)|.  This is exactly what |hB| records, stripped of the |B = 1|
normalization of |hcell|; |hcell| is the special case |B = 1|.  Dropping |hB|
entirely requires re-proving the frozen-estimate core to consume the
intensity-normalized kernel (the named input |NormalizedFrozenEstimate|,
FinslerOriginalFrozenEstimateScale.lean), which is outside the consumer chain.

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

def popData_of_intrinsicBounded
    (F : ContinuousFinslerNorm E M) (φ : M → ℝ)
    (q m : ℕ) (hm : 0 < m)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    (Am Cm : Type*) [MeasurableSpace Am] [MeasurableSpace Cm]
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ)
    (D : PopDataIntrinsic F φ q m hm ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hBd : ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (c : Fin q → Fin m),
      (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) ≤ B)
    (hsmall : ∀ (n : ℕ), n < m ^ q - 1 → ∀ (c : Fin q → Fin m)
      (ξ : canonicalOmega M n) (i j : Fin (n + 1)),
      D.cellS (canonicalX (M := M) n i ξ) = c →
      D.cellT (canonicalY (M := M) n j ξ) = c →
      |finslerTileKinetic F (fun i => canonicalX (M := M) n i ξ)
          (fun j => canonicalY (M := M) n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j -
          markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (D.kin c)
            (atlasMarkMap D.coordS D.labelS) (atlasMarkMap D.coordT D.labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| ≤
        2 * D.ε n * markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (D.kin c)
            (atlasMarkMap D.coordS D.labelS) (atlasMarkMap D.coordT D.labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)) :
    PopData F φ q m hm ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t where
  kin := D.kin
  g := D.g
  Cb := D.Cb
  G := D.G
  hCb0 := D.hCb0
  hG0 := D.hG0
  hkin := D.hkin
  hkin_bound := D.hkin_bound
  hg := D.hg
  hgb := D.hgb
  α := D.α
  β := D.β
  hαprob := D.hαprob
  hβprob := D.hβprob
  p := D.p
  hp := D.hp
  cellS := D.cellS
  hcellS := D.hcellS
  cellT := D.cellT
  hcellT := D.hcellT
  hmassS := D.hmassS
  hmassT := D.hmassT
  coordS := D.coordS
  hcoordS := D.hcoordS
  labelS := D.labelS
  hlabelS := D.hlabelS
  coordT := D.coordT
  hcoordT := D.hcoordT
  labelT := D.labelT
  hlabelT := D.hlabelT
  hcubeS := D.hcubeS
  hmarkLawS := D.hmarkLawS
  hindepS := D.hindepS
  hcubeT := D.hcubeT
  hmarkLawT := D.hmarkLawT
  hindepT := D.hindepT
  Cbnd := D.Cb * (q : ℝ) * hBd.choose
  Gbnd := D.Gbnd
  hCbnd0 := mul_nonneg (mul_nonneg D.hCb0 (Nat.cast_nonneg q)) hBd.choose_spec.1
  hGbnd0 := D.hGbnd0
  hCbnd := fun n c x y => by
    have h := D.hCbnd_intrinsic n c x y
    have hr' : (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) ≤ hBd.choose :=
      hBd.choose_spec.2 n c
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    calc
      |markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (D.kin c)
          (atlasMarkMap D.coordS D.labelS) (atlasMarkMap D.coordT D.labelT) x y|
          ≤ D.Cb * (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) * (q : ℝ) := h
      _ ≤ D.Cb * hBd.choose * (q : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr' D.hCb0) hq0
      _ = D.Cb * (q : ℝ) * hBd.choose := by ring
  hGbnd := D.hGbnd
  ε := D.ε
  Berr := D.Berr
  Gb := D.Gb
  Bnd := D.Bnd
  hε0 := D.hε0
  hB0 := D.hB0
  hGb0 := D.hGb0
  hBnd0 := D.hBnd0
  hF0 := D.hF0
  hrel := fun n c ξ i j hS hT => by
    by_cases hn : n < m ^ q - 1
    · exact hsmall n hn c ξ i j hS hT
    · exact D.hrel_guarded n (Nat.le_of_not_lt hn) c ξ i j hS hT
  hprobe := D.hprobe
  hG := D.hG
  hmodel_bound := D.hmodel_bound
  hδ := D.hδ
  hqdim := D.hqdim


theorem physicalWeightedLocalizationFamily_of_normalized
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
    (hBd : ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (c : Fin q → Fin m),
      (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) ≤ B)
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
      (fun c : Fin q → Fin m => ((blockW q m hm c : unitInterval) : ℝ)) pc radius :=
  physicalWeightedLocalizationFamily_of_popData (F := F) (φ := φ) (hφ := hφ)
    (hcomplete := hcomplete) (hdim := hdim) (ωM := ωM) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
    (hA := hA) (hB := hB) (hAB := hAB) (hμA := hμA) (hνB := hνB)
    (P := P) (X := X) (Y := Y) (hX := hX) (hY := hY) (hXi := hXi) (hYi := hYi)
    (hXlaw := hXlaw) (hYlaw := hYlaw) (hXY := hXY)
    (q := q) (m := m) (hm := hm) (radius := radius) (pc := pc)
    (data := fun f t hpert =>
      popData_of_intrinsicBounded F φ q m hm ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t
        (data f t hpert) hBd (hsmall f t hpert))
    (hpc := hpc)

end OTSelector.Reconstruction
