import OTSelector.Reconstruction.FinslerOriginalWeightedUpperLocalizationRestated
import OTSelector.Reconstruction.FinslerOriginalIIDPressureUpperLocalization
import OTSelector.Reconstruction.FinslerOriginalWeightedUpperLocalizationData

/-!
# The repaired population data: intrinsic frozen bound and guarded freezing

This module repairs the two audit defects (F13, F14 of research/AUDIT-LANES-II.md)
of the population data interface used by the upper localization lane:

* **F13.**  The localization theorem carries a uniform-in-|n| frozen bound |hCbnd|,
  while the intrinsic marked kernel is |r^(2/q) * Cb * q| with
  |r = frozenMarkedRadius (blockW q m hm) n c| growing linearly in |n| (marks are
  truncated to the unit cube, so |mDisplacement| is bounded and |hkin_bound| gives
  only |Cb * q|; research/WORKING-NOTE.md:2138-2149).  No fixed |Cbnd| majorizes
  the intrinsic kernel along the geometric lane.  The repaired structure
  |PopDataIntrinsic| replaces the uniform field by the intrinsic bound
  |hCbnd_intrinsic| of exactly that shape.
* **F14.**  The relative freezing estimate |hrel| is unguarded in |n|.  At small |n|
  the frozen radius vanishes, the marked kernel is |0|, and the unguarded field
  would force the physical kinetic to vanish at same-cell canonical pairs; the
  paper's estimate is asymptotic.  The repaired field |hrel_guarded| has guard
  |m ^ q - 1 <= n|.

The conversion |popData_of_intrinsic| recovers the original |PopData| under two
explicit named inputs: cell-boundedness |r ^ (2/q) <= 1| (under which the
intrinsic bound gives the uniform constant |Cbnd = Cb * q|) and the small-|n| part
|hsmall| of the freezing estimate (the exact residual cost of guarding |hrel|).
The theorem |physicalWeightedLocalizationFamily_of_popDataIntrinsic| consumes the
repaired structure and produces the weighted localization family, reusing the
already proved |physicalWeightedLocalizationFamily_of_popData|.

No |sorry|, |admit| or added axiom occurs.
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

structure PopDataIntrinsic
    (F : ContinuousFinslerNorm E M) (φ : M → ℝ)
    (q m : ℕ) (hm : 0 < m)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    (Am Cm : Type*) [MeasurableSpace Am] [MeasurableSpace Cm]
    (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) where
  /-- The kinetic mark kernel. -/
  kin : (Fin q → Fin m) → Am → Cm → (Fin q → ℝ) → ℝ
  /-- The probe mark kernel. -/
  g : (Fin q → Fin m) → Am → Cm → ℝ
  /-- The kinetic bound. -/
  Cb : ℝ
  /-- The probe bound. -/
  G : ℝ
  hCb0 : 0 ≤ Cb
  hG0 : 0 ≤ G
  hkin : ∀ c, Measurable (Function.uncurry (fun p : Am × Cm => kin c p.1 p.2))
  hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2
  hg : ∀ c, Measurable (Function.uncurry (g c))
  hgb : ∀ c a b, |g c a b| ≤ G
  /-- The source mark-space measures. -/
  α : (Fin q → Fin m) → Measure Am
  /-- The target mark-space measures. -/
  β : (Fin q → Fin m) → Measure Cm
  hαprob : ∀ c, IsProbabilityMeasure (α c)
  hβprob : ∀ c, IsProbabilityMeasure (β c)
  /-- The local marked pressure limits. -/
  p : (Fin q → Fin m) → ℝ → ℝ
  hp : ∀ (c : Fin q → Fin m) (t : ℝ), Tendsto
    (fun R => markedScalePressure q Am Cm (α c) (β c) (kin c) (g c) R t)
    atTop (𝓝 (p c t))
  cellS : M → (Fin q → Fin m)
  hcellS : Measurable cellS
  cellT : M → (Fin q → Fin m)
  hcellT : Measurable cellT
  hmassS : ∀ c, ((physicalSourceProbability ωM ρ₀ : Measure M)) (cellS ⁻¹' {c}) =
    ENNReal.ofReal ((blockW q m hm c : unitInterval) : ℝ)
  hmassT : ∀ c, ((physicalTargetProbability ωM ρ₁ : Measure M)) (cellT ⁻¹' {c}) =
    ENNReal.ofReal ((blockW q m hm c : unitInterval) : ℝ)
  coordS : M → Fin q → ℝ
  hcoordS : Measurable coordS
  labelS : M → Am
  hlabelS : Measurable labelS
  coordT : M → Fin q → ℝ
  hcoordT : Measurable coordT
  labelT : M → Cm
  hlabelT : Measurable labelT
  hcubeS : ∀ c, ((((physicalSourceProbability ωM ρ₀ : Measure M)) (cellS ⁻¹' {c}))⁻¹ •
    ((physicalSourceProbability ωM ρ₀ : Measure M)).restrict (cellS ⁻¹' {c})).map coordS =
      cubeMeasure (Fin q) 1
  hmarkLawS : ∀ c, ((((physicalSourceProbability ωM ρ₀ : Measure M)) (cellS ⁻¹' {c}))⁻¹ •
    ((physicalSourceProbability ωM ρ₀ : Measure M)).restrict (cellS ⁻¹' {c})).map labelS = α c
  hindepS : ∀ c, IndepFun coordS labelS
    ((((physicalSourceProbability ωM ρ₀ : Measure M)) (cellS ⁻¹' {c}))⁻¹ •
      ((physicalSourceProbability ωM ρ₀ : Measure M)).restrict (cellS ⁻¹' {c}))
  hcubeT : ∀ c, ((((physicalTargetProbability ωM ρ₁ : Measure M)) (cellT ⁻¹' {c}))⁻¹ •
    ((physicalTargetProbability ωM ρ₁ : Measure M)).restrict (cellT ⁻¹' {c})).map coordT =
      cubeMeasure (Fin q) 1
  hmarkLawT : ∀ c, ((((physicalTargetProbability ωM ρ₁ : Measure M)) (cellT ⁻¹' {c}))⁻¹ •
    ((physicalTargetProbability ωM ρ₁ : Measure M)).restrict (cellT ⁻¹' {c})).map labelT = β c
  hindepT : ∀ c, IndepFun coordT labelT
    ((((physicalTargetProbability ωM ρ₁ : Measure M)) (cellT ⁻¹' {c}))⁻¹ •
      ((physicalTargetProbability ωM ρ₁ : Measure M)).restrict (cellT ⁻¹' {c}))
  /-- The frozen probe bound. -/
  Gbnd : ℝ
  hGbnd0 : 0 ≤ Gbnd
  hGbnd : ∀ (c : Fin q → Fin m) (x y : M),
    |markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
      x y| ≤ Gbnd
  /-- The freezing errors. -/
  ε : ℕ → ℝ
  /-- The probe comparison errors. -/
  Berr : ℕ → ℝ
  /-- The probe bound sequence. -/
  Gb : ℕ → ℝ
  /-- The frozen model bounds. -/
  Bnd : ℕ → ℝ
  hε0 : ∀ n, 0 ≤ ε n
  hB0 : ∀ n, 0 ≤ Berr n
  hGb0 : ∀ n, 0 ≤ Gb n
  hBnd0 : ∀ n, 0 ≤ Bnd n
  hF0 : ∀ n c ξ i j,
    cellS (canonicalX (M := M) n i ξ) = c →
    cellT (canonicalY (M := M) n j ξ) = c →
    0 ≤ markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (kin c)
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
      (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)
  hCbnd_intrinsic : ∀ (n : ℕ) (c : Fin q → Fin m) (x y : M),
    |markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (kin c)
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤
      Cb * (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) * (q : ℝ)
  hrel_guarded : ∀ (n : ℕ), m ^ q - 1 ≤ n → ∀ c ξ i j,
      cellS (canonicalX (M := M) n i ξ) = c →
      cellT (canonicalY (M := M) n j ξ) = c →
      |finslerTileKinetic F (fun i => canonicalX (M := M) n i ξ)
          (fun j => canonicalY (M := M) n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j -
          markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (kin c)
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| ≤
        2 * ε n * markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (kin c)
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
            (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)
  hprobe : ∀ n c ξ i j,
    cellS (canonicalX (M := M) n i ξ) = c →
    cellT (canonicalY (M := M) n j ξ) = c →
    |finslerTileProbe (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
        (A ∪ B) (hA.union hB).measurableSet (hμA.mono fun x hx => Or.inl hx)
        (hνB.mono fun y hy => Or.inr hy)
        (fun i => canonicalX (M := M) n i ξ)
        (fun j => canonicalY (M := M) n j ξ) f i j -
        markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| ≤ Berr n
  hG : ∀ n c ξ i j,
    cellS (canonicalX (M := M) n i ξ) = c →
    cellT (canonicalY (M := M) n j ξ) = c →
    |markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
      (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| ≤ Gb n
  hmodel_bound : ∀ n c, (∫ ξ : canonicalOmega M n,
    frozenModelTileBlock
      (fun i => cellS (canonicalX (M := M) n i ξ))
      (fun j => cellT (canonicalY (M := M) n j ξ))
      (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
      (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
        (atlasMarkMap coordT labelT)
        (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ))
      t c / ((n + 1 : ℕ) : ℝ) ∂(canonicalLaw (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁) n)) ≤ Bnd n
  hδ : Tendsto (fun n =>
    2 * ε n * Bnd n + (|t| * Berr n + 2 * ε n * (|t| * Gb n))) atTop (𝓝 0)
  hqdim : (q : ℝ) = (Module.finrank ℝ E : ℝ) - 1


/-- **The conversion: the repaired intrinsic data yields the original |PopData|**
with |Cbnd = Cb * q| (uniform bound from the intrinsic bound under the
cell-boundedness |hr|) and with |hrel| guarded.  The small-|n| freezing estimate
|hsmall| is the exact residual named input of guarding |hrel|. -/
def popData_of_intrinsic
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
    (hr : ∀ (n : ℕ) (c : Fin q → Fin m),
      (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) ≤ 1)
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
  Cbnd := D.Cb * (q : ℝ)
  Gbnd := D.Gbnd
  hCbnd0 := mul_nonneg D.hCb0 (Nat.cast_nonneg q)
  hGbnd0 := D.hGbnd0
  hCbnd := fun n c x y => by
    have h := D.hCbnd_intrinsic n c x y
    have hr' : (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) ≤ 1 := hr n c
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    calc
      |markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (D.kin c)
          (atlasMarkMap D.coordS D.labelS) (atlasMarkMap D.coordT D.labelT) x y|
          ≤ D.Cb * (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) * (q : ℝ) := h
      _ ≤ D.Cb * 1 * (q : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr' D.hCb0) hq0
      _ = D.Cb * (q : ℝ) := by ring
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

/-- **The weighted localization family from the repaired population data.**
Re-proves the family corollary consuming |PopDataIntrinsic|: the repaired data are
converted to the original |PopData| by |popData_of_intrinsic| (cell-boundedness
|hr| and the small-|n| freezing estimate |hsmall| are the only added named
inputs), and the already proved |physicalWeightedLocalizationFamily_of_popData|
completes the proof. -/
theorem physicalWeightedLocalizationFamily_of_popDataIntrinsic
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
    (hr : ∀ (n : ℕ) (c : Fin q → Fin m),
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
      (fun c : Fin q → Fin m => ((blockW q m hm c : unitInterval) : ℝ)) pc radius :=
  physicalWeightedLocalizationFamily_of_popData (F := F) (φ := φ) (hφ := hφ)
    (hcomplete := hcomplete) (hdim := hdim) (ωM := ωM) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
    (hA := hA) (hB := hB) (hAB := hAB) (hμA := hμA) (hνB := hνB)
    (P := P) (X := X) (Y := Y) (hX := hX) (hY := hY) (hXi := hXi) (hYi := hYi)
    (hXlaw := hXlaw) (hYlaw := hYlaw) (hXY := hXY)
    (q := q) (m := m) (hm := hm) (radius := radius) (pc := pc)
    (data := fun f t hpert =>
      popData_of_intrinsic F φ q m hm ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t
        (data f t hpert) hr (hsmall f t hpert))
    (hpc := hpc)

end OTSelector.Reconstruction
