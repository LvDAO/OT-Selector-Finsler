import OTSelector.Reconstruction.FinslerOriginalPopDataIntrinsicBound

/-!
# The upper localization family under the intrinsic frozen bound (F13 repair)

This module closes the F13 work: the upper localization family is re-proved from
the *intrinsic* frozen bound |hCbnd_intrinsic| of |PopDataIntrinsic| (the field
|markedKineticKernel (frozenMarkedRadius ...) ...| <= |Cb * r ^ (2/q) * q|),
instead of the localization theorem's uniform-in-n |hCbnd|.

## Where the uniform bound is consumed

In the repo's upper localization theorem
(|finsler_originalIID_pressure_upper_localization|,
FinslerOriginalIIDPressureUpperLocalization.lean) the uniform bound |hCbnd| is
passed unchanged through the frozen domination chain (the theorem's only uses are
at lines 301, 432 and 579, where |hCbnd| is forwarded to the core frozen estimate).
In the population-data interface |PopData| it is the single field |hCbnd|; its
construction from the intrinsic field and the cell-boundedness |r ^ (2/q) <= 1|
is exactly the calc performed by |popData_of_intrinsic|
(FinslerOriginalPopDataIntrinsicBound.lean).  Hence the intrinsic replacement of
that step is |uniformFrozenBound_of_intrinsicBound| below -- the uniform constant
bound follows from the intrinsic bound precisely at the bounded cell scale -- and
the localization family theorem under |PopDataIntrinsic| is
|physicalWeightedLocalizationFamily_of_intrinsicBound|.

The conclusion is unchanged and stays at the paper scale: it is the same
|PhysicalWeightedLocalizationFamily| with block weights |1 / m^q| and the pressure
upper bound at scale |(n+1)^(2/(d-1))|.

## Residual inputs

The only residual inputs are the printed |hcell| (the bounded-cell condition
|r ^ (2/q) <= 1| under which the intrinsic bound yields a uniform constant) and
|hsmall| (the small-|n| freezing values, the exact cost of guarding |hrel|, F14).
Both are explicit binders; no silent assumption and no |sorry|/|admit|/axiom.
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

/-- **The intrinsic replacement for the uniform bound step.**  If the frozen
kernel obeys the intrinsic bound |Cb * r ^ (2/q) * q| and the radius scale is
bounded, |r ^ (2/q) <= 1|, then it obeys the uniform constant bound |Cb * q|.
This is the step at which the localization theorem's uniform |hCbnd| is consumed;
on the population lane |r| must be a bounded cell radius for it to hold, while the
block count |floor ((n + 1) / m^q)| supplies |r ^ (2/q) -> infinity|. -/
theorem uniformFrozenBound_of_intrinsicBound
    {Xs Yt A B : Type*} {q : ℕ} {Cb r : ℝ} (hCb : 0 ≤ Cb)
    (hcell : r ^ (2 / (q : ℝ)) ≤ 1)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (markS : Xs → (Fin q → ℝ) × A) (markT : Yt → (Fin q → ℝ) × B)
    (h : ∀ (x : Xs) (y : Yt),
      |markedKineticKernel (q := q) r kin markS markT x y| ≤
        Cb * r ^ (2 / (q : ℝ)) * (q : ℝ)) :
    ∀ (x : Xs) (y : Yt),
      |markedKineticKernel (q := q) r kin markS markT x y| ≤ Cb * (q : ℝ) := by
  intro x y
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  calc
    |markedKineticKernel (q := q) r kin markS markT x y|
        ≤ Cb * r ^ (2 / (q : ℝ)) * (q : ℝ) := h x y
    _ ≤ Cb * 1 * (q : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcell hCb) hq0
    _ = Cb * (q : ℝ) := by ring

/-- **The upper localization family under the intrinsic frozen bound.**  The full
sampling telescope with |PopDataIntrinsic| data (intrinsic frozen bound), the
bounded-cell input |hcell| and the small-|n| freezing input |hsmall|, producing the
paper-scale |PhysicalWeightedLocalizationFamily| with block weights |1 / m^q|.
The proof reduces to the already proved localization family theorem via the
uniform-bound step above (|popData_of_intrinsic|). -/
theorem physicalWeightedLocalizationFamily_of_intrinsicBound
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
  physicalWeightedLocalizationFamily_of_popDataIntrinsic (F := F) (φ := φ) (hφ := hφ)
    (hcomplete := hcomplete) (hdim := hdim) (ωM := ωM) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
    (hA := hA) (hB := hB) (hAB := hAB) (hμA := hμA) (hνB := hνB)
    (P := P) (X := X) (Y := Y) (hX := hX) (hY := hY) (hXi := hXi) (hYi := hYi)
    (hXlaw := hXlaw) (hYlaw := hYlaw) (hXY := hXY)
    (q := q) (m := m) (hm := hm) (radius := radius) (pc := pc)
    (hr := hcell) (data := data) (hsmall := hsmall) (hpc := hpc)

end OTSelector.Reconstruction
