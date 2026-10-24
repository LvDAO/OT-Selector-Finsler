import OTSelector.Reconstruction.FinslerOriginalPopDataIntrinsicBound

/-!
# Intrinsic upper localization with a sample-dependent frozen bound

The marked radius is a block count and its kinetic bound grows with the sample
size. The fixed-sample integrability and law identity use only a bound at that
sample size. This module uses the intrinsic bound directly; it requires no
uniform bound on block counts and does not divide the kernel by an extra scale.
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

/-- The intrinsic frozen bound suffices for the actual iid upper localization.
The kinetic majorant depends on the sample size, as does the block count. -/
theorem physicalWeightedLocalizationFamily_of_intrinsicPointwiseBound
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
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      PopDataIntrinsic F φ q m hm ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < radius f)
      (c : Fin q → Fin m), (data f t hpert).p c t = pc f t c) :
    PhysicalWeightedLocalizationFamily F
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
      hA hB hμA hνB P X Y φ
      (fun c : Fin q → Fin m => ((blockW q m hm c : unitInterval) : ℝ)) pc radius := by
  intro f t hpert ε hε
  let D := data f t hpert
  haveI : ∀ c : Fin q → Fin m, IsProbabilityMeasure (D.α c) := D.hαprob
  haveI : ∀ c : Fin q → Fin m, IsProbabilityMeasure (D.β c) := D.hβprob
  let Cn : ℕ → ℝ := fun n => D.Cb *
    ((Nat.floor (((n + 1 : ℕ) : ℝ) * (1 / ((m ^ q : ℕ) : ℝ))) : ℕ) : ℝ) ^
      (2 / (q : ℝ)) * (q : ℝ)
  have hCn0 : ∀ n, 0 ≤ Cn n := by
    intro n
    exact mul_nonneg (mul_nonneg D.hCb0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (Nat.cast_nonneg q)
  have hq : 4 < q := by
    have hd : (6 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hdim
    have hqR : (4 : ℝ) < (q : ℝ) := by rw [D.hqdim]; linarith
    exact_mod_cast hqR
  have hrel : ∀ᶠ n in atTop, ∀ c ξ i j,
      D.cellS (canonicalX (M := M) n i ξ) = c →
      D.cellT (canonicalY (M := M) n j ξ) = c →
      |finslerTileKinetic F (fun i => canonicalX (M := M) n i ξ)
          (fun j => canonicalY (M := M) n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j -
        markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c)
          (D.kin c) (atlasMarkMap D.coordS D.labelS) (atlasMarkMap D.coordT D.labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ)| ≤
        2 * D.ε n * markedKineticKernel (q := q)
          (frozenMarkedRadius (blockW q m hm) n c) (D.kin c)
          (atlasMarkMap D.coordS D.labelS) (atlasMarkMap D.coordT D.labelT)
          (canonicalX (M := M) n i ξ) (canonicalY (M := M) n j ξ) := by
    filter_upwards [eventually_ge_atTop (m ^ q - 1)] with n hn
    exact D.hrel_guarded n hn
  have hmain := finsler_hupper_of_frozen_comparison_canonical
    (F := F) (hcomplete := hcomplete)
    (μ := physicalSourceProbability ωM ρ₀) (ν := physicalTargetProbability ωM ρ₁)
    (K := A ∪ B) (hK := hA.union hB)
    (hμ := hμA.mono fun x hx => Or.inl hx) (hν := hνB.mono fun y hy => Or.inr hy)
    (φ := φ) (hφ := hφ) (f := f) (t := t) (q := q) (hq := hq)
    (w := blockW q m hm) (hwsum := blockW_sum q m hm) (hwpos := blockW_pos q m hm)
    (A := Am) (C := Cm) (kin := D.kin) (g := D.g) (Cb := D.Cb) (G := D.G)
    (hCb0 := D.hCb0) (hG0 := D.hG0) (hkin := D.hkin) (hkin_bound := D.hkin_bound)
    (hg := D.hg) (hgb := D.hgb) (α := D.α) (β := D.β) (p := D.p) (hp := D.hp)
    (cellS := D.cellS) (hcellS := D.hcellS) (cellT := D.cellT) (hcellT := D.hcellT)
    (hmassS := D.hmassS) (hmassT := D.hmassT)
    (coordS := D.coordS) (hcoordS := D.hcoordS) (labelS := D.labelS) (hlabelS := D.hlabelS)
    (coordT := D.coordT) (hcoordT := D.hcoordT) (labelT := D.labelT) (hlabelT := D.hlabelT)
    (hcubeS := D.hcubeS) (hmarkLawS := D.hmarkLawS) (hindepS := D.hindepS)
    (hcubeT := D.hcubeT) (hmarkLawT := D.hmarkLawT) (hindepT := D.hindepT)
    (Cbnd := Cn) (Gbnd := D.Gbnd) (hCbnd0 := hCn0) (hGbnd0 := D.hGbnd0)
    (hCbnd := D.hCbnd_intrinsic) (hGbnd := D.hGbnd)
    (ε := D.ε) (B := D.Berr) (Gb := D.Gb) (Bnd := D.Bnd)
    (hε0 := D.hε0) (hB0 := D.hB0) (hGb0 := D.hGb0) (hBnd0 := D.hBnd0)
    (hF0 := D.hF0) (hrel := hrel) (hprobe := D.hprobe) (hG := D.hG)
    (hmodel_bound := D.hmodel_bound) (hδ := D.hδ)
  filter_upwards [hmain ε hε] with n hn
  have heq := integral_finslerSupportedPressure_eq_canonicalLaw (F := F) hcomplete
    (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
    (A ∪ B) (hA.union hB).measurableSet
    (hμA.mono fun x hx => Or.inl hx) (hνB.mono fun y hy => Or.inr hy)
    (P n) (X n) (Y n) (hX n) (hY n) (hXi n) (hYi n) (hXlaw n) (hYlaw n) (hXY n)
    φ hφ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t
  rw [heq]
  have hsum : (∑ c : Fin q → Fin m, ((blockW q m hm c : unitInterval) : ℝ) * D.p c t) =
      ∑ c : Fin q → Fin m, ((blockW q m hm c : unitInterval) : ℝ) * pc f t c := by
    exact Finset.sum_congr rfl fun c _ => congrArg
      (fun a : ℝ => ((blockW q m hm c : unitInterval) : ℝ) * a) (hpc f t hpert c)
  rw [hsum] at hn
  simpa only [D.hqdim] using hn

end OTSelector.Reconstruction
