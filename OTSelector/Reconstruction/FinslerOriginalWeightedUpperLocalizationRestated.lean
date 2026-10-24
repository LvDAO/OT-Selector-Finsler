import OTSelector.Reconstruction.FinslerOriginalIIDPressureUpperLocalization
import OTSelector.Reconstruction.FinslerOriginalWeightedUpperLocalizationData

/-!
# Literal restatement of the IID upper localization as weighted family data

This module closes the last noted gap of the hupper lane: the literal
binder-by-binder restatement of
'OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex.finsler_originalIID_pressure_upper_localization'
into 'PhysicalWeightedLocalizationFamily' with the block weights '1 / m^q'.

## Transcription

The localization theorem's binder telescope splits into

* the probe-independent sampling binders, transcribed verbatim as parameters of
  'physicalWeightedLocalizationFamily_of_popData': 'hcomplete', 'hdim', the
  ambient measure 'omegaM' with densities 'rho0' 'rho1' and their probability
  instances, compact supports 'A' 'B' with disjointness and a.e. membership, the
  sample space 'Omega', measures 'P' with probability instances, iid coordinate
  arrays 'X' 'Y' with measurability, independence, marginals and cross
  independence, and the 1-Lipschitz potential 'phi';
* the probe-dependent population binders, transcribed verbatim as the fields of
  'PopData' (parameterised by the probe 'f', the tilt 't', 'q', 'm' and the mark
  spaces 'Am' 'Cm'): the kinetic/probe kernels 'kin' 'g' with bounds 'Cb' 'G',
  measurability, domination and Lipschitz-type bounds, cell measures 'alpha'
  'beta' with probability proofs, the local limits 'p' and their Markov
  convergence 'hp', the cell maps 'cellS' 'cellT' with masses, coordinates and
  marks with cube/Haar laws, mark laws and independence, the frozen bounds
  'Cbnd' 'Gbnd', and the freezing/probe/sample approximation data
  'eps' 'Berr' 'Gb' 'Bnd' with their nonnegativities, positivity bound 'hF0',
  model comparison 'hrel', probe comparison 'hprobe', probe bound 'hG', frozen
  model bound 'hmodel_bound', the vanishing combined error 'hdelta' and the
  dimension identity 'hqdim'.

The single adaptation is the instantiation of the localization's abstract index
type and weights: 'iota := Fin q -> Fin m' and 'w := fun _ => 1 / m^q' (the def
'blockW'), for which 'hwsum' and 'hwpos' are proved once ('blockW_sum',
'blockW_pos'); no other binder is altered, and the localization's conclusion is
converted to the block weighted sum by the hypothesis 'hpc' identifying the
local limits 'p' with the family limits 'pc'.

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
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-! ## 1. The block weights -/

/-- The constant block weight '1 / m^q' as an element of the unit interval. -/
def unitBlock (q m : ℕ) (hm : 0 < m) : unitInterval :=
  ⟨1 / (((m ^ q : ℕ) : ℝ)), by
    have hNpos : (0 : ℝ) < ((m ^ q : ℕ) : ℝ) := by exact_mod_cast pow_pos hm q
    have hmpow : 0 < m ^ q := pow_pos hm q
    have hN1 : (1 : ℝ) ≤ ((m ^ q : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr hmpow
    exact ⟨div_nonneg zero_le_one hNpos.le, by rw [div_le_one hNpos]; exact hN1⟩⟩

/-- The block weight family on the block index set 'Fin q -> Fin m'. -/
def blockW (q m : ℕ) (hm : 0 < m) : (Fin q → Fin m) → unitInterval :=
  fun _ => unitBlock q m hm

/-- The block weights sum to one. -/
theorem blockW_sum (q m : ℕ) (hm : 0 < m) :
    (∑ c : Fin q → Fin m, ((blockW q m hm c : unitInterval) : ℝ)) = 1 := by
  have hterm : ∀ c : Fin q → Fin m,
      ((blockW q m hm c : unitInterval) : ℝ) = 1 / (((m ^ q : ℕ) : ℝ)) := fun c => rfl
  simp only [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
  simp only [Fintype.card_fin]
  have hNpos : (0 : ℝ) < ((m ^ q : ℕ) : ℝ) := by exact_mod_cast pow_pos hm q
  rw [nsmul_eq_mul]
  field_simp

/-- The block weights are positive. -/
theorem blockW_pos (q m : ℕ) (hm : 0 < m) :
    ∀ c : Fin q → Fin m, 0 < ((blockW q m hm c : unitInterval) : ℝ) := by
  intro c
  have hval : ((blockW q m hm c : unitInterval) : ℝ) = 1 / (((m ^ q : ℕ) : ℝ)) := rfl
  rw [hval]
  have hNpos : (0 : ℝ) < ((m ^ q : ℕ) : ℝ) := by exact_mod_cast pow_pos hm q
  exact div_pos one_pos hNpos

/-! ## 2. The probe-dependent population data -/

/-- **The probe-dependent population data** of the localization theorem,
transcribed verbatim (with the frozen marked radius taken at the block weight
'blockW q m hm', and the block index set 'Fin q -> Fin m'). -/
structure PopData
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
  /-- The frozen kinetic bound. -/
  Cbnd : ℝ
  /-- The frozen probe bound. -/
  Gbnd : ℝ
  hCbnd0 : 0 ≤ Cbnd
  hGbnd0 : 0 ≤ Gbnd
  hCbnd : ∀ (n : ℕ) (c : Fin q → Fin m) (x y : M),
    |markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (kin c)
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Cbnd
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
  hrel : ∀ n c ξ i j,
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

/-! ## 3. The family corollary -/

/-- **The weighted localization family from the population data.**

Literal restatement of 'finsler_originalIID_pressure_upper_localization' with the
block weights '1 / m^q': for every probe and tilt in the common interval, the
expected physical supported pressure is eventually at most the block weighted sum
of the local limits 'pc' plus 'eps'.

The named inputs are exactly the population data (transcribed in 'PopData' and in
the sampling binders of this theorem) plus the identification 'hpc' of the local
limits with 'pc'. -/
theorem physicalWeightedLocalizationFamily_of_popData
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
      PopData F φ q m hm ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < radius f)
      (c : Fin q → Fin m), (data f t hpert).p c t = pc f t c) :
    PhysicalWeightedLocalizationFamily F
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
      hA hB hμA hνB P X Y φ
      (fun c : Fin q → Fin m => ((blockW q m hm c : unitInterval) : ℝ)) pc radius := by
  intro f t hpert ε hε
  let D := data f t hpert
  haveI hα : ∀ c : Fin q → Fin m, IsProbabilityMeasure (D.α c) := D.hαprob
  haveI hβ : ∀ c : Fin q → Fin m, IsProbabilityMeasure (D.β c) := D.hβprob
  have hmain := finsler_originalIID_pressure_upper_localization
    (hcomplete := hcomplete) (hdim := hdim) (ωM := ωM) (ρ₀ := ρ₀) (ρ₁ := ρ₁)
    (hA := hA) (hB := hB) (hAB := hAB) (hμA := hμA) (hνB := hνB)
    (P := P) (X := X) (Y := Y) (hX := hX) (hY := hY) (hXi := hXi) (hYi := hYi)
    (hXlaw := hXlaw) (hYlaw := hYlaw) (hXY := hXY) (φ := φ) (hφ := hφ)
    (f := f) (t := t) (q := q) (w := blockW q m hm)
    (hwsum := blockW_sum q m hm) (hwpos := blockW_pos q m hm)
    (Am := Am) (Cm := Cm) (kin := D.kin) (g := D.g) (Cb := D.Cb) (G := D.G)
    (hCb0 := D.hCb0) (hG0 := D.hG0) (hkin := D.hkin) (hkin_bound := D.hkin_bound)
    (hg := D.hg) (hgb := D.hgb) (α := D.α) (β := D.β) (p := D.p) (hp := D.hp)
    (cellS := D.cellS) (hcellS := D.hcellS) (cellT := D.cellT) (hcellT := D.hcellT)
    (hmassS := D.hmassS) (hmassT := D.hmassT)
    (coordS := D.coordS) (hcoordS := D.hcoordS) (labelS := D.labelS) (hlabelS := D.hlabelS)
    (coordT := D.coordT) (hcoordT := D.hcoordT) (labelT := D.labelT) (hlabelT := D.hlabelT)
    (hcubeS := D.hcubeS) (hmarkLawS := D.hmarkLawS) (hindepS := D.hindepS)
    (hcubeT := D.hcubeT) (hmarkLawT := D.hmarkLawT) (hindepT := D.hindepT)
    (Cbnd := D.Cbnd) (Gbnd := D.Gbnd) (hCbnd0 := D.hCbnd0) (hGbnd0 := D.hGbnd0)
    (hCbnd := D.hCbnd) (hGbnd := D.hGbnd)
    (ε := D.ε) (Berr := D.Berr) (Gb := D.Gb) (Bnd := D.Bnd)
    (hε0 := D.hε0) (hB0 := D.hB0) (hGb0 := D.hGb0) (hBnd0 := D.hBnd0)
    (hF0 := D.hF0) (hrel := D.hrel) (hprobe := D.hprobe) (hG := D.hG)
    (hmodel_bound := D.hmodel_bound) (hδ := D.hδ) (hqdim := D.hqdim)
  filter_upwards [hmain ε hε] with n hn
  have hsum : (∑ c : Fin q → Fin m,
      ((blockW q m hm c : unitInterval) : ℝ) * D.p c t) =
      ∑ c : Fin q → Fin m, (1 / (((m ^ q : ℕ) : ℝ))) * pc f t c := by
    refine Finset.sum_congr rfl fun c _ => ?_
    have hcoe : ((blockW q m hm c : unitInterval) : ℝ) = 1 / (((m ^ q : ℕ) : ℝ)) := rfl
    rw [hcoe, hpc f t hpert c]
  rwa [hsum] at hn

end OTSelector.Reconstruction
