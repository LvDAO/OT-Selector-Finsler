import OTSelector.Limit.FinslerAdditiveHblockAssembly
import OTSelector.Probability.FinslerMarkedAtlasIdentification

/-!
# The frozen-block bridge and the `hupper` with the count law discharged

`OTSelector.Limit.FinslerAdditiveHblockAssembly` reduces the additive `hblock`
to an explicit hypothesis `hmodel_law`:
the expected normalized *fixed-label-array* frozen block equals
`modelBlockSum/(n+1)`.  The law identity
`integral_frozenModelTileBlock_eq_modelBlockSum_of_atlas` proves the same
statement for the *law-version* frozen block of
`OTSelector.Probability.frozenModelTileBlock`.

This module:

1. Proves the permutation-invariance bridge between the two frozen blocks.
   The fixed-label-array block uses the enumeration `blockEmbeddingS/T`
   (`Finset.equivFin` of `blockFinset`), while the law-version uses
   `tileEmbedding` (`tileEquiv`, built from `Fintype.equivFinOfCardEq` of
   `tileIndex`).  Both enumerate the same tile index set, and
   `patternCount = blockSizeS`, so `PartialMatching.maxCardValue_reindex`
   identifies the two values.

2. Uses the bridge to derive `hmodel_law` and hence prove
   `finslerExpectationUpperBound_of_frozen_comparison'` and
   `finsler_hupper_of_frozen_comparison'`, in which `hmodel_law` is discharged
   by `integral_frozenModelTileBlock_eq_modelBlockSum_of_atlas` (the atlas
   pushforward reduced to the cube law, the mark law and independence).

The remaining hypotheses of the primed theorems are exactly the geometric
per-edge comparison, the atlas coordinate facts, boundedness/integrability of
the marked kernels and of the block functions, and the vanishing assembled
additive error.

No `sorry`, `admit` or added axiom occurs.
-/

open MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Probability
open scoped BigOperators ENNReal NNReal Topology ContDiff BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace OTSelector.Probability

variable {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The two enumerations of a tile -/

/-- The position of a tile index in the `Finset.equivFin` enumeration of the
block finset.  This is the inverse of `blockEmbeddingS` composed with
`tileEmbedding`. -/
noncomputable def blockIndexOfTile (u : Fin m → ι) (c : ι) (j : Fin (patternCount u c)) :
    Fin (blockSizeS u c) :=
  Finset.equivFin (blockFinset u c)
    ⟨tileEmbedding u c j, by
      have h := (tileEquiv u c (fun _ => patternCount u c) rfl j).2
      simpa only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and, tileEmbedding]
        using h⟩

/-- **The two enumerations agree.**  The `blockEmbeddingS` index at the position
`blockIndexOfTile` is exactly the `tileEmbedding` index. -/
theorem blockEmbeddingS_blockIndexOfTile (u : Fin m → ι) (c : ι)
    (j : Fin (patternCount u c)) :
    blockEmbeddingS u c (blockIndexOfTile u c j) = tileEmbedding u c j := by
  simp only [blockIndexOfTile, blockEmbeddingS, Equiv.symm_apply_apply]

/-- The canonical tile enumeration is injective. -/
theorem tileEmbedding_injective (u : Fin m → ι) (c : ι) :
    Function.Injective (tileEmbedding u c) := by
  intro i j h
  have h' : tileEquiv u c (fun _ => patternCount u c) rfl i =
      tileEquiv u c (fun _ => patternCount u c) rfl j := by
    apply Subtype.ext
    simpa only [tileEmbedding] using h
  exact (tileEquiv u c (fun _ => patternCount u c) rfl).injective h'

/-- `blockIndexOfTile` is injective. -/
theorem blockIndexOfTile_injective (u : Fin m → ι) (c : ι) :
    Function.Injective (blockIndexOfTile u c) := by
  intro j₁ j₂ h
  have h' : blockEmbeddingS u c (blockIndexOfTile u c j₁) =
      blockEmbeddingS u c (blockIndexOfTile u c j₂) := by rw [h]
  rw [blockEmbeddingS_blockIndexOfTile, blockEmbeddingS_blockIndexOfTile] at h'
  exact tileEmbedding_injective u c h'

/-- The equivalence between the tile-pattern index type and the block index type
induced by the two enumerations. -/
noncomputable def blockTileEquiv (u : Fin m → ι) (c : ι) :
    Fin (patternCount u c) ≃ Fin (blockSizeS u c) :=
  Equiv.ofBijective (blockIndexOfTile u c)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨blockIndexOfTile_injective u c, by
        rw [Fintype.card_fin, Fintype.card_fin]
        rfl⟩)

/-- The equivalence property in the form used by `maxCardValue_reindex`. -/
theorem blockEmbeddingS_blockTileEquiv (u : Fin m → ι) (c : ι)
    (j : Fin (patternCount u c)) :
    blockEmbeddingS u c (blockTileEquiv u c j) = tileEmbedding u c j :=
  blockEmbeddingS_blockIndexOfTile u c j

/-! ## The bridge between the two frozen blocks -/

/-- **Permutation-invariance bridge between the fixed-label-array and the
law-version frozen tile blocks.**

The fixed-label-array block (`OTSelector.frozenModelTileBlock`) enumerates the
tile by `blockEmbeddingS/T`, the law-version block
(`OTSelector.Probability.frozenModelTileBlock`) by `tileEmbedding`.  Both
enumerations run over the same tile index set, so the maximum-cardinality value
is unchanged (`PartialMatching.maxCardValue_reindex`). -/
theorem frozenModelTileBlock_bridge {n : ℕ} {Xs Yt : Type*}
    (labS : Xs → ι) (labT : Yt → ι)
    (frozenCost modelProbe : Xs → Yt → ℝ) (t : ℝ) (c : ι)
    (p : (Fin (n + 1) → Xs) × (Fin (n + 1) → Yt)) :
    OTSelector.frozenModelTileBlock (fun i => labS (p.1 i)) (fun j => labT (p.2 j))
      (fun i j => frozenCost (p.1 i) (p.2 j))
      (fun i j => modelProbe (p.1 i) (p.2 j)) t c
    = OTSelector.Probability.frozenModelTileBlock labS labT frozenCost modelProbe t c p := by
  classical
  set u : Fin (n + 1) → ι := fun i => labS (p.1 i) with hu
  set v : Fin (n + 1) → ι := fun j => labT (p.2 j) with hv
  set D : Fin (n + 1) → Fin (n + 1) → ℝ :=
    fun i j => frozenCost (p.1 i) (p.2 j) + t * modelProbe (p.1 i) (p.2 j) with hD
  have hL : OTSelector.frozenModelTileBlock u v
      (fun i j => frozenCost (p.1 i) (p.2 j))
      (fun i j => modelProbe (p.1 i) (p.2 j)) t c =
      PartialMatching.maxCardValue
        (fun i : Fin (blockSizeS u c) => fun j : Fin (blockSizeT v c) =>
          D (blockEmbeddingS u c i) (blockEmbeddingT v c j)) := rfl
  have hR : OTSelector.Probability.frozenModelTileBlock labS labT frozenCost modelProbe t c p =
      PartialMatching.maxCardValue
        (fun i : Fin (patternCount u c) => fun j : Fin (patternCount v c) =>
          D (tileEmbedding u c i) (tileEmbedding v c j)) := rfl
  rw [hL, hR]
  have hre := PartialMatching.maxCardValue_reindex
    (c := fun i : Fin (patternCount u c) => fun j : Fin (patternCount v c) =>
      D (tileEmbedding u c i) (tileEmbedding v c j))
    (e := blockTileEquiv u c) (f := blockTileEquiv v c)
  rw [← hre]
  apply congrArg PartialMatching.maxCardValue
  funext i j
  have h1 : tileEmbedding u c ((blockTileEquiv u c).symm i) = blockEmbeddingS u c i := by
    have h := blockEmbeddingS_blockTileEquiv u c ((blockTileEquiv u c).symm i)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have h2 : tileEmbedding v c ((blockTileEquiv v c).symm j) = blockEmbeddingT v c j := by
    have h := blockEmbeddingS_blockTileEquiv v c ((blockTileEquiv v c).symm j)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  rw [h1, h2]

/-! ## The fixed-array frozen block at the marked atlas kernels -/

variable {Xs Yt : Type*} [MeasurableSpace Xs] [MeasurableSpace Yt]
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- **The fixed-label-array frozen block at the marked atlas kernels has the
model-block expectation.**

This is `integral_frozenModelTileBlock_eq_modelBlockSum_of_atlas` transported
from the law-version frozen block to the fixed-label-array frozen block by
`frozenModelTileBlock_bridge`.  The sample size is `n + 1`, the shape in which
the frozen comparison of `Reconstruction/FinslerTileBlockFrozenComparison.lean`
is stated. -/
theorem integral_frozenModelTileBlock_fixedArray_eq_modelBlockSum_of_atlas
    {q : ℕ} {t : ℝ} {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (μs : Measure Xs) [IsProbabilityMeasure μs]
    (μt : Measure Yt) [IsProbabilityMeasure μt]
    (cellS : Xs → ι) (hcellS : Measurable cellS)
    (cellT : Yt → ι) (hcellT : Measurable cellT)
    (c : ι) (w : unitInterval) (hwpos : 0 < (w : ℝ))
    (hws : μs (cellS ⁻¹' {c}) = ENNReal.ofReal (w : ℝ))
    (hwt : μt (cellT ⁻¹' {c}) = ENNReal.ofReal (w : ℝ))
    (coordS : Xs → Fin q → ℝ) (hcoordS : Measurable coordS)
    (labelS : Xs → A) (hlabelS : Measurable labelS)
    (coordT : Yt → Fin q → ℝ) (hcoordT : Measurable coordT)
    (labelT : Yt → B) (hlabelT : Measurable labelT)
    (hcubeS : ((μs (cellS ⁻¹' {c}))⁻¹ • μs.restrict (cellS ⁻¹' {c})).map coordS =
      cubeMeasure (Fin q) 1)
    (hmarkLawS : ((μs (cellS ⁻¹' {c}))⁻¹ • μs.restrict (cellS ⁻¹' {c})).map labelS = α)
    (hindepS : IndepFun coordS labelS
      ((μs (cellS ⁻¹' {c}))⁻¹ • μs.restrict (cellS ⁻¹' {c})))
    (hcubeT : ((μt (cellT ⁻¹' {c}))⁻¹ • μt.restrict (cellT ⁻¹' {c})).map coordT =
      cubeMeasure (Fin q) 1)
    (hmarkLawT : ((μt (cellT ⁻¹' {c}))⁻¹ • μt.restrict (cellT ⁻¹' {c})).map labelT = β)
    (hindepT : IndepFun coordT labelT
      ((μt (cellT ⁻¹' {c}))⁻¹ • μt.restrict (cellT ⁻¹' {c})))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin (n + 1) → Ω → Xs) (Y : Fin (n + 1) → Ω → Yt)
    (hmeas : Measurable fun ξ : Ω => (fun i => X i ξ, fun j => Y j ξ))
    (hlaw : P.map (fun ξ : Ω => (fun i => X i ξ, fun j => Y j ξ)) =
      twoColourLaw μs μt (n + 1))
    {Cbnd Gbnd : ℝ} (hCbnd0 : 0 ≤ Cbnd) (hGbnd0 : 0 ≤ Gbnd)
    (hCbnd : ∀ x y, |markedKineticKernel (q := q)
      ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Cbnd)
    (hGbnd : ∀ x y, |markedProbeKernel g
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Gbnd) :
    (∫ ξ, OTSelector.frozenModelTileBlock
        (fun i => cellS (X i ξ)) (fun j => cellT (Y j ξ))
        (fun i j => markedKineticKernel (q := q)
          ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X i ξ) (Y j ξ))
        (fun i j => markedProbeKernel g
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X i ξ) (Y j ξ))
        t c ∂P)
      = modelBlockSum q t kin g α β w (n + 1) := by
  classical
  have hbridge : (∫ ξ, OTSelector.frozenModelTileBlock
        (fun i => cellS (X i ξ)) (fun j => cellT (Y j ξ))
        (fun i j => markedKineticKernel (q := q)
          ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X i ξ) (Y j ξ))
        (fun i j => markedProbeKernel g
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X i ξ) (Y j ξ))
        t c ∂P)
      = ∫ ξ, OTSelector.Probability.frozenModelTileBlock cellS cellT
          (markedKineticKernel (q := q)
            ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT))
          (markedProbeKernel g (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT))
          t c (fun i => X i ξ, fun j => Y j ξ) ∂P := by
    apply integral_congr_ae
    filter_upwards with ξ
    exact frozenModelTileBlock_bridge cellS cellT
      (markedKineticKernel (q := q)
        ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT))
      (markedProbeKernel g (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT))
      t c (fun i => X i ξ, fun j => Y j ξ)
  rw [hbridge]
  exact integral_frozenModelTileBlock_eq_modelBlockSum_of_atlas hkin hg α β μs μt
    cellS hcellS cellT hcellT c (n + 1) w hwpos hws hwt
    coordS hcoordS labelS hlabelS coordT hcoordT labelT hlabelT
    hcubeS hmarkLawS hindepS hcubeT hmarkLawT hindepT P X Y hmeas hlaw
    hCbnd0 hGbnd0 hCbnd hGbnd

/-- **The `hmodel_law` shape of the law identity.**

For arbitrary block label arrays `U ξ`, `V ξ` and frozen matrices `Fcost ξ`,
`Mprobe ξ` which agree pointwise with the label maps `cellS`, `cellT` and the
marked atlas kernels, the expected normalized fixed-array frozen block at sample
size `n + 1` is at most `modelBlockSum / (n + 1)`.  This is exactly the
`hmodel_law` hypothesis of the additive assembly, with the law identity proved
by `integral_frozenModelTileBlock_fixedArray_eq_modelBlockSum_of_atlas`. -/
theorem frozenModelTileBlock_integral_div_le_modelBlockSum_of_atlas
    {q : ℕ} {t : ℝ} {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (μs : Measure Xs) [IsProbabilityMeasure μs]
    (μt : Measure Yt) [IsProbabilityMeasure μt]
    (cellS : Xs → ι) (hcellS : Measurable cellS)
    (cellT : Yt → ι) (hcellT : Measurable cellT)
    (c : ι) (w : unitInterval) (hwpos : 0 < (w : ℝ))
    (hws : μs (cellS ⁻¹' {c}) = ENNReal.ofReal (w : ℝ))
    (hwt : μt (cellT ⁻¹' {c}) = ENNReal.ofReal (w : ℝ))
    (coordS : Xs → Fin q → ℝ) (hcoordS : Measurable coordS)
    (labelS : Xs → A) (hlabelS : Measurable labelS)
    (coordT : Yt → Fin q → ℝ) (hcoordT : Measurable coordT)
    (labelT : Yt → B) (hlabelT : Measurable labelT)
    (hcubeS : ((μs (cellS ⁻¹' {c}))⁻¹ • μs.restrict (cellS ⁻¹' {c})).map coordS =
      cubeMeasure (Fin q) 1)
    (hmarkLawS : ((μs (cellS ⁻¹' {c}))⁻¹ • μs.restrict (cellS ⁻¹' {c})).map labelS = α)
    (hindepS : IndepFun coordS labelS
      ((μs (cellS ⁻¹' {c}))⁻¹ • μs.restrict (cellS ⁻¹' {c})))
    (hcubeT : ((μt (cellT ⁻¹' {c}))⁻¹ • μt.restrict (cellT ⁻¹' {c})).map coordT =
      cubeMeasure (Fin q) 1)
    (hmarkLawT : ((μt (cellT ⁻¹' {c}))⁻¹ • μt.restrict (cellT ⁻¹' {c})).map labelT = β)
    (hindepT : IndepFun coordT labelT
      ((μt (cellT ⁻¹' {c}))⁻¹ • μt.restrict (cellT ⁻¹' {c})))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin (n + 1) → Ω → Xs) (Y : Fin (n + 1) → Ω → Yt)
    (hmeas : Measurable fun ξ : Ω => (fun i => X i ξ, fun j => Y j ξ))
    (hlaw : P.map (fun ξ : Ω => (fun i => X i ξ, fun j => Y j ξ)) =
      twoColourLaw μs μt (n + 1))
    {Cbnd Gbnd : ℝ} (hCbnd0 : 0 ≤ Cbnd) (hGbnd0 : 0 ≤ Gbnd)
    (hCbnd : ∀ x y, |markedKineticKernel (q := q)
      ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Cbnd)
    (hGbnd : ∀ x y, |markedProbeKernel g
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Gbnd)
    (U V : Ω → Fin (n + 1) → ι)
    (Fcost Mprobe : Ω → Fin (n + 1) → Fin (n + 1) → ℝ)
    (hU : ∀ ξ, U ξ = fun i => cellS (X i ξ))
    (hV : ∀ ξ, V ξ = fun j => cellT (Y j ξ))
    (hF : ∀ ξ, Fcost ξ = fun i j => markedKineticKernel (q := q)
      ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X i ξ) (Y j ξ))
    (hM : ∀ ξ, Mprobe ξ = fun i j => markedProbeKernel g
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X i ξ) (Y j ξ)) :
    (∫ ξ, OTSelector.frozenModelTileBlock (U ξ) (V ξ) (Fcost ξ) (Mprobe ξ) t c
      / (((n + 1 : ℕ) : ℝ)) ∂P) ≤
      modelBlockSum q t kin g α β w (n + 1) / (((n + 1 : ℕ) : ℝ)) := by
  classical
  have hcongr : (∫ ξ, OTSelector.frozenModelTileBlock (U ξ) (V ξ) (Fcost ξ) (Mprobe ξ)
        t c ∂P)
      = ∫ ξ, OTSelector.frozenModelTileBlock
          (fun i => cellS (X i ξ)) (fun j => cellT (Y j ξ))
          (fun i j => markedKineticKernel (q := q)
            ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X i ξ) (Y j ξ))
          (fun i j => markedProbeKernel g
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X i ξ) (Y j ξ))
          t c ∂P := by
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hU ξ, hV ξ, hF ξ, hM ξ]
  rw [integral_div, hcongr]
  rw [integral_frozenModelTileBlock_fixedArray_eq_modelBlockSum_of_atlas hkin hg α β μs μt
    cellS hcellS cellT hcellT c w hwpos hws hwt
    coordS hcoordS labelS hlabelS coordT hcoordT labelT hlabelT
    hcubeS hmarkLawS hindepS hcubeT hmarkLawT hindepT P X Y hmeas hlaw
    hCbnd0 hGbnd0 hCbnd hGbnd]

end OTSelector.Probability

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- The marked kinetic radius of scale `n` at the tile weight `w c`, namely
`⌊(n + 1) * (w c)⌋` as a real number.  This is the radius at which the marked
kinetic kernel is evaluated in `integral_frozenModelTileBlock_eq_modelBlockSum_of_atlas`. -/
noncomputable def frozenMarkedRadius {ι : Type*} (w : ι → unitInterval) (n : ℕ) (c : ι) : ℝ :=
  ((Nat.floor (((n + 1 : ℕ) : ℝ) * (w c : ℝ)) : ℕ) : ℝ)

/-- **The additive expectation upper bound with the frozen law identity
discharged.**

This is `finslerExpectationUpperBound_of_frozen_comparison` with

* `blockS`, `blockT` specialized to the label maps `cellS ∘ X`, `cellT ∘ Y`;
* `frozenCost`, `modelProbe` specialized to the marked atlas kernels
  `markedKineticKernel` and `markedProbeKernel` built from the atlas maps
  `atlasMarkMap coordS labelS`, `atlasMarkMap coordT labelT`;
* the law identity `hmodel_law` derived from
  `integral_frozenModelTileBlock_fixedArray_eq_modelBlockSum_of_atlas` rather
  than assumed.

The remaining probabilistic input is the joint sample law `hlaw`; everything
else is the geometric per-edge comparison, the atlas coordinate facts, the
kernel bounds, integrability and the vanishing additive error. -/
theorem finslerExpectationUpperBound_of_frozen_comparison'
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hlaw : ∀ n, (P n).map (fun ξ : Ω n => (fun i => X n i ξ, fun j => Y n j ξ)) =
      twoColourLaw (μ : Measure M) (ν : Measure M) (n + 1))
    (φ : M → ℝ)
    (hφ : let _instUpperPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (q : ℕ) (hq : 4 < q) {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (w : ι → unitInterval) (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
    {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    {kin : ι → A → C → (Fin q → ℝ) → ℝ} {g : ι → A → C → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × C => kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure A) (β : ι → Measure C)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ (c : ι) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A C (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (cellS : M → ι) (hcellS : Measurable cellS)
    (cellT : M → ι) (hcellT : Measurable cellT)
    (hmassS : ∀ c, (μ : Measure M) (cellS ⁻¹' {c}) = ENNReal.ofReal (w c : ℝ))
    (hmassT : ∀ c, (ν : Measure M) (cellT ⁻¹' {c}) = ENNReal.ofReal (w c : ℝ))
    (coordS : M → Fin q → ℝ) (hcoordS : Measurable coordS)
    (labelS : M → A) (hlabelS : Measurable labelS)
    (coordT : M → Fin q → ℝ) (hcoordT : Measurable coordT)
    (labelT : M → C) (hlabelT : Measurable labelT)
    (hcubeS : ∀ c, (((μ : Measure M) (cellS ⁻¹' {c}))⁻¹ •
      (μ : Measure M).restrict (cellS ⁻¹' {c})).map coordS = cubeMeasure (Fin q) 1)
    (hmarkLawS : ∀ c, (((μ : Measure M) (cellS ⁻¹' {c}))⁻¹ •
      (μ : Measure M).restrict (cellS ⁻¹' {c})).map labelS = α c)
    (hindepS : ∀ c, IndepFun coordS labelS
      (((μ : Measure M) (cellS ⁻¹' {c}))⁻¹ •
        (μ : Measure M).restrict (cellS ⁻¹' {c})))
    (hcubeT : ∀ c, (((ν : Measure M) (cellT ⁻¹' {c}))⁻¹ •
      (ν : Measure M).restrict (cellT ⁻¹' {c})).map coordT = cubeMeasure (Fin q) 1)
    (hmarkLawT : ∀ c, (((ν : Measure M) (cellT ⁻¹' {c}))⁻¹ •
      (ν : Measure M).restrict (cellT ⁻¹' {c})).map labelT = β c)
    (hindepT : ∀ c, IndepFun coordT labelT
      (((ν : Measure M) (cellT ⁻¹' {c}))⁻¹ •
        (ν : Measure M).restrict (cellT ⁻¹' {c})))
    {Cbnd : ℕ → ℝ} {Gbnd : ℝ} (hCbnd0 : ∀ n, 0 ≤ Cbnd n) (hGbnd0 : 0 ≤ Gbnd)
    (hCbnd : ∀ (n : ℕ) (c : ι) (x y : M),
      |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Cbnd n)
    (hGbnd : ∀ (c : ι) (x y : M),
      |markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        x y| ≤ Gbnd)
    (ε B Gb Bnd : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n) (hB0 : ∀ n, 0 ≤ B n) (hGb0 : ∀ n, 0 ≤ Gb n)
    (hBnd0 : ∀ n, 0 ≤ Bnd n)
    (hF0 : ∀ n c ξ i j, cellS (X n i ξ) = c → cellT (Y n j ξ) = c →
      0 ≤ markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
    (hrel : ∀ᶠ n in atTop, ∀ c ξ i j, cellS (X n i ξ) = c → cellT (Y n j ξ) = c →
      |finslerTileKinetic F (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j -
          markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ)| ≤
        2 * ε n * markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
    (hprobe : ∀ n c ξ i j, cellS (X n i ξ) = c → cellT (Y n j ξ) = c →
      |finslerTileProbe μ ν K hK.measurableSet hμ hν
          (fun i => X n i ξ) (fun j => Y n j ξ) f i j -
          markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
            (X n i ξ) (Y n j ξ)| ≤ B n)
    (hG : ∀ n c ξ i j, cellS (X n i ξ) = c → cellT (Y n j ξ) = c →
      |markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        (X n i ξ) (Y n j ξ)| ≤ Gb n)
    (hintBlock : ∀ n c, Integrable (fun ξ =>
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (fun i ω' => cellS (X n i ω')) (fun j ω' => cellT (Y n j ω')) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ) (P n))
    (hintModel : ∀ n c, Integrable (fun ξ =>
      frozenModelTileBlock (fun i => cellS (X n i ξ)) (fun j => cellT (Y n j ξ))
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
        t c / ((n + 1 : ℕ) : ℝ)) (P n))
    (hmodel_bound : ∀ n c, (∫ ξ,
      frozenModelTileBlock (fun i => cellS (X n i ξ)) (fun j => cellT (Y n j ξ))
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
        t c / ((n + 1 : ℕ) : ℝ) ∂P n) ≤ Bnd n)
    (hintCount : ∀ n c, Integrable (fun ξ =>
      |tileSourceCount (fun i ω' => cellS (X n i ω')) c ξ -
        tileTargetCount (fun j ω' => cellT (Y n j ω')) c ξ|) (P n))
    (hcount : ∀ n c, ∫ ξ,
      |tileSourceCount (fun i ω' => cellS (X n i ω')) c ξ -
        tileTargetCount (fun j ω' => cellT (Y n j ω')) c ξ| ∂P n ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ)))
    (hδ : Tendsto (fun n =>
      2 * ε n * Bnd n + (|t| * B n + 2 * ε n * (|t| * Gb n))) atTop (𝓝 0)) :
    ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
        (∑ c, (w c : ℝ) * p c t) + ε' := by
  classical
  -- Measurability of the joint physical sample map.
  have hmeas : ∀ n, Measurable fun ξ : Ω n => (fun i => X n i ξ, fun j => Y n j ξ) := by
    intro n
    exact (measurable_pi_iff.mpr (fun i => hX n i)).prodMk
      (measurable_pi_iff.mpr (fun j => hY n j))
  -- The frozen law identity uses only the bound at this sample size.
  have hmodel_law : ∀ n c, (∫ ξ,
      frozenModelTileBlock (fun i => cellS (X n i ξ)) (fun j => cellT (Y n j ξ))
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
        t c / ((n + 1 : ℕ) : ℝ) ∂P n) ≤
      modelBlockSum q t (kin c) (g c) (α c) (β c) (w c) (n + 1) /
        ((n + 1 : ℕ) : ℝ) := by
    intro n c
    exact frozenModelTileBlock_integral_div_le_modelBlockSum_of_atlas
      (q := q) (t := t) (n := n) (Ω := Ω n)
      (kin := kin c) (g := g c) (hkin := hkin c) (hg := hg c)
      (α := α c) (β := β c) (μs := (μ : Measure M)) (μt := (ν : Measure M))
      (cellS := cellS) (hcellS := hcellS) (cellT := cellT) (hcellT := hcellT)
      (c := c) (w := w c) (hwpos := hwpos c) (hws := hmassS c) (hwt := hmassT c)
      (coordS := coordS) (hcoordS := hcoordS) (labelS := labelS) (hlabelS := hlabelS)
      (coordT := coordT) (hcoordT := hcoordT) (labelT := labelT) (hlabelT := hlabelT)
      (hcubeS := hcubeS c) (hmarkLawS := hmarkLawS c) (hindepS := hindepS c)
      (hcubeT := hcubeT c) (hmarkLawT := hmarkLawT c) (hindepT := hindepT c)
      (P := P n) (X := X n) (Y := Y n) (hmeas := hmeas n) (hlaw := hlaw n)
      (Cbnd := Cbnd n) (Gbnd := Gbnd) (hCbnd0 := hCbnd0 n) (hGbnd0 := hGbnd0)
      (hCbnd := hCbnd n c) (hGbnd := hGbnd c)
      (U := fun ξ => fun i => cellS (X n i ξ))
      (V := fun ξ => fun j => cellT (Y n j ξ))
      (Fcost := fun ξ => fun i j => markedKineticKernel (q := q)
        (frozenMarkedRadius w n c) (kin c) (atlasMarkMap coordS labelS)
        (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
      (Mprobe := fun ξ => fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
        (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
      (hU := fun ξ => rfl) (hV := fun ξ => rfl) (hF := fun ξ => rfl) (hM := fun ξ => rfl)
  exact finslerExpectationUpperBound_of_frozen_comparison
    (F := F) hcomplete μ ν K hK hμ hν P X Y hX hY hXlaw hYlaw φ hφ f t q hq
    w hwsum hwpos hCb0 hG0 hkin hkin_bound hg hgb α β p hp
    (fun n i ξ => cellS (X n i ξ)) (fun n j ξ => cellT (Y n j ξ))
    (fun n c ξ i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
    (fun n c ξ i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
      (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
    ε B Gb Bnd hε0 hB0 hGb0 hBnd0 hF0 hrel hprobe hG hintBlock hintModel hmodel_law
    hmodel_bound hintCount hcount hδ

/-- **The `hupper` clause with the frozen law identity discharged.**

If the target pressure agrees with the weighted sum of the local marked pressure
limits at the fixed probe and tilt, the expectation upper bound of
`finslerExpectationUpperBound_of_frozen_comparison'` is exactly the `hupper`
clause of `exists_finsler_pressure_producer_of_squeeze`, with `hmodel_law`
derived from the atlas law identity. The raw frozen-kernel bound may depend on the
sample size; it is used only to justify each fixed-size integral. -/
theorem finsler_hupper_of_frozen_comparison'
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hlaw : ∀ n, (P n).map (fun ξ : Ω n => (fun i => X n i ξ, fun j => Y n j ξ)) =
      twoColourLaw (μ : Measure M) (ν : Measure M) (n + 1))
    (φ : M → ℝ)
    (hφ : let _instUpperPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (q : ℕ) (hq : 4 < q) {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (w : ι → unitInterval) (hwsum : ∑ c, (w c : ℝ) = 1) (hwpos : ∀ c, 0 < (w c : ℝ))
    {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    {kin : ι → A → C → (Fin q → ℝ) → ℝ} {g : ι → A → C → ℝ}
    {Cb G : ℝ} (hCb0 : 0 ≤ Cb) (hG0 : 0 ≤ G)
    (hkin : ∀ c, Measurable (Function.uncurry (fun p : A × C => kin c p.1 p.2)))
    (hkin_bound : ∀ c a b v, |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (hg : ∀ c, Measurable (Function.uncurry (g c)))
    (hgb : ∀ c a b, |g c a b| ≤ G)
    (α : ι → Measure A) (β : ι → Measure C)
    [∀ c, IsProbabilityMeasure (α c)] [∀ c, IsProbabilityMeasure (β c)]
    (p : ι → ℝ → ℝ)
    (hp : ∀ (c : ι) (t : ℝ), Tendsto
      (fun R => markedScalePressure q A C (α c) (β c) (kin c) (g c) R t)
      atTop (𝓝 (p c t)))
    (cellS : M → ι) (hcellS : Measurable cellS)
    (cellT : M → ι) (hcellT : Measurable cellT)
    (hmassS : ∀ c, (μ : Measure M) (cellS ⁻¹' {c}) = ENNReal.ofReal (w c : ℝ))
    (hmassT : ∀ c, (ν : Measure M) (cellT ⁻¹' {c}) = ENNReal.ofReal (w c : ℝ))
    (coordS : M → Fin q → ℝ) (hcoordS : Measurable coordS)
    (labelS : M → A) (hlabelS : Measurable labelS)
    (coordT : M → Fin q → ℝ) (hcoordT : Measurable coordT)
    (labelT : M → C) (hlabelT : Measurable labelT)
    (hcubeS : ∀ c, (((μ : Measure M) (cellS ⁻¹' {c}))⁻¹ •
      (μ : Measure M).restrict (cellS ⁻¹' {c})).map coordS = cubeMeasure (Fin q) 1)
    (hmarkLawS : ∀ c, (((μ : Measure M) (cellS ⁻¹' {c}))⁻¹ •
      (μ : Measure M).restrict (cellS ⁻¹' {c})).map labelS = α c)
    (hindepS : ∀ c, IndepFun coordS labelS
      (((μ : Measure M) (cellS ⁻¹' {c}))⁻¹ •
        (μ : Measure M).restrict (cellS ⁻¹' {c})))
    (hcubeT : ∀ c, (((ν : Measure M) (cellT ⁻¹' {c}))⁻¹ •
      (ν : Measure M).restrict (cellT ⁻¹' {c})).map coordT = cubeMeasure (Fin q) 1)
    (hmarkLawT : ∀ c, (((ν : Measure M) (cellT ⁻¹' {c}))⁻¹ •
      (ν : Measure M).restrict (cellT ⁻¹' {c})).map labelT = β c)
    (hindepT : ∀ c, IndepFun coordT labelT
      (((ν : Measure M) (cellT ⁻¹' {c}))⁻¹ •
        (ν : Measure M).restrict (cellT ⁻¹' {c})))
    {Cbnd : ℕ → ℝ} {Gbnd : ℝ} (hCbnd0 : ∀ n, 0 ≤ Cbnd n) (hGbnd0 : 0 ≤ Gbnd)
    (hCbnd : ∀ (n : ℕ) (c : ι) (x y : M),
      |markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ Cbnd n)
    (hGbnd : ∀ (c : ι) (x y : M),
      |markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        x y| ≤ Gbnd)
    (ε B Gb Bnd : ℕ → ℝ)
    (hε0 : ∀ n, 0 ≤ ε n) (hB0 : ∀ n, 0 ≤ B n) (hGb0 : ∀ n, 0 ≤ Gb n)
    (hBnd0 : ∀ n, 0 ≤ Bnd n)
    (hF0 : ∀ n c ξ i j, cellS (X n i ξ) = c → cellT (Y n j ξ) = c →
      0 ≤ markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
    (hrel : ∀ᶠ n in atTop, ∀ c ξ i j, cellS (X n i ξ) = c → cellT (Y n j ξ) = c →
      |finslerTileKinetic F (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) i j -
          markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ)| ≤
        2 * ε n * markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
            (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
    (hprobe : ∀ n c ξ i j, cellS (X n i ξ) = c → cellT (Y n j ξ) = c →
      |finslerTileProbe μ ν K hK.measurableSet hμ hν
          (fun i => X n i ξ) (fun j => Y n j ξ) f i j -
          markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
            (X n i ξ) (Y n j ξ)| ≤ B n)
    (hG : ∀ n c ξ i j, cellS (X n i ξ) = c → cellT (Y n j ξ) = c →
      |markedProbeKernel (g c) (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT)
        (X n i ξ) (Y n j ξ)| ≤ Gb n)
    (hintBlock : ∀ n c, Integrable (fun ξ =>
      finslerNormalizedTileBlock (n := n) (ι := ι) F μ ν K hK.measurableSet hμ hν
        (fun i ω' => cellS (X n i ω')) (fun j ω' => cellT (Y n j ω')) (X n) (Y n) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t c ξ) (P n))
    (hintModel : ∀ n c, Integrable (fun ξ =>
      frozenModelTileBlock (fun i => cellS (X n i ξ)) (fun j => cellT (Y n j ξ))
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
        t c / ((n + 1 : ℕ) : ℝ)) (P n))
    (hmodel_bound : ∀ n c, (∫ ξ,
      frozenModelTileBlock (fun i => cellS (X n i ξ)) (fun j => cellT (Y n j ξ))
        (fun i j => markedKineticKernel (q := q) (frozenMarkedRadius w n c) (kin c)
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
        (fun i j => markedProbeKernel (g c) (atlasMarkMap coordS labelS)
          (atlasMarkMap coordT labelT) (X n i ξ) (Y n j ξ))
        t c / ((n + 1 : ℕ) : ℝ) ∂P n) ≤ Bnd n)
    (hintCount : ∀ n c, Integrable (fun ξ =>
      |tileSourceCount (fun i ω' => cellS (X n i ω')) c ξ -
        tileTargetCount (fun j ω' => cellT (Y n j ω')) c ξ|) (P n))
    (hcount : ∀ n c, ∫ ξ,
      |tileSourceCount (fun i ω' => cellS (X n i ω')) c ξ -
        tileTargetCount (fun j ω' => cellT (Y n j ω')) c ξ| ∂P n ≤
      Real.sqrt (2 * ((n + 1 : ℕ) : ℝ) * (w c : ℝ)))
    (hδ : Tendsto (fun n =>
      2 * ε n * Bnd n + (|t| * B n + 2 * ε n * (|t| * Gb n))) atTop (𝓝 0))
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (hpressure : pressure f t = ∑ c, (w c : ℝ) * p c t) :
    ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i => X n i ξ) (fun j => Y n j ξ) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / (q : ℝ))) f t ∂P n) ≤
        pressure f t + ε' := by
  have h := finslerExpectationUpperBound_of_frozen_comparison'
    (F := F) hcomplete μ ν K hK hμ hν P X Y hX hY hXlaw hYlaw hlaw φ hφ f t q hq
    w hwsum hwpos hCb0 hG0 hkin hkin_bound hg hgb α β p hp
    cellS hcellS cellT hcellT hmassS hmassT
    coordS hcoordS labelS hlabelS coordT hcoordT labelT hlabelT
    hcubeS hmarkLawS hindepS hcubeT hmarkLawT hindepT
    hCbnd0 hGbnd0 hCbnd hGbnd
    ε B Gb Bnd hε0 hB0 hGb0 hBnd0 hF0 hrel hprobe hG hintBlock hintModel
    hmodel_bound hintCount hcount hδ
  intro ε' hε'
  filter_upwards [h ε' hε'] with n hn
  rwa [hpressure]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
