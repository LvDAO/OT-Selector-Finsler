import OTSelector.Probability.FinslerTileBlockLawComparisonCounts
import Mathlib.Probability.Independence.Basic

/-!
# M2: identification of the normalized tile law with the marked one-point law

This module isolates the geometric link between the physical normalized tile law
and the marked one-point law used by the upper bound.  The target identity is

`((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})).map markS =
  markedOnePointLaw q A α`

with `markS : Xs → (Fin q → ℝ) × A` the atlas mark map (cube coordinate plus
mark), and the analogous target identity for `markT`.

## Reduction

The marked one-point law is the product `(cubeMeasure (Fin q) 1).prod α`
(`markedOnePointLaw_eq_prod`).  Consequently the pushforward identity follows
from three checkable atlas facts:

1. `hcube`: the normalized cube coordinate has the uniform cube law
   `cubeMeasure (Fin q) 1`;
2. `hmark`: the mark marginal has law `α`;
3. `hindep`: the cube coordinate and the mark are independent, i.e. the
   conditional law of the mark given the cube coordinate is `α` for almost every
   coordinate.

These give `map_pair_eq_markedOnePointLaw`, hence
`map_normalized_tile_atlasMarkMap_eq_markedOnePointLaw` for the normalized tile
law, and finally
`integral_frozenModelTileBlock_eq_modelBlockSum_of_atlas`, which is
`integral_frozenModelTileBlock_eq_modelBlockSum_of_bounds` with the atlas
hypotheses `hα`/`hβ` replaced by the three reductions above.

## Gap map: atlas fields supplying the hypotheses

The reconstruction lane in `OTSelector.Reconstruction` provides the following
data and should discharge the three hypotheses of
`map_normalized_tile_atlasMarkMap_eq_markedOnePointLaw`:

* `μs`, `μt`: the physical (root) point laws.  The physical point of a seed label
  `w` at time `t` is `P.toManifold (t, w) = P.seed.curve w t`
  (`CalibratedSeedWindow.toManifold`, `CalibratedSeedWindow.domain`).
* `coordS`: the normalized seed label coordinate.  In a window `P` every point of
  the piece is `P.toManifold (t, w)` for a unique label `w : P.seed.covector.ker`;
  the cube coordinate is the coordinate of `w` in a linear basis of
  `P.seed.covector.ker` (`Module.finBasis ℝ P.seed.covector.ker`, with
  `q = finrank ℝ P.seed.covector.ker`), normalized by `P.seed.normalization` to
  the unit cube.  The atlas fields are `CalibratedSeedWindow.toManifold`,
  `seed.curve`, `seed.normalization`, `seed.labels`, `domain`, `readout`.
* `hcube`: the normalized label-coordinate law is the uniform cube law.  This is
  the Haar/uniform reference statement of
  `FinslerPopulationSeedIntensity`: `populationSeedPieceCoordinateLaw_eq_withDensity`
  writes the pulled-back piece law as the seed Haar measure weighted by
  `populationSeedPieceHaarDensity`; `hcube` is the case in which that weight is
  the constant uniform density on the cube.
* `labelS` and `hmark`: the mark (population/coefficient mark) and its marginal
  law `α`.  The atlas fields are the coefficient core label
  (`FinslerCoefficientCoreLabel`, `populationSeedRootLabelValue`) and the local
  marked population law `α`.
* `hindep`: the conditional law of the mark given the cube coordinate is `α`.
  In the reconstruction lane this is the product factorization of the
  conditional density in `FinslerPopulationConditionalLaw`
  (`populationConditionalDensity`, `PopulationConditionalWindowLaw`): the
  conditional density splits into the label-coordinate factor
  (`populationWindowLabelReference`, uniform reference) and the population mark
  factor `α`.

The remaining geometric work is to instantiate `coordS`, `labelS` from these
fields and to verify `hcube`, `hmark`, `hindep`; the law-theoretic passage from
those three facts to the marked one-point law, and from there to `hblock`, is
proved here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace OTSelector.Probability

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable {M : Type*} [MeasurableSpace M]
variable {Ω : Type*} [MeasurableSpace Ω]
variable {Xs Yt : Type*} [MeasurableSpace Xs] [MeasurableSpace Yt]
variable {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [Fintype ι] [DecidableEq ι]

/-- The marked one-point law is the product of the uniform cube law and the mark
law. -/
theorem markedOnePointLaw_eq_prod (α : Measure A) :
    markedOnePointLaw q A α = (cubeMeasure (Fin q) 1).prod α :=
  rfl

/-- **Joint marked law from independent marginals.**  If the cube coordinate has
the uniform cube law, the mark has law `α`, and the two are independent, then the
joint map `x ↦ (coord x, mark x)` has law `markedOnePointLaw q A α`. -/
theorem map_pair_eq_markedOnePointLaw (ν : Measure M) [IsFiniteMeasure ν]
    (coord : M → Fin q → ℝ) (mark : M → A)
    (hcoord : AEMeasurable coord ν) (hmark : AEMeasurable mark ν)
    (hcube : ν.map coord = cubeMeasure (Fin q) 1)
    (hmarkLaw : ν.map mark = α)
    (hindep : IndepFun coord mark ν) :
    ν.map (fun x => (coord x, mark x)) = markedOnePointLaw q A α := by
  rw [hindep.map_prod_eq_prod_map_map hcoord hmark, hcube, hmarkLaw]

/-- The atlas mark map: the cube coordinate together with the mark. -/
def atlasMarkMap (coord : M → Fin q → ℝ) (mark : M → A) : M → (Fin q → ℝ) × A :=
  fun x => (coord x, mark x)

/-- Measurability of the atlas mark map. -/
theorem measurable_atlasMarkMap (coord : M → Fin q → ℝ) (mark : M → A)
    (hcoord : Measurable coord) (hmark : Measurable mark) :
    Measurable (atlasMarkMap coord mark) :=
  hcoord.prodMk hmark

/-- **M2 atlas identification for the normalized tile law.**  The normalized
physical tile law pushes forward under the atlas mark map to the marked
one-point law, provided the normalized cube coordinate has the uniform cube law,
the mark marginal is `α`, and the two are independent (equivalently, the
conditional mark law is `α` at almost every cube coordinate). -/
theorem map_normalized_tile_atlasMarkMap_eq_markedOnePointLaw
    (μ : Measure M) [IsProbabilityMeasure μ] (lab : M → ι) (c : ι)
    (hρ : μ (lab ⁻¹' {c}) ≠ 0)
    (coord : M → Fin q → ℝ) (mark : M → A)
    (hcoord : Measurable coord) (hmark : Measurable mark)
    (hcube : ((μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c})).map coord =
      cubeMeasure (Fin q) 1)
    (hmarkLaw : ((μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c})).map mark = α)
    (hindep : IndepFun coord mark ((μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c}))) :
    ((μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c})).map (atlasMarkMap coord mark) =
      markedOnePointLaw q A α := by
  haveI : IsProbabilityMeasure ((μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c})) :=
    isProbabilityMeasure_inv_smul_restrict μ hρ
  exact map_pair_eq_markedOnePointLaw
    ((μ (lab ⁻¹' {c}))⁻¹ • μ.restrict (lab ⁻¹' {c})) coord mark
    hcoord.aemeasurable hmark.aemeasurable hcube hmarkLaw hindep

/-- The source atlas identification is exactly the `hα` hypothesis of the model
bridge. -/
theorem atlas_source_identification
    (μs : Measure Xs) [IsProbabilityMeasure μs] (labS : Xs → ι) (c : ι)
    (hρs : μs (labS ⁻¹' {c}) ≠ 0)
    (coordS : Xs → Fin q → ℝ) (labelS : Xs → A)
    (hcoordS : Measurable coordS) (hlabelS : Measurable labelS)
    (hcubeS : ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})).map coordS =
      cubeMeasure (Fin q) 1)
    (hmarkLawS : ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})).map labelS = α)
    (hindepS : IndepFun coordS labelS
      ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c}))) :
    ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})).map
        (atlasMarkMap coordS labelS) = markedOnePointLaw q A α :=
  map_normalized_tile_atlasMarkMap_eq_markedOnePointLaw μs labS c hρs
    coordS labelS hcoordS hlabelS hcubeS hmarkLawS hindepS

/-- The target atlas identification is exactly the `hβ` hypothesis of the model
bridge. -/
theorem atlas_target_identification
    (μt : Measure Yt) [IsProbabilityMeasure μt] (labT : Yt → ι) (c : ι)
    (hρt : μt (labT ⁻¹' {c}) ≠ 0)
    (coordT : Yt → Fin q → ℝ) (labelT : Yt → B)
    (hcoordT : Measurable coordT) (hlabelT : Measurable labelT)
    (hcubeT : ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})).map coordT =
      cubeMeasure (Fin q) 1)
    (hmarkLawT : ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})).map labelT = β)
    (hindepT : IndepFun coordT labelT
      ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c}))) :
    ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})).map
        (atlasMarkMap coordT labelT) = markedOnePointLaw q B β :=
  atlas_source_identification μt labT c hρt
    coordT labelT hcoordT hlabelT hcubeT hmarkLawT hindepT


/-- **`hblock` from the M2 atlas identification.**  This is
`integral_frozenModelTileBlock_eq_modelBlockSum_of_bounds` with the atlas
pushforward hypotheses `hα`/`hβ` replaced by the three atlas reductions: the
normalized cube coordinate has the uniform cube law, the mark marginal has law
`α` (resp. `β`), and the coordinate and the mark are independent. -/
theorem integral_frozenModelTileBlock_eq_modelBlockSum_of_atlas {q : ℕ} {t : ℝ}
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hg : Measurable (Function.uncurry g))
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (μs : Measure Xs) [IsProbabilityMeasure μs]
    (μt : Measure Yt) [IsProbabilityMeasure μt]
    (labS : Xs → ι) (hS : Measurable labS) (labT : Yt → ι) (hT : Measurable labT)
    (c : ι) (m : ℕ) (w : unitInterval) (hwpos : 0 < (w : ℝ))
    (hws : μs (labS ⁻¹' {c}) = ENNReal.ofReal (w : ℝ))
    (hwt : μt (labT ⁻¹' {c}) = ENNReal.ofReal (w : ℝ))
    (coordS : Xs → Fin q → ℝ) (hcoordS : Measurable coordS)
    (labelS : Xs → A) (hlabelS : Measurable labelS)
    (coordT : Yt → Fin q → ℝ) (hcoordT : Measurable coordT)
    (labelT : Yt → B) (hlabelT : Measurable labelT)
    (hcubeS : ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})).map coordS =
      cubeMeasure (Fin q) 1)
    (hmarkLawS : ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})).map labelS = α)
    (hindepS : IndepFun coordS labelS
      ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})))
    (hcubeT : ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})).map coordT =
      cubeMeasure (Fin q) 1)
    (hmarkLawT : ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})).map labelT = β)
    (hindepT : IndepFun coordT labelT
      ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})))
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin m → Ω → Xs) (Y : Fin m → Ω → Yt)
    (hmeas : Measurable fun ξ : Ω => (fun i => X i ξ, fun j => Y j ξ))
    (hlaw : P.map (fun ξ : Ω => (fun i => X i ξ, fun j => Y j ξ)) =
      twoColourLaw μs μt m)
    {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    (hC : ∀ x y, |markedKineticKernel (q := q)
      ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ C)
    (hG : ∀ x y, |markedProbeKernel g
      (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤ G) :
    ∫ ξ, frozenModelTileBlock labS labT
        (markedKineticKernel (q := q) ((Nat.floor ((m : ℝ) * (w : ℝ)) : ℕ) : ℝ) kin
          (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT))
        (markedProbeKernel g (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT))
        t c (fun i => X i ξ, fun j => Y j ξ) ∂P
      = modelBlockSum q t kin g α β w m := by
  classical
  have hρs : μs (labS ⁻¹' {c}) ≠ 0 := by
    rw [hws]
    exact ne_of_gt ((ENNReal.ofReal_pos).mpr hwpos)
  have hρt : μt (labT ⁻¹' {c}) ≠ 0 := by
    rw [hwt]
    exact ne_of_gt ((ENNReal.ofReal_pos).mpr hwpos)
  have hα : ((μs (labS ⁻¹' {c}))⁻¹ • μs.restrict (labS ⁻¹' {c})).map
      (atlasMarkMap coordS labelS) = markedOnePointLaw q A α :=
    atlas_source_identification μs labS c hρs coordS labelS hcoordS hlabelS
      hcubeS hmarkLawS hindepS
  have hβ : ((μt (labT ⁻¹' {c}))⁻¹ • μt.restrict (labT ⁻¹' {c})).map
      (atlasMarkMap coordT labelT) = markedOnePointLaw q B β :=
    atlas_target_identification μt labT c hρt coordT labelT hcoordT hlabelT
      hcubeT hmarkLawT hindepT
  exact integral_frozenModelTileBlock_eq_modelBlockSum_of_bounds hkin hg α β μs μt labS hS
    labT hT c m w hwpos hws hwt
    (atlasMarkMap coordS labelS) (measurable_atlasMarkMap coordS labelS hcoordS hlabelS)
    (atlasMarkMap coordT labelT) (measurable_atlasMarkMap coordT labelT hcoordT hlabelT)
    hα hβ P X Y hmeas hlaw hC0 hG0 hC hG

end OTSelector.Probability
