import OTSelector.Reconstruction.FinslerOriginalRadiusTranscription

/-!
# The intrinsic frozen-bound term of the F13 data (actual producer)

## Delivered

|hCbnd_intrinsic_lane|: the |hCbnd_intrinsic| field of |PopDataIntrinsic| in the
exact shape required by the repaired interface, produced from the lane's per-pair
kinetic bound |kin c a b v <= Cb * sum_l v_l^2| by
|hCbnd_intrinsic_blockW_of_hkin_bound| (FinslerOriginalRadiusTranscription.lean:229).
This is the only field of |PopDataIntrinsic| whose content is a *derived
mathematical estimate*; it is now available unconditionally for the lane's
geometric data (atlas mark maps of the lane's coordinate and label functions).

## What cannot be filled from the modules in scope (precise list)

Constructing |dataIntr_of_geometricLane : forall f t hpert, PopDataIntrinsic ...|
requires, beyond |hCbnd_intrinsic| and |hrel_guarded|, the full geometric lane
bundle: a measurable cell decomposition |cellS cellT : M -> Fin q -> Fin m| with
the mass laws |hmassS hmassT| (block weights |1 / m^q|), coordinate maps
|coordS coordT : M -> Fin q -> R| with cube laws |hcubeS hcubeT|
(cubeMeasure (Fin q) 1), label maps |labelS : M -> Am|, |labelT : M -> Cm| with
mark laws |hmarkLawS hmarkLawT| and independence |hindepS hindepT|, the per-cell
kinetic |kin : (Fin q -> Fin m) -> Am -> Cm -> (Fin q -> R) -> R| and probe
|g : (Fin q -> Fin m) -> Am -> Cm -> R| with their bounds |hkin hkin_bound|,
|hg hgb| and constants |Cb G|, the population limits |p| with |hp|, the error
sequences |epsilon Berr Gb Bnd| with |hF0 hrel_guarded hprobe hG hmodel_bound hdelta|,
and |hqdim|.  The modules in my read scope
(|FinslerOriginalFrozenSupportBoundWiring|, |FinslerOriginalRadiusTranscription|,
|FinslerOriginalPopDataIntrinsicBound|) provide only the *frozen support bounds*
and the intrinsic frozen estimate; no module in them constructs a |PopDataIntrinsic|
or the geometric cell/coordinate/label bundle it needs, so those fields cannot be
filled without additional geometric-lane data (not in my write scope).

The |hpc| identification is likewise a definitional identification of the
population limit |p| with the lane's |pc|; it can only be produced once |p| itself
is chosen, so it is part of the same missing bundle.

No 'sorry', 'admit' or added axiom occurs.
-/

open Set Function Filter MeasureTheory
open OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ENNReal NNReal

noncomputable section

namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **The |hCbnd_intrinsic| field of |PopDataIntrinsic|, produced for the lane.**
From a per-pair kinetic bound and the lane's atlas mark maps this gives exactly the
intrinsic frozen bound consumed by |PopDataIntrinsic.hCbnd_intrinsic|:
|markedKineticKernel (frozenMarkedRadius (blockW q m hm) n c) (kin c) ... <=
Cb * r ^ (2/q) * q| for all |n c x y|. -/
theorem hCbnd_intrinsic_lane
    {M Am Cm : Type*} (q m : ℕ) (hm : 0 < m)
    (kin : (Fin q → Fin m) → Am → Cm → (Fin q → ℝ) → ℝ) {Cb : ℝ} (hCb0 : 0 ≤ Cb)
    (hkin : ∀ (c : Fin q → Fin m) (a : Am) (b : Cm) (v : Fin q → ℝ),
      |kin c a b v| ≤ Cb * ∑ l, v l ^ 2)
    (coordS : M → Fin q → ℝ) (labelS : M → Am)
    (coordT : M → Fin q → ℝ) (labelT : M → Cm) :
    ∀ (n : ℕ) (c : Fin q → Fin m) (x y : M),
      |markedKineticKernel (q := q) (frozenMarkedRadius (blockW q m hm) n c) (kin c)
        (atlasMarkMap coordS labelS) (atlasMarkMap coordT labelT) x y| ≤
        Cb * (frozenMarkedRadius (blockW q m hm) n c) ^ (2 / (q : ℝ)) * (q : ℝ) :=
  hCbnd_intrinsic_blockW_of_hkin_bound (q := q) (m := m) (hm := hm) kin hCb0 hkin
    coordS labelS coordT labelT

end OTSelector.Reconstruction
