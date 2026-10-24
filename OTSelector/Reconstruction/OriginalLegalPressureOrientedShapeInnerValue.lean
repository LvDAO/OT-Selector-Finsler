import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeInnerLaw
import OTSelector.Reconstruction.OriginalLegalScreeningPressureFrame
import OTSelector.Reconstruction.MarkedStationaryValueLegalAffineShape

/-! Literal original finite legal values in the inner orthogonal cube. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {q : ℕ}

theorem measurable_originalOrientedShapeUnitInnerMap
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (s : ℝ) :
    Measurable (originalOrientedShapeUnitInnerMap b s) := by
  exact measurable_pi_lambda _ fun i ↦ ((measurable_pi_apply i).comp
    (measurable_originalOrientedRawCubePhysicalMap b (s/2))).add_const (1/2:ℝ)

/-- All original marks, counts and allowed edges are kept by the exact inner
coordinate map. Its spatial volume supplies exactly the intensity rescaling. -/
theorem unclamped_originalOrientedShape_inner_value
    (hq : 0 < q) (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a d (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a d (fun i ↦ c*v i) = c^2*kin a d v)
    (g : ℝ → ℝ → ℝ) (t : ℝ) (dS dT : BlockData ((Fin q → ℝ) × ℝ)) :
    unclampedBlockLegalTilted q id id r kin g t
      (mapBlockData (Prod.map (originalOrientedShapeUnitInnerMap b s) id) dS)
      (mapBlockData (Prod.map (originalOrientedShapeUnitInnerMap b s) id) dT) =
      unclampedBlockLegalTilted q id id (r*s^q)
        (originalScreeningFrameKinetic b kin) g t dS dT := by
  unfold unclampedBlockLegalTilted
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j _
  change r^(2/(q:ℝ))*kin (dS.2 i).2 (dT.2 j).2
    (fun l ↦ (originalOrientedRawCubePhysicalMap b (s/2) (dT.2 j).1 l+(1/2:ℝ)) -
      (originalOrientedRawCubePhysicalMap b (s/2) (dS.2 i).1 l+(1/2:ℝ))) + _ = _
  have hdiff :
      (fun l ↦ (originalOrientedRawCubePhysicalMap b (s/2) (dT.2 j).1 l+(1/2:ℝ)) -
        (originalOrientedRawCubePhysicalMap b (s/2) (dS.2 i).1 l+(1/2:ℝ))) =
      orthonormalPhysicalCubeMap b (s • ((dT.2 j).1-(dS.2 i).1)) := by
    calc
      _ = originalOrientedRawCubePhysicalMap b (s/2) (dT.2 j).1 -
          originalOrientedRawCubePhysicalMap b (s/2) (dS.2 i).1 := by
        funext l
        simp only [Pi.sub_apply]
        ring
      _ = _ := by rw [originalOrientedRawCubePhysicalMap_sub,show 2*(s/2)=s by ring]
  rw [hdiff]
  change r^(2/(q:ℝ))*originalScreeningFrameKinetic b kin (dS.2 i).2 (dT.2 j).2
    (fun l ↦ s*((dT.2 j).1 l-(dS.2 i).1 l)) + _ = _
  rw [originalScreeningFrameKinetic_homogeneous b hhom _ _ s hs,
    rpow_affine_intensity q hq hr hs]
  simp only [mapBlockData,Prod.map_snd,id_eq]
  ring

end OTSelector.Reconstruction
