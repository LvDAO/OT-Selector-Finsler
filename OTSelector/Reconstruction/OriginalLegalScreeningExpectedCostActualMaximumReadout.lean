import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostFiniteValue

/-! The actual FULL scalar readout is the signed minimum among true legal maxima. -/
open Set Function
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Every genuine legal maximum on the unchanged physical FULL indices bounds
its actual finite optimum. No optimizer, repaired matching or cost bound is selected. -/
theorem originalScreeningFullValue_le_actualMaximum_cost {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (cloud : TwoMarkedCloudSpace q ℝ ℝ)
    (γ : OTSelector.PartialMatching cloud.1.1 cloud.2.1)
    (hlegal : PartialMatching.IsLegal
      (scalarClockLegalGraph (fun i : Fin cloud.1.1 ↦ (cloud.1.2 i).2) (fun j : Fin cloud.2.1 ↦ (cloud.2.2 j).2)) γ)
    (hmax : γ.card = PartialMatching.legalMaximumCard
      (scalarClockLegalGraph (fun i : Fin cloud.1.1 ↦ (cloud.1.2 i).2) (fun j : Fin cloud.2.1 ↦ (cloud.2.2 j).2))) :
    let A := originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) cloud
    originalScreeningFullValue b R kin g t cloud ≤
      γ.cost (fun i j ↦ originalWeightedEdgeCost kin g t (A.1.2 i,A.2.2 j)) := by
  let A := originalMappedReserveCloudArrays q (originalOrientedRawCubePhysicalMap b R) cloud
  simpa only [originalScreeningFullValue,unclampedBlockLegalTilted,Real.one_rpow,one_mul,id_eq,
    originalWeightedEdgeCost,Pi.sub_def,A,originalMappedReserveCloudArrays,
    originalPhysicalReserveCloudArrays,originalMappedReserveTwoCloud,originalMappedReserveCloud,cloudEncode] using
    PartialMatching.legalMaximumValue_le
      (fun i j ↦ originalWeightedEdgeCost kin g t (A.1.2 i,A.2.2 j)) hlegal hmax

end OTSelector.Reconstruction
