import OTSelector.Reconstruction.OriginalReserveOrientedWindowDilation

/-! Actual physical placement and dilation commute with the same finite original point measures. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Mapping physical positions maps the actual finite colored measure, preserving
every original clock, color, index and repeated atom. -/
theorem originalFiniteInputArrays_map_physical {q : ℕ}
    (arrays : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    {T : (Fin q → ℝ) → (Fin q → ℝ)} (hT : Measurable T) :
    (legalInputTwoBlockMeasure q arrays).map (fun p ↦ ((T p.1.1, p.1.2), p.2)) =
      legalInputTwoBlockMeasure q
        (mapBlockData (Prod.map T id) arrays.1, mapBlockData (Prod.map T id) arrays.2) := by
  have hm : Measurable (fun p : LegalColoredInputPoint q ↦ ((T p.1.1, p.1.2), p.2)) := by
    fun_prop
  change ((∑ i : Fin arrays.1.1, Measure.dirac (arrays.1.2 i, (0 : Fin 2))) +
    (∑ i : Fin arrays.2.1, Measure.dirac (arrays.2.2 i, (1 : Fin 2)))).map _ =
      (∑ i : Fin arrays.1.1, Measure.dirac ((T (arrays.1.2 i).1, (arrays.1.2 i).2), (0 : Fin 2))) +
      (∑ i : Fin arrays.2.1, Measure.dirac ((T (arrays.2.2 i).1, (arrays.2.2 i).2), (1 : Fin 2)))
  rw [Measure.map_add _ _ hm,
    Measure.map_finset_sum hm.aemeasurable, Measure.map_finset_sum hm.aemeasurable]
  simp only [Measure.map_dirac]

/-- Dilation of the genuine preimage-window finite arrays is exactly the same
frame's actual physical-window array, with every original index unchanged. -/
theorem originalMappedReserveCloudArrays_oriented_dilation {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {c : ℝ} (hc : c ≠ 0) (R : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    (legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
      (originalOrientedRawCubePhysicalMap b (R / c)) ω)).map
        (legalColoredInputDilation q c hc) =
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) ω) := by
  change (legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
    (originalOrientedRawCubePhysicalMap b (R / c)) ω)).map
      (fun p ↦ ((c • p.1.1, p.1.2), p.2)) = _
  rw [originalFiniteInputArrays_map_physical _ (show Measurable (fun x : Fin q → ℝ ↦ c • x) by fun_prop)]
  simp only [originalMappedReserveCloudArrays, originalPhysicalReserveCloudArrays,
    originalMappedReserveTwoCloud, originalMappedReserveCloud, mapBlockData, cloudEncode,
    Prod.map_apply, id_eq, originalOrientedRawCubePhysicalMap_scale b hc R]

end OTSelector.Reconstruction
