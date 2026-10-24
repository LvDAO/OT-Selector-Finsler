import OTSelector.Reconstruction.OriginalQuadraticTransportQuantizationNeumannEndpoint

/-! Exact transfer of the original raw-coordinate transport to its genuine
Euclidean physical metric, preserving both marginals and full square cost. -/
open Set Function MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The actual coordinate map transports a real raw density plan to the physical
Euclidean space. In particular no raw sup distance is used as Euclidean distance. -/
theorem originalRawQuadraticCoupling_toEuclidean
    (μ ν : Measure (ι → ℝ)) (π : Measure ((ι → ℝ) × (ι → ℝ)))
    (hπ : Vlasov.IsCoupling π μ ν) [IsFiniteMeasure π]
    (hI : Integrable (fun z ↦ ‖(EuclideanSpace.equiv ι ℝ).symm z.2-
      (EuclideanSpace.equiv ι ℝ).symm z.1‖^2) π) :
    let e := (EuclideanSpace.equiv ι ℝ).symm
    let Γ := π.map (Prod.map e e)
    Vlasov.IsCoupling Γ (μ.map e) (ν.map e) ∧ IsFiniteMeasure Γ ∧
    Integrable (fun z ↦ dist z.1 z.2^2) Γ ∧
    (∫ z, dist z.1 z.2^2 ∂Γ) =
      ∫ z, ‖(EuclideanSpace.equiv ι ℝ).symm z.2-
        (EuclideanSpace.equiv ι ℝ).symm z.1‖^2 ∂π := by
  let e : (ι → ℝ) → EuclideanSpace ℝ ι := (EuclideanSpace.equiv ι ℝ).symm
  have he : Measurable e := (EuclideanSpace.equiv ι ℝ).symm.continuous.measurable
  have hc : Measurable (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ dist z.1 z.2^2) :=
    (measurable_fst.dist measurable_snd).pow_const 2
  have hcompI : Integrable ((fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      dist z.1 z.2^2) ∘ Prod.map e e) π := by
    apply hI.congr
    filter_upwards [] with z
    change ‖e z.2-e z.1‖^2 = dist (e z.1) (e z.2)^2
    rw [dist_eq_norm, norm_sub_rev]
  have hmapI := (integrable_map_measure hc.aestronglyMeasurable (he.prodMap he).aemeasurable).2 hcompI
  refine ⟨hπ.map e e he he, inferInstance, hmapI, ?_⟩
  rw [integral_map (he.prodMap he).aemeasurable hc.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  change dist (e z.1) (e z.2)^2 = ‖e z.2-e z.1‖^2
  rw [dist_eq_norm, norm_sub_rev]
end OTSelector.Reconstruction
