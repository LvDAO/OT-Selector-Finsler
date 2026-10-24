import OTSelector.Reconstruction.OriginalReserveWindowExactCompactReadout

/-! A literal original iid sampler for the prescribed physical reserve window. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Original normalized Haar positions, independent original marks, and the
physical-volume Poisson count of one reserve color. -/
def originalPhysicalReserveCloudLaw (q : ℕ) (K : Set (Fin q → ℝ))
    (α : Measure ℝ) : Measure (MarkedCloudSpace q ℝ) :=
  (poissonMeasure (volume K).toNNReal).prod (Measure.infinitePi fun _ : ℕ ↦
    (normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K)).prod α)

/-- Both original reserve colors are sampled independently on the same window. -/
def originalPhysicalReserveTwoCloudLaw (q : ℕ) (K : Set (Fin q → ℝ))
    (α β : Measure ℝ) : Measure (TwoMarkedCloudSpace q ℝ ℝ) :=
  (originalPhysicalReserveCloudLaw q K α).prod (originalPhysicalReserveCloudLaw q K β)

/-- The finite readout uses only the same original indices below each count. -/
def originalPhysicalReserveCloudArrays (q : ℕ) (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q) :=
  (cloudEncode ω.1, cloudEncode ω.2)

theorem measurable_originalPhysicalReserveCloudArrays (q : ℕ) :
    Measurable (originalPhysicalReserveCloudArrays q) :=
  (measurable_cloudEncode.comp measurable_fst).prodMk
    (measurable_cloudEncode.comp measurable_snd)

/-- A compact positive physical window supplies its own normalized Haar probability. -/
theorem isProbabilityMeasure_originalPhysicalReservePointLaw (q : ℕ)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0) :
    IsProbabilityMeasure (normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K)) := by
  rw [normalizedFiniteLaw_restrict_eq_cond volume K hK.measure_lt_top.ne]
  exact cond_isProbabilityMeasure_of_finite hKpos hK.measure_lt_top.ne

/-- The actual physical-window reserve sampler is a probability law. -/
theorem isProbabilityMeasure_originalPhysicalReserveTwoCloudLaw (q : ℕ)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    IsProbabilityMeasure (originalPhysicalReserveTwoCloudLaw q K α β) := by
  let := isProbabilityMeasure_originalPhysicalReservePointLaw q hK hKpos
  unfold originalPhysicalReserveTwoCloudLaw originalPhysicalReserveCloudLaw
  infer_instance

/-- One original physical reserve prefix has the literal finite Poisson array law. -/
theorem map_originalPhysicalReserveCloudLaw_encode (q : ℕ)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    (α : Measure ℝ) [IsProbabilityMeasure α] :
    (originalPhysicalReserveCloudLaw q K α).map cloudEncode =
      Measure.sum (fun n : ℕ ↦ poissonMeasure (volume K).toNNReal {n} •
        (Measure.pi (fun _ : Fin n ↦
          (normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K)).prod α)).map
          (fun x ↦ (⟨n, x⟩ : BlockData (LegalMarkedPhysicalPoint q)))) := by
  let := isProbabilityMeasure_originalPhysicalReservePointLaw q hK hKpos
  exact (blockDataLaw_eq_map_cloud _ _).symm

/-- Discarding the unused infinite tails produces the exact finite Poisson
window law; no tail is attributed to a position-selected subarray. -/
theorem map_originalPhysicalReserveCloudArrays (q : ℕ)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    (originalPhysicalReserveTwoCloudLaw q K α β).map
      (originalPhysicalReserveCloudArrays q) = legalInputPoissonWindowLaw q K α β := by
  let := isProbabilityMeasure_originalPhysicalReservePointLaw q hK hKpos
  let : IsProbabilityMeasure (originalPhysicalReserveCloudLaw q K α) := by
    unfold originalPhysicalReserveCloudLaw
    infer_instance
  let : IsProbabilityMeasure (originalPhysicalReserveCloudLaw q K β) := by
    unfold originalPhysicalReserveCloudLaw
    infer_instance
  change ((originalPhysicalReserveCloudLaw q K α).prod
    (originalPhysicalReserveCloudLaw q K β)).map (Prod.map cloudEncode cloudEncode) = _
  rw [← Measure.map_prod_map _ _ measurable_cloudEncode measurable_cloudEncode,
    map_originalPhysicalReserveCloudLaw_encode q hK hKpos α,
    map_originalPhysicalReserveCloudLaw_encode q hK hKpos β]
  rfl

end OTSelector.Reconstruction
