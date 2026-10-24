import OTSelector.Reconstruction.OriginalReservePhysicalWindowSupport

/-! Physical placement of the same original cube reserve sampler preserves all indices. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Place every original spatial point physically while preserving its count,
original natural index and original clock mark, including the unused tail. -/
def originalMappedReserveCloud (q : ℕ) (F : (Fin q → ℝ) → (Fin q → ℝ))
    (ω : MarkedCloudSpace q ℝ) : MarkedCloudSpace q ℝ :=
  (ω.1, fun i ↦ (F (ω.2 i).1, (ω.2 i).2))

def originalMappedReserveTwoCloud (q : ℕ) (F : (Fin q → ℝ) → (Fin q → ℝ))
    (ω : TwoMarkedCloudSpace q ℝ ℝ) : TwoMarkedCloudSpace q ℝ ℝ :=
  (originalMappedReserveCloud q F ω.1, originalMappedReserveCloud q F ω.2)

def originalMappedReserveCloudArrays (q : ℕ) (F : (Fin q → ℝ) → (Fin q → ℝ))
    (ω : TwoMarkedCloudSpace q ℝ ℝ) :
    BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q) :=
  originalPhysicalReserveCloudArrays q (originalMappedReserveTwoCloud q F ω)

theorem measurable_originalMappedReserveCloud (q : ℕ)
    {F : (Fin q → ℝ) → (Fin q → ℝ)} (hF : Measurable F) :
    Measurable (originalMappedReserveCloud q F) := by
  unfold originalMappedReserveCloud
  fun_prop

theorem measurable_originalMappedReserveTwoCloud (q : ℕ)
    {F : (Fin q → ℝ) → (Fin q → ℝ)} (hF : Measurable F) :
    Measurable (originalMappedReserveTwoCloud q F) :=
  (measurable_originalMappedReserveCloud q hF).prodMap
    (measurable_originalMappedReserveCloud q hF)

theorem measurable_originalMappedReserveCloudArrays (q : ℕ)
    {F : (Fin q → ℝ) → (Fin q → ℝ)} (hF : Measurable F) :
    Measurable (originalMappedReserveCloudArrays q F) :=
  (measurable_originalPhysicalReserveCloudArrays q).comp
    (measurable_originalMappedReserveTwoCloud q hF)

/-- The original physical-window point law identifies the entire placed original
Poisson sampler, without changing its independent count or marks. -/
theorem map_originalMappedReserveCloud (q : ℕ)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    {F : (Fin q → ℝ) → (Fin q → ℝ)} (hF : Measurable F)
    (hpoint : (cubeMeasure (Fin q) 1).map F =
      normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K))
    (α : Measure ℝ) [IsProbabilityMeasure α] :
    (markedPoissonLaw q ℝ α (volume K).toNNReal).map (originalMappedReserveCloud q F) =
      originalPhysicalReserveCloudLaw q K α := by
  let := isProbabilityMeasure_originalPhysicalReservePointLaw q hK hKpos
  have hm : ((cubeMeasure (Fin q) 1).prod α).map (Prod.map F id) =
      (normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K)).prod α := by
    rw [← Measure.map_prod_map _ _ hF measurable_id, hpoint, Measure.map_id]
  have hseq : (Measure.infinitePi fun _ : ℕ ↦ (cubeMeasure (Fin q) 1).prod α).map
      (fun z i ↦ Prod.map F id (z i)) =
      Measure.infinitePi (fun _ : ℕ ↦
        (normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K)).prod α) := by
    rw [Measure.infinitePi_map_pi _ (fun _ ↦ hF.prodMap measurable_id)]
    simp only [hm]
  change ((poissonMeasure (volume K).toNNReal).prod
    (Measure.infinitePi fun _ : ℕ ↦ (cubeMeasure (Fin q) 1).prod α)).map
      (Prod.map id (fun z i ↦ Prod.map F id (z i))) = _
  rw [← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id, hseq]
  rfl

/-- Both placed original colors have exactly the actual independent
physical-window reserve law. -/
theorem map_originalMappedReserveTwoCloud (q : ℕ)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    {F : (Fin q → ℝ) → (Fin q → ℝ)} (hF : Measurable F)
    (hpoint : (cubeMeasure (Fin q) 1).map F =
      normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K))
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    (twoMarkedCloudLaw q ℝ ℝ α β (volume K).toNNReal).map
      (originalMappedReserveTwoCloud q F) = originalPhysicalReserveTwoCloudLaw q K α β := by
  change ((markedPoissonLaw q ℝ α (volume K).toNNReal).prod
    (markedPoissonLaw q ℝ β (volume K).toNNReal)).map
      (Prod.map (originalMappedReserveCloud q F) (originalMappedReserveCloud q F)) = _
  rw [← Measure.map_prod_map _ _ (measurable_originalMappedReserveCloud q hF)
    (measurable_originalMappedReserveCloud q hF),
    map_originalMappedReserveCloud q hK hKpos hF hpoint α,
    map_originalMappedReserveCloud q hK hKpos hF hpoint β]
  rfl

/-- The physical finite arrays are the same placed original prefixes and have
the exact prescribed spatial-window Poisson law. -/
theorem map_originalMappedReserveCloudArrays (q : ℕ)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    {F : (Fin q → ℝ) → (Fin q → ℝ)} (hF : Measurable F)
    (hpoint : (cubeMeasure (Fin q) 1).map F =
      normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K))
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    (twoMarkedCloudLaw q ℝ ℝ α β (volume K).toNNReal).map
      (originalMappedReserveCloudArrays q F) = legalInputPoissonWindowLaw q K α β := by
  change (twoMarkedCloudLaw q ℝ ℝ α β (volume K).toNNReal).map
    (originalPhysicalReserveCloudArrays q ∘ originalMappedReserveTwoCloud q F) = _
  rw [← Measure.map_map (measurable_originalPhysicalReserveCloudArrays q)
      (measurable_originalMappedReserveTwoCloud q hF),
    map_originalMappedReserveTwoCloud q hK hKpos hF hpoint α β,
    map_originalPhysicalReserveCloudArrays q hK hKpos α β]

end OTSelector.Reconstruction
