import OTSelector.Probability.HaarAffineCube
import OTSelector.Probability.BlockDataTransport
import OTSelector.Probability.MarkedShapeLaw
import OTSelector.Probability.FiniteMeasureConditioning

/-!
# Exact original marked input laws in physical Haar windows

The physical dilation and translation are the inverse of the original affine
cube normalization. Restricting the original used prefix to a physical window
therefore has its actual normalized Haar point law, unchanged marks and exact
physical Poisson count intensity. No law of selected optimal endpoints enters.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Physical placement of the same original unit-cube point. -/
def legalInputPhysicalPoint (q : ℕ) (origin : Fin q → ℝ) (side : ℝ≥0)
    (x : Fin q → ℝ) : Fin q → ℝ := (side : ℝ) • x + origin

theorem measurable_legalInputPhysicalPoint (q : ℕ) (origin : Fin q → ℝ) (side : ℝ≥0) :
    Measurable (legalInputPhysicalPoint q origin side) := by unfold legalInputPhysicalPoint; fun_prop

/-- The literal original physical open box, with its actual affine coordinates. -/
def legalInputPhysicalBox (q : ℕ) (origin : Fin q → ℝ) (side : ℝ≥0) : Set (Fin q → ℝ) :=
  affineHaarCube (ContinuousLinearEquiv.refl ℝ (Fin q → ℝ)) origin side

/-- Original Haar mass and original normalized point law of the physical box. -/
theorem legalInputPhysicalBox_mass_and_pointLaw (q : ℕ) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side) :
    volume (legalInputPhysicalBox q origin side) = ((side ^ q : ℝ≥0) : ℝ≥0∞) ∧
    (cubeMeasure (Fin q) 1).map (legalInputPhysicalPoint q origin side) =
      normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict
        (legalInputPhysicalBox q origin side)) := by
  let e := ContinuousLinearEquiv.refl ℝ (Fin q → ℝ)
  let f := affineHaarCubeCoord e origin side
  have hf : Measurable f := measurable_affineHaarCubeCoord e origin side
  have hid : (volume : Measure (Fin q → ℝ)).map e =
      (1 : ℝ≥0) • (volume : Measure (Fin q → ℝ)) := by change volume.map id = _; simp
  have hmap : (volume : Measure (Fin q → ℝ)).map f =
      (side ^ q : ℝ≥0) • (volume : Measure (Fin q → ℝ)) := by
    simpa only [one_mul] using map_affineHaarCubeCoord volume e hid origin hside
  have hmass := congrArg (fun μ : Measure (Fin q → ℝ) ↦ μ (seedUnitCube q)) hmap
  rw [Measure.map_apply hf (measurableSet_seedUnitCube q), Measure.smul_apply,
    volume_seedUnitCube] at hmass
  simp only [ENNReal.smul_one] at hmass
  have hn := normalized_haar_coordinate_preimage_cube q volume hf (pow_pos hside q) hmap
  have hinv : legalInputPhysicalPoint q origin side ∘ f = id := by
    funext x i
    have hs : (side : ℝ) ≠ 0 := by exact_mod_cast hside.ne'
    change (side : ℝ) * ((side : ℝ)⁻¹ * (x i - origin i)) + origin i = x i
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    ring
  constructor
  · exact hmass
  · rw [← hn, Measure.map_map (measurable_legalInputPhysicalPoint q origin side) hf,
      hinv, Measure.map_id]
    rfl

/-- An actual physical subwindow has its exact normalized Haar point law
under restriction of the same original unit-cube samples. -/
theorem legalInputPhysicalPoint_restricted_law (q : ℕ) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ legalInputPhysicalBox q origin side) (hpos : volume U ≠ 0) :
    let _cube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
    (restrictedPointLaw (cubeMeasure (Fin q) 1)
      ((legalInputPhysicalPoint q origin side) ⁻¹' U)).map (legalInputPhysicalPoint q origin side) =
      normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U) := by
  dsimp only
  let : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  let B := legalInputPhysicalBox q origin side
  have hB : MeasurableSet B := measurableSet_affineHaarCube _ _ _
  obtain ⟨hmass, hmap⟩ := legalInputPhysicalBox_mass_and_pointLaw q origin hside
  have hBfin : volume B ≠ ∞ := by rw [hmass]; exact ENNReal.coe_ne_top
  have hB0 : volume B ≠ 0 := by rw [hmass]; exact_mod_cast (pow_pos hside q).ne'
  have hUfin : volume U ≠ ∞ := ((measure_mono hsub).trans_lt (lt_top_iff_ne_top.mpr hBfin)).ne
  let ν := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict B)
  have hν : ν = ProbabilityTheory.cond volume B := normalizedFiniteLaw_restrict_eq_cond volume B hBfin
  have hνmass : ν U = (volume B)⁻¹ * volume U := by
    rw [hν, cond_apply' hU, inter_eq_right.mpr hsub]
  have hνU : ν U ≠ 0 := by
    rw [hνmass]
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hBfin) hpos
  rw [← restrictedPointLaw_map (cubeMeasure (Fin q) 1)
    (measurable_legalInputPhysicalPoint q origin side) hU, hmap]
  change restrictedPointLaw ν U = _
  rw [restrictedPointLaw, ite_eq_right hνU, hν, cond_cond_eq_cond_inter' hB hU hBfin,
    inter_eq_right.mpr hsub]
  exact (normalizedFiniteLaw_restrict_eq_cond volume U hUfin).symm

/-- The same actual restriction has physical Poisson intensity equal to window
volume, including null windows. Its original box volume cancels exactly. -/
theorem legalInputPhysicalWindow_intensity (q : ℕ) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ legalInputPhysicalBox q origin side) :
    let _cube : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
    side ^ q * restrictionWeight (cubeMeasure (Fin q) 1)
      ((legalInputPhysicalPoint q origin side) ⁻¹' U) = (volume U).toNNReal := by
  dsimp only
  let : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  obtain ⟨hmass, hmap⟩ := legalInputPhysicalBox_mass_and_pointLaw q origin hside
  have hBfin : volume (legalInputPhysicalBox q origin side) ≠ ∞ := by
    rw [hmass]; exact ENNReal.coe_ne_top
  have hpoint : (cubeMeasure (Fin q) 1) ((legalInputPhysicalPoint q origin side) ⁻¹' U) =
      (volume (legalInputPhysicalBox q origin side))⁻¹ * volume U := by
    rw [← Measure.map_apply (measurable_legalInputPhysicalPoint q origin side) hU,
      hmap, normalizedFiniteLaw_restrict_eq_cond volume _ hBfin,
      cond_apply' hU, inter_eq_right.mpr hsub]
  rw [restrictionWeight, hpoint, hmass, ENNReal.toNNReal_mul, ENNReal.toNNReal_inv,
    ENNReal.toNNReal_coe, ← mul_assoc, mul_inv_cancel₀ (pow_pos hside q).ne', one_mul]

/-- The actual physical window law is a probability law when the original
window has positive volume. This is produced from original point transport. -/
theorem isProbabilityMeasure_legalInputWindowLaw (q : ℕ) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ legalInputPhysicalBox q origin side) (hpos : volume U ≠ 0) :
    IsProbabilityMeasure (normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)) := by
  let : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  rw [← legalInputPhysicalPoint_restricted_law q origin hside hU hsub hpos]
  exact Measure.isProbabilityMeasure_map (measurable_legalInputPhysicalPoint q origin side).aemeasurable

/-- Keep exactly the original prefix points in the physical source window,
then place those same points at their physical coordinates without resampling. -/
def legalInputWindowPrefix (q : ℕ) (origin : Fin q → ℝ) (side : ℝ≥0)
    (U : Set (Fin q → ℝ)) (z : MarkedCloudSpace q ℝ) :
    BlockData ((Fin q → ℝ) × ℝ) :=
  mapBlockData (Prod.map (legalInputPhysicalPoint q origin side) id)
    (shapeCloud ((legalInputPhysicalPoint q origin side) ⁻¹' U) z)

theorem measurable_legalInputWindowPrefix (q : ℕ) (origin : Fin q → ℝ) (side : ℝ≥0)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U) :
    Measurable (legalInputWindowPrefix q origin side U) :=
  (measurable_mapBlockData ((measurable_legalInputPhysicalPoint q origin side).prodMap measurable_id)).comp
    (measurable_shapeCloud (hU.preimage (measurable_legalInputPhysicalPoint q origin side)))

/-- The actual original marked Poisson prefix in a positive physical window
has the exact physical-volume count law and normalized original Haar point law,
with the original scalar mark law unchanged. -/
theorem map_legalInputWindowPrefix_markedPoissonLaw (q : ℕ) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ legalInputPhysicalBox q origin side) (hpos : volume U ≠ 0)
    (α : Measure ℝ) [IsProbabilityMeasure α] :
    let _window := isProbabilityMeasure_legalInputWindowLaw q origin hside hU hsub hpos
    (markedPoissonLaw q ℝ α (side ^ q)).map (legalInputWindowPrefix q origin side U) =
      blockDataLaw ((normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)).prod α)
        (fun n ↦ poissonMeasure (volume U).toNNReal {n}) := by
  dsimp only
  let : IsProbabilityMeasure (cubeMeasure (Fin q) 1) := isProbabilityMeasure_cubeMeasure (by norm_num)
  let : IsProbabilityMeasure (normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)) :=
    isProbabilityMeasure_legalInputWindowLaw q origin hside hU hsub hpos
  let S := (legalInputPhysicalPoint q origin side) ⁻¹' U
  have hS : MeasurableSet S := hU.preimage (measurable_legalInputPhysicalPoint q origin side)
  have hpoint : ((restrictedPointLaw (cubeMeasure (Fin q) 1) S).prod α).map
      (Prod.map (legalInputPhysicalPoint q origin side) id) =
        (normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)).prod α := by
    rw [← Measure.map_prod_map _ _ (measurable_legalInputPhysicalPoint q origin side) measurable_id,
      legalInputPhysicalPoint_restricted_law q origin hside hU hsub hpos, Measure.map_id]
  change (markedPoissonLaw q ℝ α (side ^ q)).map
    (mapBlockData (Prod.map (legalInputPhysicalPoint q origin side) id) ∘ shapeCloud S) = _
  rw [← Measure.map_map
    (measurable_mapBlockData ((measurable_legalInputPhysicalPoint q origin side).prodMap measurable_id))
    (measurable_shapeCloud hS), map_shapeCloud_markedPoissonLaw q α _ hS]
  unfold shapeBlockLaw
  rw [legalInputPhysicalWindow_intensity q origin hside hU hsub]
  exact blockDataLaw_mapPoints _ _
    ((measurable_legalInputPhysicalPoint q origin side).prodMap measurable_id) hpoint _

/-- Both original colors in the same actual physical window retain their exact
independent Poisson-prefix laws and unchanged original scalar populations. -/
theorem map_legalInputWindowPrefix_twoMarkedCloudLaw (q : ℕ) (origin : Fin q → ℝ)
    {side : ℝ≥0} (hside : 0 < side)
    {U : Set (Fin q → ℝ)} (hU : MeasurableSet U)
    (hsub : U ⊆ legalInputPhysicalBox q origin side) (hpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    let _window := isProbabilityMeasure_legalInputWindowLaw q origin hside hU hsub hpos
    (twoMarkedCloudLaw q ℝ ℝ α β (side ^ q)).map
      (Prod.map (legalInputWindowPrefix q origin side U) (legalInputWindowPrefix q origin side U)) =
      (blockDataLaw ((normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)).prod α)
        (fun n ↦ poissonMeasure (volume U).toNNReal {n})).prod
      (blockDataLaw ((normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)).prod β)
        (fun n ↦ poissonMeasure (volume U).toNNReal {n})) := by
  dsimp only
  let : IsProbabilityMeasure (normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)) :=
    isProbabilityMeasure_legalInputWindowLaw q origin hside hU hsub hpos
  change ((markedPoissonLaw q ℝ α (side ^ q)).prod (markedPoissonLaw q ℝ β (side ^ q))).map _ = _
  rw [← Measure.map_prod_map _ _ (measurable_legalInputWindowPrefix q origin side hU)
    (measurable_legalInputWindowPrefix q origin side hU),
    map_legalInputWindowPrefix_markedPoissonLaw q origin hside hU hsub hpos α,
    map_legalInputWindowPrefix_markedPoissonLaw q origin hside hU hsub hpos β]

end OTSelector.Reconstruction
