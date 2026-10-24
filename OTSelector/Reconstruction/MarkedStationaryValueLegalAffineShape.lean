import OTSelector.Reconstruction.MarkedStationaryValueLegalShapeLaw
import OTSelector.Probability.BlockDataTransport
import OTSelector.Probability.MarkedCloudCarriers

/-! Literal legal quadratic values under translated and rescaled microscopic
coordinates. Physical displacements are never clamped. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- An actual affine microbox coordinate map, leaving the original mark fixed. -/
def affineMarkedPoint (origin : Fin q → ℝ) (side : ℝ)
    (p : (Fin q → ℝ) × A) : (Fin q → ℝ) × A :=
  (fun l ↦ origin l + side * p.1 l, p.2)

theorem measurable_affineMarkedPoint (origin : Fin q → ℝ) (side : ℝ) :
    Measurable (affineMarkedPoint (A := A) origin side) := by
  unfold affineMarkedPoint
  fun_prop

/-- The actual finite legal value with the true spatial difference y-x. -/
def unclampedBlockLegalTilted (q : ℕ) (source : A → ℝ) (target : B → ℝ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) : ℝ :=
  PartialMatching.legalMaximumValue
    (scalarClockLegalGraph (fun i ↦ source (dS.2 i).2) (fun j ↦ target (dT.2 j).2))
    (fun i j ↦ r ^ (2 / (q : ℝ)) * kin (dS.2 i).2 (dT.2 j).2
      (fun l ↦ (dT.2 j).1 l - (dS.2 i).1 l) + t * probe (dS.2 i).2 (dT.2 j).2)

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- On the original unit cube, global domination by truncation changes no edge. -/
theorem unclampedBlockLegalTilted_eq_block (q : ℕ)
    (source : A → ℝ) (target : B → ℝ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B))
    (hS : ∀ i, (dS.2 i).1 ∈ unitCube q) (hT : ∀ j, (dT.2 j).1 ∈ unitCube q) :
    unclampedBlockLegalTilted q source target r kin probe t dS dT =
      blockLegalTilted q source target r kin probe t dS dT := by
  unfold unclampedBlockLegalTilted blockLegalTilted
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j _
  have hd : mDisplacement (dS.2 i).1 (dT.2 j).1 =
      (fun l ↦ (dT.2 j).1 l - (dS.2 i).1 l) := by
    unfold mDisplacement
    rw [cubeTruncPoint_eq_of_mem (hT j), cubeTruncPoint_eq_of_mem (hS i)]
  rw [hd]

/-- The physical intensity under dilation changes by the actual q-dimensional
volume factor. This identity also includes zero ambient intensity. -/
theorem rpow_affine_intensity (q : ℕ) (hq : 0 < q) {r side : ℝ}
    (hr : 0 ≤ r) (hside : 0 ≤ side) :
    (r * side ^ q) ^ (2 / (q : ℝ)) = r ^ (2 / (q : ℝ)) * side ^ 2 := by
  rw [Real.mul_rpow hr (pow_nonneg hside q)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hside]
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have he : (q : ℝ) * (2 / (q : ℝ)) = 2 := by field_simp
  rw [he, Real.rpow_two]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- The same finite observations and the same allowed graph transform exactly
under any affine microbox coordinates and the physical intensity volume factor. -/
theorem unclampedBlockLegalTilted_affine (q : ℕ) (hq : 0 < q)
    (source : A → ℝ) (target : B → ℝ) {r side : ℝ}
    (hr : 0 ≤ r) (hside : 0 ≤ side) (origin : Fin q → ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    (probe : A → B → ℝ) (t : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) :
    unclampedBlockLegalTilted q source target r kin probe t
      (mapBlockData (affineMarkedPoint origin side) dS)
      (mapBlockData (affineMarkedPoint origin side) dT) =
        unclampedBlockLegalTilted q source target (r * side ^ q) kin probe t dS dT := by
  unfold unclampedBlockLegalTilted
  congr 1
  funext i j
  change r ^ (2 / (q : ℝ)) * kin (dS.2 i).2 (dT.2 j).2
      (fun l ↦ (origin l + side * (dT.2 j).1 l) - (origin l + side * (dS.2 i).1 l)) + _ = _
  have hdiff : (fun l ↦ (origin l + side * (dT.2 j).1 l) -
      (origin l + side * (dS.2 i).1 l)) =
      (fun l ↦ side * ((dT.2 j).1 l - (dS.2 i).1 l)) := by funext l; ring
  rw [hdiff, hhom _ _ side hside, rpow_affine_intensity q hq hr hside]
  simp only [mapBlockData, affineMarkedPoint]
  ring

/-- All stored coordinates belonging to a measurable spatial set is a
measurable event even though the observed point count is random. -/
theorem measurableSet_blockSpatialCarrier {U : Set (Fin q → ℝ)}
    (hU : MeasurableSet U) :
    MeasurableSet {d : BlockData ((Fin q → ℝ) × A) | ∀ i, (d.2 i).1 ∈ U} := by
  change MeasurableSet[⨅ n : ℕ,
    (inferInstance : MeasurableSpace (Fin n → (Fin q → ℝ) × A)).map (Sigma.mk n)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet {d : Fin n → (Fin q → ℝ) × A | ∀ i, (d i).1 ∈ U}
  simpa only [ofPred_forall, preimage] using MeasurableSet.iInter (fun i : Fin n ↦
    hU.preimage ((measurable_pi_apply i : Measurable
      (fun d : Fin n → (Fin q → ℝ) × A ↦ d i)).fst))

/-- The exact original normalized shape laws remain supported on the unit
cube, including the zero-mass shape case with its zero Poisson count. -/
theorem ae_shapeBlockLaw_unitCube_two (q : ℕ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S) :
    ∀ᵐ d ∂(shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S),
      (∀ i, (d.1.2 i).1 ∈ unitCube q) ∧ (∀ j, (d.2.2 j).1 ∈ unitCube q) := by
  have hEvent : MeasurableSet {d : BlockData ((Fin q → ℝ) × A) ×
      BlockData ((Fin q → ℝ) × B) |
      (∀ i, (d.1.2 i).1 ∈ unitCube q) ∧ (∀ j, (d.2.2 j).1 ∈ unitCube q)} :=
    ((measurableSet_blockSpatialCarrier (A := A) (measurableSet_unitCube q)).preimage
      measurable_fst).inter
      ((measurableSet_blockSpatialCarrier (A := B) (measurableSet_unitCube q)).preimage
      measurable_snd)
  rw [← map_shapeCloud_twoMarkedCloudLaw q α β r hS]
  apply (ae_map_iff ((measurable_shapeCloud (A := A) hS).prodMap
    (measurable_shapeCloud (A := B) hS)).aemeasurable hEvent).mpr
  filter_upwards [ae_points_mem_unitCube_twoMarkedCloudLaw q α β r] with ω hω
  constructor
  · intro i
    change ((shapeCloud S ω.1).2 i).1 ∈ unitCube q
    rw [shapeCloud_point]
    exact hω.1 (shapeCloudEmbedding S ω.1 i)
  · intro j
    change ((shapeCloud S ω.2).2 j).1 ∈ unitCube q
    rw [shapeCloud_point]
    exact hω.2 (shapeCloudEmbedding S ω.2 j)

/-- The real physical affine microbox value has the original shape-law
expectation, with local intensity r*side^q, unchanged conditional marks and
an explicit original hole-mass error. -/
theorem FiniteScalarBins.integrable_affine_shapeBlockValue_compare_legalPressure
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) (hq : 0 < q) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r side : ℝ≥0) (origin : Fin q → ℝ) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, source a < target b → |g a b| ≤ G) (t : ℝ) :
    let localIntensity := r * side ^ q
    let law := (shapeBlockLaw q α localIntensity S).prod
      (shapeBlockLaw q β localIntensity S)
    let value := fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      unclampedBlockLegalTilted q source target r kin g t
        (mapBlockData (affineMarkedPoint origin side) d.1)
        (mapBlockData (affineMarkedPoint origin side) d.2)
    Integrable value law ∧
    |(∫ d, value d ∂law) - legalMarkedPressure q source target α β localIntensity kin g t| ≤
      (2 * (localIntensity : ℝ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) *
          ((localIntensity : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G)) := by
  dsimp only
  let localIntensity := r * side ^ q
  obtain ⟨hInt, hbound⟩ := D.integrable_shapeBlockValue_compare_legalPressure hgap q hs ht
    α β localIntensity hS hsource hsep hC hG hk hkb hg hgb t
  have hcoerce : (r : ℝ) * (side : ℝ) ^ q = (localIntensity : ℝ) := by
    simp only [localIntensity, NNReal.coe_mul, NNReal.coe_pow]
  have heq : (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      unclampedBlockLegalTilted q source target r kin g t
        (mapBlockData (affineMarkedPoint origin side) d.1)
        (mapBlockData (affineMarkedPoint origin side) d.2)) =ᵐ[
      (shapeBlockLaw q α localIntensity S).prod (shapeBlockLaw q β localIntensity S)]
      fun d ↦ blockLegalTilted q source target localIntensity kin g t d.1 d.2 := by
    filter_upwards [ae_shapeBlockLaw_unitCube_two q α β localIntensity hS] with d hd
    rw [unclampedBlockLegalTilted_affine q hq source target r.coe_nonneg side.coe_nonneg
      origin kin hhom g t, hcoerce]
    exact unclampedBlockLegalTilted_eq_block q source target localIntensity kin g t d.1 d.2 hd.1 hd.2
  refine ⟨hInt.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  exact hbound

end OTSelector.Reconstruction
