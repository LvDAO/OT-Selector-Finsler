import OTSelector.Reconstruction.MarkedStationaryValueLegalGridComparison
import OTSelector.Probability.GridRepairArithmetic
import OTSelector.Probability.GridRepairError

/-! Exact original legal leaf pressures and expectation for an arbitrary grid. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- Padded labels outside the real grid have no legal edges. -/
theorem gridLegalValue_zero_of_not_lt (q m J : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (source : A → ℝ) (target : B → ℝ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) (c : Fin q → Fin (2 ^ J + 1))
    (hc : ¬∀ l, (c l).val < m) :
    gridLegalValue q m J J hm hJ source target r kin probe t ω c = 0 := by
  obtain ⟨l, hl⟩ : ∃ l, ¬(c l).val < m := not_forall.mp hc
  have hgraph : spatialLegalMarkedGraph q (mSourceCount ω) (mTargetCount ω)
      (gridCellLabel q m J J hm hJ) source target c ω = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hcell := (Finset.mem_filter.mp he).2.1
    change gridCellLabel q m J J hm hJ (mSourcePoint ω e.1) = c at hcell
    have hv := gridCellLabel_leaf_val_lt hm hJ (mSourcePoint ω e.1) l
    rw [hcell] at hv
    exact hl hv
  rw [gridLegalValue, hgraph, PartialMatching.legalMaximumValue_empty]

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- All literal legal padded leaves sum exactly over the real uniform blocks. -/
theorem gridLegalValue_sum_eq_realBlocks (q m J : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (source : A → ℝ) (target : B → ℝ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) :
    (∑ c : Fin q → Fin (2 ^ J + 1), gridLegalValue q m J J hm hJ source target r kin probe t ω c) =
      ∑ b : Fin q → Fin m, gridLegalValue q m J J hm hJ source target r kin probe t ω
        (blockLeafLabel q m J hJ b) := by
  let f := gridLegalValue q m J J hm hJ source target r kin probe t ω
  let S : Finset (Fin q → Fin (2 ^ J + 1)) := Finset.univ.filter (fun c ↦ ∀ l, (c l).val < m)
  have hzero : ∀ c ∈ (Finset.univ : Finset (Fin q → Fin (2 ^ J + 1))), c ∉ S → f c = 0 := by
    intro c _ hc
    exact gridLegalValue_zero_of_not_lt q m J hm hJ source target r kin probe t ω c
      (fun h ↦ hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  rw [← Finset.sum_subset (Finset.subset_univ S) hzero]
  let ρ : (c : Fin q → Fin (2 ^ J + 1)) → c ∈ S → (Fin q → Fin m) :=
    fun c hc l ↦ ⟨(c l).val, (Finset.mem_filter.mp hc).2 l⟩
  refine Finset.sum_bij (i := ρ) (fun c hc ↦ Finset.mem_univ _) ?_ ?_ ?_
  · intro c hc d hd heq
    funext l
    apply Fin.ext
    exact congrArg (fun b : Fin q → Fin m ↦ (b l).val) heq
  · intro b _
    refine ⟨blockLeafLabel q m J hJ b, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l ↦ blockLeafLabel_lt q m J hJ b l⟩
    · funext l
      apply Fin.ext
      rfl
  · intro c hc
    apply congrArg f
    funext l
    apply Fin.ext
    rfl

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- The original-index leaf graph is the actual raw selected block graph. -/
theorem gridLegalGraph_real_eq_rawBlock (q m J : ℕ) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (source : A → ℝ) (target : B → ℝ) (ω : TwoMarkedCloudSpace q A B)
    (hS : ∀ i, mSourcePoint ω i ∈ unitCube q) (hT : ∀ j, mTargetPoint ω j ∈ unitCube q)
    (b : Fin q → Fin m) :
    spatialLegalMarkedGraph q (mSourceCount ω) (mTargetCount ω)
      (gridCellLabel q m J J hm hJ) source target (blockLeafLabel q m J hJ b) ω =
      rawBlockLegalGraph q m b source target ω := by
  ext e
  simp only [spatialLegalMarkedGraph, PartialMatching.spatialLegalBlock, rawBlockLegalGraph,
    Finset.mem_filter]
  rw [gridCellLabel_leaf_eq_iff hm hJ (hS e.1) b,
    gridCellLabel_leaf_eq_iff hm hJ (hT e.2) b]
  simp only [blockLocalFilter, Finset.mem_filter, Finset.mem_univ, true_and,
    mSourcePoint, mTargetPoint]

/-- Each actual original legal leaf value has the rescaled actual legal
pressure as its expectation, with integrability produced from original bounds. -/
theorem gridLegalValue_real_integrable_integral (q m J : ℕ) (hq : 0 < q)
    (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (r : ℝ≥0) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) (b : Fin q → Fin m) :
    Integrable (fun ω ↦ gridLegalValue q m J J hm hJ source target r kin probe t ω
      (blockLeafLabel q m J hJ b)) (twoMarkedCloudLaw q A B α β r) ∧
    (∫ ω, gridLegalValue q m J J hm hJ source target r kin probe t ω (blockLeafLabel q m J hJ b)
      ∂twoMarkedCloudLaw q A B α β r) =
      legalMarkedPressure q source target α β (r / (m ^ q : ℝ≥0)) kin probe t := by
  obtain ⟨hInt, hmean⟩ := blockLocalCloud_legalTilted_integral q m hm
    hs ht r α β b hC hG hk hkb hp hpb t
  have hcoe : ((r / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ) = (r : ℝ) / ((m : ℝ) ^ q) := by simp
  have hae : (fun ω ↦ gridLegalValue q m J J hm hJ source target r kin probe t ω
      (blockLeafLabel q m J hJ b)) =ᵐ[twoMarkedCloudLaw q A B α β r]
        fun ω ↦ blockLegalTilted q source target ((r / (m ^ q : ℝ≥0) : ℝ≥0) : ℝ) kin probe t
          (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2) := by
    filter_upwards [ae_points_mem_unitCube_twoMarkedCloudLaw q α β r] with ω hω
    rw [gridLegalValue, gridLegalGraph_real_eq_rawBlock q m J hm hJ source target ω hω.1 hω.2 b,
      hcoe]
    exact rawBlockLegalValue_eq_local q m hq hm b source target r.coe_nonneg kin hhom probe t
      ω hω.1 hω.2
  exact ⟨hInt.congr hae.symm, (integral_congr_ae hae).trans hmean⟩

/-- The full actual legal leaf sum has exactly m^q times the smaller-intensity
original legal pressure as its mean. -/
theorem gridLegalValue_sum_integrable_integral (q m J : ℕ) (hq : 0 < q)
    (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (r : ℝ≥0) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    Integrable (fun ω ↦ ∑ b : Fin q → Fin (2 ^ J + 1),
      gridLegalValue q m J J hm hJ source target r kin probe t ω b)
      (twoMarkedCloudLaw q A B α β r) ∧
    (∫ ω, ∑ b : Fin q → Fin (2 ^ J + 1), gridLegalValue q m J J hm hJ source target r kin probe t ω b
      ∂twoMarkedCloudLaw q A B α β r) =
      ((m ^ q : ℕ) : ℝ) * legalMarkedPressure q source target α β (r / (m ^ q : ℝ≥0)) kin probe t := by
  have hblock (b : Fin q → Fin m) := gridLegalValue_real_integrable_integral q m J hq hm hJ
    hs ht r α β hC hG hk hkb hhom hp hpb t b
  have heq : (fun ω ↦ ∑ b : Fin q → Fin (2 ^ J + 1),
      gridLegalValue q m J J hm hJ source target r kin probe t ω b) =
      (fun ω ↦ ∑ b : Fin q → Fin m, gridLegalValue q m J J hm hJ source target r kin probe t ω
        (blockLeafLabel q m J hJ b)) :=
    funext (gridLegalValue_sum_eq_realBlocks q m J hm hJ source target r kin probe t)
  rw [heq]
  refine ⟨integrable_finsetSum _ (fun b _ ↦ (hblock b).1), ?_⟩
  rw [integral_finsetSum _ (fun b _ ↦ (hblock b).1)]
  simp only [fun b ↦ (hblock b).2, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul]

set_option maxHeartbeats 1400000 in
/-- Every repair and leaf expectation in the actual arbitrary-grid pressure
comparison is supplied by the original scalar-bin population and cloud law. -/
theorem scalarBinPopulationTypes_legalPressure_le_grid
    {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace J] [MeasurableSingletonClass J] [Fintype J]
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ) (hIm : MeasurableSet I)
    [MeasurableSpace (Option (J × Fin D.count × Fin D.count))]
    [MeasurableSingletonClass (Option (J × Fin D.count × Fin D.count))]
    (chart : X × Y → J) (source : X → ℝ) (target : Y → ℝ)
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) (hchart : Measurable chart)
    (hs : Measurable source) (ht : Measurable target)
    (hI : ∀ᵐ p ∂π, source p.1 ∈ I ∧ target p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1)
    (hsep : ∀ᵐ p ∂μ.prod ν, δ ≤ |target p.2 - source p.1|)
    (q m depth : ℕ) (hq : 0 < q) (hm : 0 < m) (hdepth : m ≤ 2 ^ depth)
    (hdepth2 : 2 ^ depth ≤ 2 * m) (r : ℝ≥0) {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : X → Y → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : X × Y ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {probe : X → Y → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) :
    legalMarkedPressure q source target μ ν r kin probe t ≤
      ((m ^ q : ℕ) : ℝ) *
        legalMarkedPressure q source target μ ν (r / (m ^ q : ℝ≥0)) kin probe t +
      ∑ k ∈ Finset.range depth,
        Real.sqrt (2 * (r : ℝ) *
          ((((2 ^ (k + 1) + 1) ^ q : ℕ) : ℝ) *
            Fintype.card (Option (J × Fin D.count × Fin D.count)))) *
          (2 * ((D.count : ℝ) + 1) * legalGridEdgeBound q r C G t k) := by
  have hμI : ∀ᵐ x ∂μ, source x ∈ I := by
    rw [← hπ.1]
    exact (ae_map_iff measurable_fst.aemeasurable (hs hIm)).mpr (hI.mono (fun _ h ↦ h.1))
  have hsource := ae_all_sourceMarks q μ ν r (fun x ↦ source x ∈ I) hμI
  have hsepcloud := ae_all_crossMarks q μ ν r
    (fun p ↦ δ ≤ |target p.2 - source p.1|) hsep
  have hleaf := gridLegalValue_sum_integrable_integral q m depth hq hm hdepth hs ht r μ ν
    hC hG hk hkb hhom hp hpb t
  have hdef (k : ℕ) := scalarBinPopulationTypes_poisson_spatialSourceDefect D hδ
    chart source target π μ ν hπ hchart hs ht hI hgap q
      (gridCellLabel q m depth (k + 1) hm hdepth)
      (measurable_gridCellLabel q m depth (k + 1) hm hdepth) r
  have hrep : Integrable (fun ω : TwoMarkedCloudSpace q X Y ↦
      ∑ k ∈ Finset.range depth, spatialLegalMarkedSourceDefectSum q
        (gridCellLabel q m depth (k + 1) hm hdepth) source target ω *
          (2 * ((D.count : ℝ) + 1) * legalGridEdgeBound q r C G t k))
      (twoMarkedCloudLaw q X Y μ ν r) :=
    integrable_finsetSum _ (fun k _ ↦ (hdef k).1.mul_const _)
  have htotal : Integrable (fun ω : TwoMarkedCloudSpace q X Y ↦
      (∑ b : Fin q → Fin (2 ^ depth + 1),
        gridLegalValue q m depth depth hm hdepth source target r kin probe t ω b) +
      ∑ k ∈ Finset.range depth, spatialLegalMarkedSourceDefectSum q
        (gridCellLabel q m depth (k + 1) hm hdepth) source target ω *
          (2 * ((D.count : ℝ) + 1) * legalGridEdgeBound q r C G t k))
      (twoMarkedCloudLaw q X Y μ ν r) := hleaf.1.add hrep
  have hpt : ∀ᵐ ω ∂twoMarkedCloudLaw q X Y μ ν r,
      legalMarkedTilted q source target r kin probe t ω ≤
      (∑ b : Fin q → Fin (2 ^ depth + 1),
        gridLegalValue q m depth depth hm hdepth source target r kin probe t ω b) +
      ∑ k ∈ Finset.range depth, spatialLegalMarkedSourceDefectSum q
        (gridCellLabel q m depth (k + 1) hm hdepth) source target ω *
          (2 * ((D.count : ℝ) + 1) * legalGridEdgeBound q r C G t k) := by
    filter_upwards [ae_points_mem_unitCube_twoMarkedCloudLaw q μ ν r,
      hsource, hsepcloud] with ω hω hsrc hsepω
    exact D.legalMarkedTilted_le_grid hδ q m depth hm hdepth hdepth2 source target r.coe_nonneg
      hC hG (fun a b _ ↦ hkb a b) (fun a b _ ↦ hpb a b) t ω hω.1 hω.2 hsrc hsepω
  have h := integral_mono_ae (integrable_legalMarkedTilted q hs ht μ ν r hC hG
    hk hkb hp hpb t) htotal hpt
  rw [integral_add hleaf.1 hrep, hleaf.2,
    integral_finsetSum _ (fun k _ ↦ (hdef k).1.mul_const _)] at h
  refine h.trans (add_le_add le_rfl (Finset.sum_le_sum ?_))
  intro k _
  rw [integral_mul_const]
  apply mul_le_mul_of_nonneg_right _
    (mul_nonneg (by positivity) (legalGridEdgeBound_nonneg q k r.coe_nonneg hC hG))
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_mul] using (hdef k).2

end OTSelector.Reconstruction
