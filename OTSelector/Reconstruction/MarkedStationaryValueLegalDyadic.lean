import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonBlock
import OTSelector.Reconstruction.MarkedStationaryValueLegalEmbedding
import OTSelector.Reconstruction.MarkedStationaryValueLegalMultiscale
import OTSelector.Probability.MarkedBlockComparison

/-!
# Actual dyadic legal subcloud defects

The finite raw block enumeration carries the original legal graph exactly.
On the original cube-supported Poisson law its graph is the literal dyadic
hierarchy graph, so the proved original source-defect estimate applies directly.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Original vertex indices of the stored raw block prefix. -/
def rawBlockEmbedding (q m : ℕ) (b : Fin q → Fin m) (z : MarkedCloudSpace q A) :
    Fin (blockLocalCloud q m b z).1 ↪ Fin z.1 where
  toFun i := ((blockLocalFilter q m b z).orderIsoOfFin rfl i).1
  inj' := by
    intro i j h
    apply ((blockLocalFilter q m b z).orderIsoOfFin rfl).injective
    exact Subtype.ext h

omit [MeasurableSpace A] in
theorem mem_range_rawBlockEmbedding (q m : ℕ) (b : Fin q → Fin m)
    (z : MarkedCloudSpace q A) (i : Fin z.1) :
    i ∈ range (rawBlockEmbedding q m b z) ↔ i ∈ blockLocalFilter q m b z := by
  constructor
  · rintro ⟨j, rfl⟩
    exact ((blockLocalFilter q m b z).orderIsoOfFin rfl j).2
  · intro hi
    refine ⟨((blockLocalFilter q m b z).orderIsoOfFin rfl).symm ⟨i, hi⟩, ?_⟩
    exact congrArg Subtype.val (((blockLocalFilter q m b z).orderIsoOfFin rfl).apply_symm_apply _)

/-- The ambient graph using the literal raw spatial block predicate. -/
def rawBlockLegalGraph (q m : ℕ) (b : Fin q → Fin m)
    (source : A → ℝ) (target : B → ℝ) (ω : TwoMarkedCloudSpace q A B) :
    Finset (Fin (mSourceCount ω) × Fin (mTargetCount ω)) :=
  (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) source target ω).filter
    (fun e ↦ e.1 ∈ blockLocalFilter q m b ω.1 ∧ e.2 ∈ blockLocalFilter q m b ω.2)

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem induced_rawBlockLegalGraph (q m : ℕ) (b : Fin q → Fin m)
    (source : A → ℝ) (target : B → ℝ) (ω : TwoMarkedCloudSpace q A B) :
    PartialMatching.inducedLegalGraph (rawBlockLegalGraph q m b source target ω)
      (rawBlockEmbedding q m b ω.1) (rawBlockEmbedding q m b ω.2) =
      scalarClockLegalGraph
        (fun i ↦ source ((blockLocalCloud q m b ω.1).2 i).2)
        (fun j ↦ target ((blockLocalCloud q m b ω.2).2 j).2) := by
  ext e
  have hS : rawBlockEmbedding q m b ω.1 e.1 ∈ blockLocalFilter q m b ω.1 :=
    ((blockLocalFilter q m b ω.1).orderIsoOfFin rfl e.1).2
  have hT : rawBlockEmbedding q m b ω.2 e.2 ∈ blockLocalFilter q m b ω.2 :=
    ((blockLocalFilter q m b ω.2).orderIsoOfFin rfl e.2).2
  simp only [PartialMatching.inducedLegalGraph, rawBlockLegalGraph, legalMarkedGraph,
    scalarClockLegalGraph, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, hS, hT⟩

omit [MeasurableSpace A] [MeasurableSpace B] in
/-- The raw stored subcloud has the actual ambient legal rank. -/
theorem legalMaximumCard_rawBlockLegalGraph (q m : ℕ) (b : Fin q → Fin m)
    (source : A → ℝ) (target : B → ℝ) (ω : TwoMarkedCloudSpace q A B) :
    PartialMatching.legalMaximumCard (rawBlockLegalGraph q m b source target ω) =
      PartialMatching.legalMaximumCard (scalarClockLegalGraph
        (fun i ↦ source ((blockLocalCloud q m b ω.1).2 i).2)
        (fun j ↦ target ((blockLocalCloud q m b ω.2).2 j).2)) := by
  have hcarry : ∀ p ∈ rawBlockLegalGraph q m b source target ω,
      p.1 ∈ range (rawBlockEmbedding q m b ω.1) ∧
      p.2 ∈ range (rawBlockEmbedding q m b ω.2) := by
    intro p hp
    exact ⟨(mem_range_rawBlockEmbedding q m b ω.1 p.1).mpr (Finset.mem_filter.mp hp).2.1,
      (mem_range_rawBlockEmbedding q m b ω.2 p.2).mpr (Finset.mem_filter.mp hp).2.2⟩
  rw [← PartialMatching.legalMaximumCard_inducedLegalGraph _ _ _ hcarry,
    induced_rawBlockLegalGraph]

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem rawBlockSourceDefect_eq (q m : ℕ) (b : Fin q → Fin m)
    (source : A → ℝ) (target : B → ℝ) (ω : TwoMarkedCloudSpace q A B) :
    ((blockLocalFilter q m b ω.1).card : ℝ) -
      PartialMatching.legalMaximumCard (rawBlockLegalGraph q m b source target ω) =
      blockLegalSourceDefect q source target
        (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2) := by
  rw [legalMaximumCard_rawBlockLegalGraph]
  rfl

/-- On the original unit cube, the dyadic cell is the raw floor block label. -/
theorem dyadicCell_eq_iff_blockIndex (q k : ℕ) {x : Fin q → ℝ}
    (hx : x ∈ unitCube q) (b : Fin q → Fin (2 ^ k)) :
    dyadicCell q k x = b ↔
      ∀ l, blockIndex (((2 ^ k : ℕ) : ℝ)⁻¹) (x l) = (b l).val := by
  have hxc (l) : 0 ≤ x l ∧ x l < 1 := by
    have := Set.mem_pi.mp hx l (mem_univ l)
    exact ⟨this.1.le, this.2⟩
  rw [funext_iff]
  simp only [Fin.ext_iff, dyadicCell_eq_floor_of_nonneg (fun l ↦ (hxc l).1)
    (fun l ↦ (hxc l).2)]
  simp only [blockIndex, div_inv_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm]

/-- The exact hierarchy graph on the actual original cloud. -/
def dyadicLegalGraph (q k : ℕ) (source : A → ℝ) (target : B → ℝ)
    (ω : TwoMarkedCloudSpace q A B) (b : Fin q → Fin (2 ^ k)) :=
  PartialMatching.spatialLegalBlock
    (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) source target ω)
    (fun i ↦ dyadicCell q k (mSourcePoint ω i))
    (fun j ↦ dyadicCell q k (mTargetPoint ω j)) b

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem dyadicLegalGraph_eq_rawBlock (q k : ℕ) (source : A → ℝ) (target : B → ℝ)
    (ω : TwoMarkedCloudSpace q A B) (hS : ∀ i, mSourcePoint ω i ∈ unitCube q)
    (hT : ∀ j, mTargetPoint ω j ∈ unitCube q) (b : Fin q → Fin (2 ^ k)) :
    dyadicLegalGraph q k source target ω b = rawBlockLegalGraph q (2 ^ k) b source target ω := by
  ext e
  simp only [dyadicLegalGraph, PartialMatching.spatialLegalBlock, rawBlockLegalGraph,
    Finset.mem_filter]
  rw [dyadicCell_eq_iff_blockIndex q k (hS e.1) b,
    dyadicCell_eq_iff_blockIndex q k (hT e.2) b]
  simp only [blockLocalFilter, Finset.mem_filter, Finset.mem_univ, true_and,
    mSourcePoint, mTargetPoint]

/-- The source-only defect which occurs literally in the finite hierarchy. -/
def dyadicLegalSourceDefect (q k : ℕ) (source : A → ℝ) (target : B → ℝ)
    (ω : TwoMarkedCloudSpace q A B) (b : Fin q → Fin (2 ^ k)) : ℝ :=
  (((OTSelector.blockFinset (fun i : Fin (mSourceCount ω) ↦
      dyadicCell q k (mSourcePoint ω i)) b).card -
    PartialMatching.legalMaximumCard (dyadicLegalGraph q k source target ω b) : ℕ) : ℝ)

omit [MeasurableSpace A] [MeasurableSpace B] in
theorem dyadicLegalSourceDefect_eq_block (q k : ℕ)
    (source : A → ℝ) (target : B → ℝ) (ω : TwoMarkedCloudSpace q A B)
    (hS : ∀ i, mSourcePoint ω i ∈ unitCube q)
    (hT : ∀ j, mTargetPoint ω j ∈ unitCube q) (b : Fin q → Fin (2 ^ k)) :
    dyadicLegalSourceDefect q k source target ω b = blockLegalSourceDefect q source target
      (blockLocalCloud q (2 ^ k) b ω.1) (blockLocalCloud q (2 ^ k) b ω.2) := by
  have hcard := PartialMatching.spatialLegalBlock_source_card_le
    (legalMarkedGraph q (mSourceCount ω) (mTargetCount ω) source target ω)
    (fun i ↦ dyadicCell q k (mSourcePoint ω i))
    (fun j ↦ dyadicCell q k (mTargetPoint ω j)) b
  change PartialMatching.legalMaximumCard (dyadicLegalGraph q k source target ω b) ≤ _ at hcard
  have hfilter : OTSelector.blockFinset
      (fun i : Fin (mSourceCount ω) ↦ dyadicCell q k (mSourcePoint ω i)) b =
      blockLocalFilter q (2 ^ k) b ω.1 := by
    ext i
    simp only [OTSelector.mem_blockFinset, blockLocalFilter, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact dyadicCell_eq_iff_blockIndex q k (hS i) b
  unfold dyadicLegalSourceDefect
  rw [Nat.cast_sub hcard, hfilter, dyadicLegalGraph_eq_rawBlock q k source target ω hS hT b]
  exact rawBlockSourceDefect_eq q (2 ^ k) b source target ω

/-- The actual original cube law identifies each literal hierarchy defect with
the finite prefix of the actual smaller-intensity original cloud. -/
theorem dyadicLegalSourceDefect_ae_eq_block (q k : ℕ)
    (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (b : Fin q → Fin (2 ^ k)) :
    (fun ω ↦ dyadicLegalSourceDefect q k source target ω b) =ᵐ[
      twoMarkedCloudLaw q A B α β r] fun ω ↦ blockLegalSourceDefect q source target
        (blockLocalCloud q (2 ^ k) b ω.1) (blockLocalCloud q (2 ^ k) b ω.2) := by
  filter_upwards [ae_points_mem_unitCube_twoMarkedCloudLaw q α β r] with ω hω
  exact dyadicLegalSourceDefect_eq_block q k source target ω hω.1 hω.2 b

/-- Original scalar-bin coupling data supply an integrable square-root bound
for each actual dyadic hierarchy source defect. -/
theorem scalarBinPopulationTypes_poisson_dyadicSourceDefect
    {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace J] [MeasurableSingletonClass J] [Fintype J]
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    [MeasurableSpace (Option (J × Fin D.count × Fin D.count))]
    [MeasurableSingletonClass (Option (J × Fin D.count × Fin D.count))]
    (chart : X × Y → J) (source : X → ℝ) (target : Y → ℝ)
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) (hchart : Measurable chart)
    (hs : Measurable source) (ht : Measurable target)
    (hI : ∀ᵐ p ∂π, source p.1 ∈ I ∧ target p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1)
    (q k : ℕ) (r : ℝ≥0) (b : Fin q → Fin (2 ^ k)) :
    Integrable (fun ω : TwoMarkedCloudSpace q X Y ↦ dyadicLegalSourceDefect q k source target ω b)
      (twoMarkedCloudLaw q X Y μ ν r) ∧
    (∫ ω, dyadicLegalSourceDefect q k source target ω b
      ∂twoMarkedCloudLaw q X Y μ ν r) ≤
      Real.sqrt (2 * ((r / ((2 ^ k : ℕ) ^ q : ℝ≥0) : ℝ≥0) : ℝ) *
        Fintype.card (Option (J × Fin D.count × Fin D.count))) := by
  obtain ⟨hInt, hbound⟩ := scalarBinPopulationTypes_poisson_blockSourceDefect D hδ chart
    source target π μ ν hπ hchart hs ht hI hgap q (2 ^ k) (by positivity) r b
  have hae := dyadicLegalSourceDefect_ae_eq_block q k source target μ ν r b
  exact ⟨hInt.congr hae.symm, (integral_congr_ae hae).trans_le hbound⟩

/-- Summing the actual original child source deficiencies has the sharp
square-root dependence on the number of spatial cells. -/
theorem scalarBinPopulationTypes_poisson_dyadicSourceDefect_sum
    {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace J] [MeasurableSingletonClass J] [Fintype J]
    {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ) (hδ : 0 < δ)
    [MeasurableSpace (Option (J × Fin D.count × Fin D.count))]
    [MeasurableSingletonClass (Option (J × Fin D.count × Fin D.count))]
    (chart : X × Y → J) (source : X → ℝ) (target : Y → ℝ)
    (π : Measure (X × Y)) [IsFiniteMeasure π]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) (hchart : Measurable chart)
    (hs : Measurable source) (ht : Measurable target)
    (hI : ∀ᵐ p ∂π, source p.1 ∈ I ∧ target p.2 ∈ I)
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1)
    (q k : ℕ) (r : ℝ≥0) :
    Integrable (fun ω : TwoMarkedCloudSpace q X Y ↦
      ∑ b : Fin q → Fin (2 ^ k), dyadicLegalSourceDefect q k source target ω b)
      (twoMarkedCloudLaw q X Y μ ν r) ∧
    (∫ ω, ∑ b : Fin q → Fin (2 ^ k), dyadicLegalSourceDefect q k source target ω b
      ∂twoMarkedCloudLaw q X Y μ ν r) ≤
      Real.sqrt (2 * (r : ℝ) * Fintype.card (Option (J × Fin D.count × Fin D.count)) *
        (((2 ^ k : ℕ) ^ q : ℕ) : ℝ)) := by
  have hblock (b : Fin q → Fin (2 ^ k)) :=
    scalarBinPopulationTypes_poisson_dyadicSourceDefect D hδ chart source target π μ ν
      hπ hchart hs ht hI hgap q k r b
  refine ⟨integrable_finsetSum _ (fun b _ ↦ (hblock b).1), ?_⟩
  rw [integral_finsetSum _ (fun b _ ↦ (hblock b).1)]
  calc
    _ ≤ ∑ _b : Fin q → Fin (2 ^ k),
        Real.sqrt (2 * ((r / ((2 ^ k : ℕ) ^ q : ℝ≥0) : ℝ≥0) : ℝ) *
          Fintype.card (Option (J × Fin D.count × Fin D.count))) :=
      Finset.sum_le_sum (fun b _ ↦ (hblock b).2)
    _ = (((2 ^ k : ℕ) ^ q : ℕ) : ℝ) *
        Real.sqrt (2 * ((r / ((2 ^ k : ℕ) ^ q : ℝ≥0) : ℝ≥0) : ℝ) *
          Fintype.card (Option (J × Fin D.count × Fin D.count))) := by
      simp
    _ = _ := by
      have ha : (0 : ℝ) < (((2 ^ k : ℕ) ^ q : ℕ) : ℝ) := by positivity
      calc
        _ = Real.sqrt ((((2 ^ k : ℕ) ^ q : ℕ) : ℝ) ^ 2) *
            Real.sqrt (2 * ((r / ((2 ^ k : ℕ) ^ q : ℝ≥0) : ℝ≥0) : ℝ) *
              Fintype.card (Option (J × Fin D.count × Fin D.count))) := by
          rw [Real.sqrt_sq ha.le]
        _ = Real.sqrt (((((2 ^ k : ℕ) ^ q : ℕ) : ℝ) ^ 2) *
            (2 * ((r / ((2 ^ k : ℕ) ^ q : ℝ≥0) : ℝ≥0) : ℝ) *
              Fintype.card (Option (J × Fin D.count × Fin D.count)))) :=
          (Real.sqrt_mul (sq_nonneg _) _).symm
        _ = _ := by
          congr 1
          push_cast
          field_simp

/-- The actual ambient legal block minimum is precisely the local legal
finite-cloud minimum, at its rescaled physical intensity. -/
theorem rawBlockLegalValue_eq_local (q m : ℕ) (hq : 0 < q) (hm : 0 < m)
    (b : Fin q → Fin m) (source : A → ℝ) (target : B → ℝ)
    {r : ℝ} (hr : 0 ≤ r) (kin : A → B → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    (probe : A → B → ℝ) (t : ℝ) (ω : TwoMarkedCloudSpace q A B)
    (hS : ∀ i, mSourcePoint ω i ∈ unitCube q)
    (hT : ∀ j, mTargetPoint ω j ∈ unitCube q) :
    PartialMatching.legalMaximumValue (rawBlockLegalGraph q m b source target ω)
      (fun i j ↦ mKineticCost q r kin ω i j + t * mProbe probe ω i j) =
      blockLegalTilted q source target (r / ((m : ℝ) ^ q)) kin probe t
        (blockLocalCloud q m b ω.1) (blockLocalCloud q m b ω.2) := by
  have hcarry : ∀ p ∈ rawBlockLegalGraph q m b source target ω,
      p.1 ∈ range (rawBlockEmbedding q m b ω.1) ∧
      p.2 ∈ range (rawBlockEmbedding q m b ω.2) := by
    intro p hp
    exact ⟨(mem_range_rawBlockEmbedding q m b ω.1 p.1).mpr (Finset.mem_filter.mp hp).2.1,
      (mem_range_rawBlockEmbedding q m b ω.2 p.2).mpr (Finset.mem_filter.mp hp).2.2⟩
  rw [← PartialMatching.legalMaximumValue_inducedLegalGraph _ _ _ hcarry,
    induced_rawBlockLegalGraph]
  unfold blockLegalTilted
  congr 1
  funext i j
  have hpointS : (blockLocalCloud q m b ω.1).2 i =
      (blockScaledLocalPoint q m (mSourcePoint ω (rawBlockEmbedding q m b ω.1 i)),
        mSourceMark ω (rawBlockEmbedding q m b ω.1 i)) := rfl
  have hpointT : (blockLocalCloud q m b ω.2).2 j =
      (blockScaledLocalPoint q m (mTargetPoint ω (rawBlockEmbedding q m b ω.2 j)),
        mTargetMark ω (rawBlockEmbedding q m b ω.2 j)) := rfl
  rw [hpointS, hpointT]
  have hpS := mem_blockLocalFilter.mp
    (((blockLocalFilter q m b ω.1).orderIsoOfFin rfl i).2)
  have hpT := mem_blockLocalFilter.mp
    (((blockLocalFilter q m b ω.2).orderIsoOfFin rfl j).2)
  have hxy : ∀ l, blockIndex ((m : ℝ)⁻¹)
      (mSourcePoint ω (rawBlockEmbedding q m b ω.1 i) l) =
      blockIndex ((m : ℝ)⁻¹) (mTargetPoint ω (rawBlockEmbedding q m b ω.2 j) l) :=
    fun l ↦ (hpS l).trans (hpT l).symm
  have hk := mKineticCost_eq_local_of_same_block hm hq hr hhom
    (a := mSourceMark ω (rawBlockEmbedding q m b ω.1 i))
    (b := mTargetMark ω (rawBlockEmbedding q m b ω.2 j))
    (hS _) (hT _) hxy
  exact congrArg (fun x ↦ x + t * mProbe probe ω
    (rawBlockEmbedding q m b ω.1 i) (rawBlockEmbedding q m b ω.2 j)) hk

/-- The true legal dyadic block value in the original-index hierarchy. -/
def dyadicLegalValue (q k : ℕ) (source : A → ℝ) (target : B → ℝ) (r : ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q A B) (b : Fin q → Fin (2 ^ k)) : ℝ :=
  PartialMatching.legalMaximumValue (dyadicLegalGraph q k source target ω b)
    (fun i j ↦ mKineticCost q r kin ω i j + t * mProbe probe ω i j)

/-- Every actual legal dyadic block has the smaller-intensity original legal
pressure as its expectation. Integrability is produced from original bounds. -/
theorem dyadicLegalValue_integrable_integral (q k : ℕ) (hq : 0 < q)
    {source : A → ℝ} {target : B → ℝ} (hs : Measurable source) (ht : Measurable target)
    (r : ℝ≥0) (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hhom : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l ↦ c * v l) = c ^ 2 * kin a b v)
    {probe : A → B → ℝ} (hp : Measurable (Function.uncurry probe))
    (hpb : ∀ a b, |probe a b| ≤ G) (t : ℝ) (b : Fin q → Fin (2 ^ k)) :
    Integrable (fun ω ↦ dyadicLegalValue q k source target r kin probe t ω b)
      (twoMarkedCloudLaw q A B α β r) ∧
    (∫ ω, dyadicLegalValue q k source target r kin probe t ω b
      ∂twoMarkedCloudLaw q A B α β r) =
      legalMarkedPressure q source target α β (r / ((2 ^ k : ℕ) ^ q : ℝ≥0)) kin probe t := by
  obtain ⟨hInt, hmean⟩ := blockLocalCloud_legalTilted_integral q (2 ^ k) (by positivity)
    hs ht r α β b hC hG hk hkb hp hpb t
  have hcoe : ((r / ((2 ^ k : ℕ) ^ q : ℝ≥0) : ℝ≥0) : ℝ) =
      (r : ℝ) / (((2 ^ k : ℕ) : ℝ) ^ q) := by simp
  have hae : (fun ω ↦ dyadicLegalValue q k source target r kin probe t ω b) =ᵐ[
      twoMarkedCloudLaw q A B α β r] fun ω ↦ blockLegalTilted q source target
        ((r / ((2 ^ k : ℕ) ^ q : ℝ≥0) : ℝ≥0) : ℝ) kin probe t
        (blockLocalCloud q (2 ^ k) b ω.1) (blockLocalCloud q (2 ^ k) b ω.2) := by
    filter_upwards [ae_points_mem_unitCube_twoMarkedCloudLaw q α β r] with ω hω
    rw [dyadicLegalValue, dyadicLegalGraph_eq_rawBlock q k source target ω hω.1 hω.2 b, hcoe]
    exact rawBlockLegalValue_eq_local q (2 ^ k) hq (by positivity) b source target
      r.coe_nonneg kin hhom probe t ω hω.1 hω.2
  exact ⟨hInt.congr hae.symm, (integral_congr_ae hae).trans hmean⟩

/-- The literal dyadic leaf sum has the exact actual legal pressure mean. -/
theorem dyadicLegalValue_sum_integrable_integral (q k : ℕ) (hq : 0 < q)
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
    Integrable (fun ω ↦ ∑ b : Fin q → Fin (2 ^ k),
      dyadicLegalValue q k source target r kin probe t ω b)
      (twoMarkedCloudLaw q A B α β r) ∧
    (∫ ω, ∑ b : Fin q → Fin (2 ^ k), dyadicLegalValue q k source target r kin probe t ω b
      ∂twoMarkedCloudLaw q A B α β r) =
      (((2 ^ k : ℕ) ^ q : ℕ) : ℝ) *
        legalMarkedPressure q source target α β (r / ((2 ^ k : ℕ) ^ q : ℝ≥0)) kin probe t := by
  have hblock (b : Fin q → Fin (2 ^ k)) :=
    dyadicLegalValue_integrable_integral q k hq hs ht r α β hC hG hk hkb hhom hp hpb t b
  refine ⟨integrable_finsetSum _ (fun b _ ↦ (hblock b).1), ?_⟩
  rw [integral_finsetSum _ (fun b _ ↦ (hblock b).1)]
  simp only [fun b ↦ (hblock b).2, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul]

end OTSelector.Reconstruction
