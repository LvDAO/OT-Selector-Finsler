import OTSelector.Reconstruction.MarkedStationaryValueLegalSpatialTypesFinite
import OTSelector.Reconstruction.MarkedStationaryValueLegalSpatialTypes
import OTSelector.Finite.BlockLeafAssembly

/-! Actual retained spatial source defects from original optional point types.
Inactive points are omitted before histogram repair; no selected endpoints are
assumed to be iid. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A same-type comparator on the actual active points bounds the true sum of
spatial legal source defects by the original active type discrepancies. -/
theorem active_spatial_source_defect_le_type_discrepancy
    {m n : ℕ} {Cell T : Type*} [Fintype Cell] [DecidableEq Cell]
    [Fintype T] [DecidableEq T]
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → Cell) (t : Fin n → Cell)
    (typeS : Fin m → Option T) (typeT : Fin n → Option T)
    (htype : ∀ i j a, typeS i = some a → typeT j = some a →
      (i, j) ∈ allowed ∧ s i = t j) :
    (∑ a : T, (blockSizeS typeS (some a) : ℝ)) -
        ∑ b : Cell, (PartialMatching.legalMaximumCard
          (PartialMatching.spatialLegalBlock allowed s t b) : ℝ) ≤
      ∑ a : T, |(blockSizeS typeS (some a) : ℝ) - (blockSizeT typeT (some a) : ℝ)| := by
  classical
  let cost : Fin m → Fin n → ℝ := fun _ _ ↦ 0
  let U := Finset.univ.biUnion (fun a : T ↦ blockEdgesAmbient typeS typeT cost (some a))
  have hU : U ⊆ (blockPartialMatching typeS typeT cost).edges := by
    intro e he
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_biUnion.mpr ⟨some a, Finset.mem_univ _, ha⟩
  let σ := (blockPartialMatching typeS typeT cost).subMatching U hU
  have hedge (e : Fin m × Fin n) (he : e ∈ σ.edges) :
      ∃ a : T, typeS e.1 = some a ∧ typeT e.2 = some a := by
    change e ∈ U at he
    obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp he
    exact ⟨a, by simpa only [mem_blockFinset_iff] using
      fst_mem_blockEdgesAmbient typeS typeT cost ha,
      by simpa only [mem_blockFinsetT_iff] using
        snd_mem_blockEdgesAmbient typeS typeT cost ha⟩
  have hcard : σ.card = ∑ a : T, min (blockSizeS typeS (some a))
      (blockSizeT typeT (some a)) := by
    change U.card = _
    rw [Finset.card_biUnion]
    · simp only [card_blockEdgesAmbient]
    · intro a _ b _ hab
      exact blockEdgesAmbient_pairwiseDisjoint typeS typeT cost
        (Finset.mem_univ (some a)) (Finset.mem_univ (some b))
        (fun h ↦ hab (Option.some.inj h))
  have hleg : PartialMatching.IsLegal allowed σ := by
    intro e he
    obtain ⟨a, ha, hb⟩ := hedge e he
    exact (htype e.1 e.2 a ha hb).1
  have hcell : ∀ e ∈ σ.edges, s e.1 = t e.2 := by
    intro e he
    obtain ⟨a, ha, hb⟩ := hedge e he
    exact (htype e.1 e.2 a ha hb).2
  have hR := PartialMatching.card_le_sum_spatial_legal_ranks allowed s t σ hleg hcell
  rw [hcard] at hR
  have hRreal : (∑ a : T, ((min (blockSizeS typeS (some a))
      (blockSizeT typeT (some a)) : ℕ) : ℝ)) ≤
      ∑ b : Cell, (PartialMatching.legalMaximumCard
        (PartialMatching.spatialLegalBlock allowed s t b) : ℝ) := by
    exact_mod_cast hR
  calc
    _ ≤ (∑ a : T, (blockSizeS typeS (some a) : ℝ)) -
        ∑ a : T, ((min (blockSizeS typeS (some a)) (blockSizeT typeT (some a)) : ℕ) : ℝ) :=
      sub_le_sub_left hRreal _
    _ = ∑ a : T, ((blockSizeS typeS (some a) : ℝ) -
        ((min (blockSizeS typeS (some a)) (blockSizeT typeT (some a)) : ℕ) : ℝ)) :=
      by rw [Finset.sum_sub_distrib]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a _
      by_cases h : blockSizeS typeS (some a) ≤ blockSizeT typeT (some a)
      · rw [min_eq_left h, sub_self]
        exact abs_nonneg _
      · rw [min_eq_right (le_of_not_ge h)]
        exact le_abs_self _

/-- Original edge and cell events determine every spatial child graph
measurably. The same statement supports both its actual rank and signed value. -/
theorem measurableSet_active_spatial_graph_eq
    {Ω Cell : Type*} [MeasurableSpace Ω] [MeasurableSpace Cell]
    [Fintype Cell] [DecidableEq Cell] [MeasurableSingletonClass Cell] {m n : ℕ}
    (allowed : Ω → Finset (Fin m × Fin n))
    (ha : ∀ e, MeasurableSet {ω | e ∈ allowed ω})
    (s : Ω → Fin m → Cell) (t : Ω → Fin n → Cell)
    (hs : ∀ i, Measurable (fun ω ↦ s ω i)) (ht : ∀ j, Measurable (fun ω ↦ t ω j))
    (b : Cell) (edges : Finset (Fin m × Fin n)) :
    MeasurableSet {ω | PartialMatching.spatialLegalBlock (allowed ω) (s ω) (t ω) b = edges} := by
  apply measurableSet_graph_eq_of_mem
  intro e
  have hS := measurableSet_eq_fun (hs e.1) measurable_const (g := fun _ ↦ b)
  have hT := measurableSet_eq_fun (ht e.2) measurable_const (g := fun _ ↦ b)
  simpa only [PartialMatching.spatialLegalBlock, Finset.mem_filter, Set.ofPred_and] using
    (ha e).inter (hS.inter hT)

/-- Original measurable edge and cell events make the actual legal spatial
rank measurable. No point-cloud replacement is involved. -/
theorem measurable_active_spatial_legal_rank
    {Ω Cell : Type*} [MeasurableSpace Ω] [MeasurableSpace Cell]
    [Fintype Cell] [DecidableEq Cell] [MeasurableSingletonClass Cell] {m n : ℕ}
    (allowed : Ω → Finset (Fin m × Fin n))
    (ha : ∀ e, MeasurableSet {ω | e ∈ allowed ω})
    (s : Ω → Fin m → Cell) (t : Ω → Fin n → Cell)
    (hs : ∀ i, Measurable (fun ω ↦ s ω i)) (ht : ∀ j, Measurable (fun ω ↦ t ω j))
    (b : Cell) : Measurable (fun ω ↦ (PartialMatching.legalMaximumCard
      (PartialMatching.spatialLegalBlock (allowed ω) (s ω) (t ω) b) : ℝ)) :=
  measurable_legalMaximumCard_cast _
    (measurableSet_active_spatial_graph_eq allowed ha s t hs ht b)

/-- The literal active spatial source deficiency on the original iid samples
has its original binomial square-root estimate, including arbitrary nonuniform
spatial shapes and zero-mass types. -/
theorem integral_active_spatial_source_defect_le_of_iid_types
    {Ω X Y Cell T : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Cell] [Fintype Cell] [DecidableEq Cell] [MeasurableSingletonClass Cell]
    [Fintype T] [DecidableEq T] [MeasurableSpace (Option T)]
    [MeasurableSingletonClass (Option T)]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {N : ℕ} (xs : Fin N → Ω → X) (ys : Fin N → Ω → Y)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = ν)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω j ↦ ys j ω) P)
    (tagA : X → Option T) (tagB : Y → Option T)
    (hA : Measurable tagA) (hB : Measurable tagB)
    (hmass : ∀ a : T, μ.real (tagA ⁻¹' {some a}) = ν.real (tagB ⁻¹' {some a}))
    {p : ℝ} (hp : ∑ a : T, μ.real (tagA ⁻¹' {some a}) = p)
    (allowed : Ω → Finset (Fin N × Fin N))
    (ha : ∀ e, MeasurableSet {ω | e ∈ allowed ω})
    (s t : Ω → Fin N → Cell)
    (hs : ∀ i, Measurable (fun ω ↦ s ω i)) (ht : ∀ j, Measurable (fun ω ↦ t ω j))
    (hlegal : ∀ᵐ ω ∂P, ∀ i j a, tagA (xs i ω) = some a → tagB (ys j ω) = some a →
      (i, j) ∈ allowed ω ∧ s ω i = t ω j) :
    let defect := fun ω ↦ (∑ a : T, (blockSizeS (fun i ↦ tagA (xs i ω)) (some a) : ℝ)) -
      ∑ b : Cell, (PartialMatching.legalMaximumCard
        (PartialMatching.spatialLegalBlock (allowed ω) (s ω) (t ω) b) : ℝ)
    Integrable defect P ∧ (∫ ω, defect ω ∂P) ≤
      Real.sqrt (2 * (N : ℝ) * Fintype.card T * p) := by
  classical
  dsimp only
  have hmA (a : T) : MeasurableSet (tagA ⁻¹' {some a}) := (measurableSet_singleton _).preimage hA
  have hmB (a : T) : MeasurableSet (tagB ⁻¹' {some a}) := (measurableSet_singleton _).preimage hB
  have hcountS (a : T) (ω : Ω) :
      (blockSizeS (fun i ↦ tagA (xs i ω)) (some a) : ℝ) =
        iidTypeCount xs (tagA ⁻¹' {some a}) ω :=
    cast_blockSize_eq_iidTypeCount xs tagA ω (some a)
  have hcountT (a : T) (ω : Ω) :
      (blockSizeT (fun j ↦ tagB (ys j ω)) (some a) : ℝ) =
        iidTypeCount ys (tagB ⁻¹' {some a}) ω :=
    cast_blockSize_eq_iidTypeCount ys tagB ω (some a)
  have hcountI (a : T) : Integrable (fun ω ↦
      (blockSizeS (fun i ↦ tagA (xs i ω)) (some a) : ℝ)) P := by
    have h := (iidTypeCount_moments P μ xs hx hxi hxl (hmA a)).1.integrable (by norm_num)
    simpa only [hcountS] using h
  have hrankI (b : Cell) : Integrable (fun ω ↦ (PartialMatching.legalMaximumCard
      (PartialMatching.spatialLegalBlock (allowed ω) (s ω) (t ω) b) : ℝ)) P := by
    apply Integrable.of_bound (measurable_active_spatial_legal_rank allowed ha s t hs ht b).aestronglyMeasurable N
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    exact Nat.cast_le.mpr ((PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _))
  have hdefI : Integrable (fun ω ↦
      (∑ a : T, (blockSizeS (fun i ↦ tagA (xs i ω)) (some a) : ℝ)) -
        ∑ b : Cell, (PartialMatching.legalMaximumCard
          (PartialMatching.spatialLegalBlock (allowed ω) (s ω) (t ω) b) : ℝ)) P :=
    (integrable_finsetSum (Finset.univ : Finset T) (fun a _ ↦ hcountI a)).sub
      (integrable_finsetSum (Finset.univ : Finset Cell) (fun b _ ↦ hrankI b))
  obtain ⟨hdI, hd⟩ := iidTypeCount_total_difference_bound P μ ν xs ys hx hy hxi hyi
    hxl hyl hxy (fun a ↦ tagA ⁻¹' {some a}) (fun a ↦ tagB ⁻¹' {some a}) hmA hmB hmass hp
  refine ⟨hdefI, (integral_mono_ae hdefI hdI ?_).trans hd⟩
  filter_upwards [hlegal] with ω hω
  have h := active_spatial_source_defect_le_type_discrepancy (allowed ω) (s ω) (t ω)
    (fun i ↦ tagA (xs i ω)) (fun j ↦ tagB (ys j ω)) hω
  simpa only [hcountS, hcountT] using h

end OTSelector.Reconstruction
