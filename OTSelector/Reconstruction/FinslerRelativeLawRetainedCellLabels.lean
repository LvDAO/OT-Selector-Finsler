import OTSelector.Reconstruction.FinslerRelativeLawActualSeedRecovery
import OTSelector.Reconstruction.FinslerRelativeLawGlobalRetainedCell

/-! Original finite retained cells determine their measurable sample labels.
The true residual flag remains separate from every retained cell. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The unique original retained cell, with none outside their original union. -/
def finiteOriginalCellLabel {C Z : Type*} (cell : C → Set Z) (z : Z) : Option C := by
  classical
  exact if h : ∃ c, z ∈ cell c then some (Classical.choose h) else none

theorem finiteOriginalCellLabel_eq_some_iff
    {C Z : Type*} (cell : C → Set Z) (hdisj : Pairwise (Disjoint on cell)) (z : Z) (c : C) :
    finiteOriginalCellLabel cell z = some c ↔ z ∈ cell c := by
  classical
  unfold finiteOriginalCellLabel
  split_ifs with h
  · have hmem := Classical.choose_spec h
    constructor
    · intro he
      exact Option.some.inj he ▸ hmem
    · intro hz
      have heq : Classical.choose h = c := by
        by_contra hn
        exact disjoint_left.mp (hdisj hn) hmem hz
      exact congrArg some heq
  · simp only [false_iff]
    exact fun hz ↦ h ⟨c, hz⟩

theorem finiteOriginalCellLabel_eq_none_iff
    {C Z : Type*} (cell : C → Set Z) (z : Z) :
    finiteOriginalCellLabel cell z = none ↔ z ∉ ⋃ c, cell c := by
  classical
  unfold finiteOriginalCellLabel
  split_ifs with h <;> simp [h, Set.mem_iUnion]

theorem measurable_finiteOriginalCellLabel
    {C Z : Type*} [Fintype C] [MeasurableSpace Z]
    [MeasurableSpace (Option C)]
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell)) : Measurable (finiteOriginalCellLabel cell) := by
  apply measurable_to_countable'
  intro c
  cases c with
  | none =>
    have heq : (finiteOriginalCellLabel cell) ⁻¹' {none} = (⋃ c, cell c)ᶜ := by
      ext z
      exact finiteOriginalCellLabel_eq_none_iff cell z
    rw [heq]
    exact (MeasurableSet.iUnion hcell).compl
  | some c =>
    have heq : (finiteOriginalCellLabel cell) ⁻¹' {some c} = cell c := by
      ext z
      exact finiteOriginalCellLabel_eq_some_iff cell hdisj z c
    rw [heq]
    exact hcell c

/-- The true residual mark has no retained cell. All other marks read their
original physical label's cell. -/
def originalRetainedCellTag {X Z C T : Type*} [DecidableEq T]
    (a : X → Z) (cell : C → Set Z) (selected : Finset T) (p : X × T) : Option C := by
  classical
  exact if p.2 ∈ selected then none else finiteOriginalCellLabel cell (a p.1)

theorem originalRetainedCellTag_none_iff
    {X Z C T : Type*} [DecidableEq T] (a : X → Z) (cell : C → Set Z)
    (selected : Finset T) (p : X × T)
    (hcover : p.2 ∉ selected → a p.1 ∈ ⋃ c, cell c) :
    originalRetainedCellTag a cell selected p = none ↔ p.2 ∈ selected := by
  classical
  unfold originalRetainedCellTag
  by_cases h : p.2 ∈ selected
  · simp [h]
  · rw [ite_eq_right h, finiteOriginalCellLabel_eq_none_iff]
    exact ⟨fun hn ↦ False.elim (hn (hcover h)), fun ht ↦ False.elim (h ht)⟩

/-- A retained cell tag reads the original physical cell and excludes exactly
 the selected residual types. -/
theorem originalRetainedCellTag_eq_some_iff
    {X Z C T : Type*} [DecidableEq T] (a : X → Z) (cell : C → Set Z)
    (hdisj : Pairwise (Disjoint on cell)) (selected : Finset T) (p : X × T) (c : C) :
    originalRetainedCellTag a cell selected p = some c ↔
      p.2 ∉ selected ∧ a p.1 ∈ cell c := by
  classical
  unfold originalRetainedCellTag
  by_cases h : p.2 ∈ selected
  · simp [h]
  · rw [ite_eq_right h, finiteOriginalCellLabel_eq_some_iff cell hdisj]
    simp only [h, not_false_eq_true, true_and]

/-- Every literal false flag is outside the true-residual type set. -/
theorem not_mem_selectedSubplanTags_of_flag_false
    {T : Type*} [Fintype T] {t : Option (Bool × T)}
    (ht : subplanRetentionFlag t = false) : t ∉ PopulationTypedCostData.selectedSubplanTags (T := T) := by
  classical
  cases t with
  | none => simp [subplanRetentionFlag] at ht
  | some t =>
    rcases t with ⟨flag, t⟩
    cases flag
    · simp [PopulationTypedCostData.selectedSubplanTags]
    · simp [subplanRetentionFlag] at ht

/-- The global original retained population is supported on the actual finite
cell union. This follows from its literal original inverse and conditional
marginal domination, rather than a new retained-support premise. -/
theorem original_global_retained_cell_support
    {X Z C : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableEq Z] [Fintype C]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (lambda : Measure Z) [SFinite lambda]
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (b : Z × ℝ → X) (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (K : C → Kernel Z (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (hmarginals : ∀ᵐ z ∂lambda,
      (finiteCellPairKernel cell hcell K z).map Prod.fst ≤ condDistrib u a μ z ∧
      (finiteCellPairKernel cell hcell K z).map Prod.snd ≤ condDistrib u a ν z) :
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
    ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c ∧ a p.2 ∈ ⋃ c, cell c := by
  classical
  let G := ⋃ c, cell c
  let Kg := finiteCellPairKernel cell hcell K
  have hG : MeasurableSet G := MeasurableSet.iUnion hcell
  have hlatent : ∀ᵐ p ∂lambda ⊗ₘ Kg, p.1 ∈ G := by
    apply Measure.ae_compProd_of_ae_ae (measurable_fst hG)
    exact Filter.Eventually.of_forall fun z ↦ by
      by_cases hz : z ∈ G
      · exact Filter.Eventually.of_forall fun _ ↦ hz
      · rw [show Kg z = 0 from finiteCellPairKernel_eq_zero cell hcell K hz]
        simp
  have hread := original_retained_pair_read_coordinates μ ν lambda a u ha hu b hb
    hμinv hνinv hlabel0 hlabel1 (L := univ) Kg (by simpa using hmarginals) id measurable_id
  simp only [Measure.restrict_univ, Prod.map_id, Measure.map_id, id_eq] at hread
  have hpairs : ∀ᵐ p ∂(lambda ⊗ₘ Kg).map sameLabelPopulationPair,
      p.1.1 ∈ G ∧ p.2.1 ∈ G := by
    apply (ae_map_iff measurable_sameLabelPopulationPair.aemeasurable
      (((measurable_fst.comp measurable_fst) hG).inter
        ((measurable_fst.comp measurable_snd) hG))).mpr
    exact hlatent.mono fun p hp ↦ ⟨hp, hp⟩
  rw [← hread] at hpairs
  exact ae_of_ae_map ((ha.prodMk hu).prodMap (ha.prodMk hu)).aemeasurable hpairs

/-- The actual global original population discharges the finite-cell partition
hypothesis in the full assignment splice on its same residual-marked sample. -/
theorem PopulationTypedCostData.original_global_cell_tags_ae
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableEq Z]
    [Fintype C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (lambda : Measure Z) [SFinite lambda]
    (a : X → Z) (u : X → ℝ) (ha : Measurable a) (hu : Measurable u)
    (b : Z × ℝ → X) (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (K : C → Kernel Z (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (Qglobal : Kernel Z (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell K z + Qglobal z) (condDistrib u a μ z) (condDistrib u a ν z))
    (πWhole ξ : Measure (X × X)) [IsFiniteMeasure πWhole]
    (hπWhole : Vlasov.IsCoupling πWhole μ ν)
    (hsplit : πWhole = (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b)) + ξ)
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData πWhole μ ν T q cost)
    (n : ℕ) :
    let hξ : ξ ≤ πWhole := by rw [hsplit]; exact Measure.le_add_left le_rfl
    let R := D.refineSubplan ξ hξ
    let selected := selectedSubplanTags (T := T)
    ∀ᵐ sample ∂R.markedLaw n,
      (∀ i, originalRetainedCellTag a cell selected (sample.1 i) = none ↔
        (R.sourceSample n i sample).1 ∈ selected) ∧
      (∀ j, originalRetainedCellTag a cell selected (sample.2 j) = none ↔
        (R.targetSample n j sample).1 ∈ selected) := by
  classical
  let hξ : ξ ≤ πWhole := by rw [hsplit]; exact Measure.le_add_left le_rfl
  let R := D.refineSubplan ξ hξ
  let selected := selectedSubplanTags (T := T)
  let G := ⋃ c, cell c
  have hG : MeasurableSet G := MeasurableSet.iUnion hcell
  have hmarginals : ∀ᵐ z ∂lambda,
      (finiteCellPairKernel cell hcell K z).map Prod.fst ≤ condDistrib u a μ z ∧
      (finiteCellPairKernel cell hcell K z).map Prod.snd ≤ condDistrib u a ν z :=
    hwhole.mono fun z hz ↦ clockPair_marginals_le_of_original_split _ _ _ _ hz
  have hsupport := original_global_retained_cell_support μ ν lambda a u ha hu b hb
    hμinv hνinv hlabel0 hlabel1 cell hcell K hmarginals
  let _instξ : IsFiniteMeasure ξ := isFiniteMeasure_of_le πWhole hξ
  have hcancel : πWhole - ξ = (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b)) := by rw [hsplit, Measure.add_sub_cancel]
  have hs : ∀ᵐ x ∂(πWhole - ξ).map Prod.fst, a x ∈ G := by
    apply (ae_map_iff measurable_fst.aemeasurable (ha hG)).mpr
    rw [hcancel]
    exact hsupport.mono fun p hp ↦ hp.1
  have ht : ∀ᵐ y ∂(πWhole - ξ).map Prod.snd, a y ∈ G := by
    apply (ae_map_iff measurable_snd.aemeasurable (ha hG)).mpr
    rw [hcancel]
    exact hsupport.mono fun p hp ↦ hp.2
  have hsFalse : ∀ᵐ p ∂(R.types.sourceMarkedLaw μ).restrict
      {p | subplanRetentionFlag p.2 = false}, a p.1 ∈ G := by
    apply ae_of_ae_map (p := fun x : X ↦ a x ∈ G) measurable_fst.aemeasurable
    rw [(D.refineSubplan_retained_physical_laws ξ hξ).1]
    exact hs
  have htFalse : ∀ᵐ p ∂(R.types.targetMarkedLaw ν).restrict
      {p | subplanRetentionFlag p.2 = false}, a p.1 ∈ G := by
    apply ae_of_ae_map (p := fun x : X ↦ a x ∈ G) measurable_fst.aemeasurable
    rw [(D.refineSubplan_retained_physical_laws ξ hξ).2]
    exact ht
  have hproper := R.types.marked_ae_some_of_sum_eq hπWhole R.sum_eq
  have hsTag : ∀ᵐ p ∂R.types.sourceMarkedLaw μ,
      originalRetainedCellTag a cell selected p = none ↔ p.2 ∈ selected := by
    filter_upwards [hproper.1, ae_imp_of_ae_restrict hsFalse] with p hp hf
    apply originalRetainedCellTag_none_iff
    intro hn
    obtain ⟨⟨flag, t⟩, hmark⟩ := hp
    cases flag
    · exact hf (by rw [hmark]; rfl)
    · exact False.elim (hn (by simp [selected, selectedSubplanTags, hmark]))
  have htTag : ∀ᵐ p ∂R.types.targetMarkedLaw ν,
      originalRetainedCellTag a cell selected p = none ↔ p.2 ∈ selected := by
    filter_upwards [hproper.2, ae_imp_of_ae_restrict htFalse] with p hp hf
    apply originalRetainedCellTag_none_iff
    intro hn
    obtain ⟨⟨flag, t⟩, hmark⟩ := hp
    cases flag
    · exact hf (by rw [hmark]; rfl)
    · exact False.elim (hn (by simp [selected, selectedSubplanTags, hmark]))
  have hsArray : ∀ᵐ x ∂Measure.pi (fun _ : Fin n ↦ R.types.sourceMarkedLaw μ),
      ∀ i, originalRetainedCellTag a cell selected (x i) = none ↔ (x i).2 ∈ selected :=
    ae_all_iff.mpr fun i ↦ (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin n ↦ R.types.sourceMarkedLaw μ) i).ae hsTag
  have htArray : ∀ᵐ y ∂Measure.pi (fun _ : Fin n ↦ R.types.targetMarkedLaw ν),
      ∀ j, originalRetainedCellTag a cell selected (y j) = none ↔ (y j).2 ∈ selected :=
    ae_all_iff.mpr fun j ↦ (Measure.quasiMeasurePreserving_eval
      (fun _ : Fin n ↦ R.types.targetMarkedLaw ν) j).ae htTag
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsArray,
    Measure.quasiMeasurePreserving_snd.ae htArray] with sample hs ht
  exact ⟨hs, ht⟩

end OTSelector.Reconstruction
