import OTSelector.Reconstruction.OriginalLegalWeightedWindowCoreRecovery
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryReserveWindowCoupling
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryReserveCore

/-!
# Original reserve labels survive the actual finite-window joining

The whole original retained scene and an independent whole original reserve
scene remain separate coordinates while their superposed input is coupled to
the literal original Poisson arrays. Actual reserve atoms are then identified
in those unchanged finite indices; no selected leftover is assigned an iid law.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

variable {q : ℕ} {α β : Measure ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
local instance reserveCompletionColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
local instance reserveCompletionPlanPolish :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) :=
  LocalFiniteMeasure.instPolishSpace
local instance reserveCompletionInputPolish :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) :=
  LocalFiniteMeasure.instPolishSpace

/-- Superpose the actual independently dilated original inputs while retaining
the SAME first original plan and both original scene coordinates separately. -/
def legalOriginalDilatedReserveScene (q : ℕ) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (p : LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) :
    LegalMarkedOptimalInputScene q :=
  legalMarkedReserveInputScene q
    (legalMarkedInputSceneDilation q c hc p.1, legalMarkedInputSceneDilation q d hd p.2)

theorem measurable_legalOriginalDilatedReserveScene
    (q : ℕ) (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    Measurable (legalOriginalDilatedReserveScene q c d hc hd) :=
  (measurable_legalMarkedReserveInputScene q).comp
    ((continuous_legalMarkedInputSceneDilation q c hc).measurable.prodMap
      (continuous_legalMarkedInputSceneDilation q d hd).measurable)

/-- The true independent original product maps to the existing actual
superposed input law, with no new independence assertion about selected atoms. -/
theorem map_original_pair_eq_dilatedReserveLaw
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    ((M.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (N.law : Measure (LegalMarkedOptimalInputScene q))).map
        (legalOriginalDilatedReserveScene q c d hc hd) =
      (legalMarkedReserveInputLaw q (legalMarkedInputDilationLaw q c hc M.law)
        (legalMarkedInputDilationLaw q d hd N.law) :
          Measure (LegalMarkedOptimalInputScene q)) := by
  change _ = (((M.law : Measure (LegalMarkedOptimalInputScene q)).map
      (legalMarkedInputSceneDilation q c hc)).prod
    ((N.law : Measure (LegalMarkedOptimalInputScene q)).map
      (legalMarkedInputSceneDilation q d hd))).map (legalMarkedReserveInputScene q)
  rw [Measure.map_prod_map _ _
    (continuous_legalMarkedInputSceneDilation q c hc).measurable
    (continuous_legalMarkedInputSceneDilation q d hd).measurable,
    Measure.map_map (measurable_legalMarkedReserveInputScene q)
      ((continuous_legalMarkedInputSceneDilation q c hc).measurable.prodMap
        (continuous_legalMarkedInputSceneDilation q d hd).measurable)]
  rfl

/-- A literal original Poisson finite-window joining preserves BOTH original
independent scene coordinates, including their reserve origin labels. The
first marginal is exactly M.law × N.law, before physical dilation. -/
theorem exists_original_labelled_reserve_windowCoupling
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hunit : |(c ^ q)⁻¹| + |(d ^ q)⁻¹| = 1)
    {U : Set (LegalColoredInputPoint q)} (hU : IsCompact U) :
    ∃ S > 0, ∃ J : ProbabilityMeasure
        ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))),
      (J : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
          Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
            (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (J : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
          Prod.snd = legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β ∧
      ∀ᵐ p ∂(J : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
        legalInputRestrictionLocal U (legalOriginalDilatedReserveScene q c d hc hd p.1).2 =
          legalInputRestrictionLocal U (legalInputTwoBlockLocal q p.2) := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← M.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  let : IsProbabilityMeasure β := by
    rw [← M.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  have : StandardBorelSpace (MarkedCloudSpace q ℝ) := by infer_instance
  have : Nonempty (LegalMarkedOptimalInputScene q) :=
    nonempty_of_isProbabilityMeasure (M.law : Measure (LegalMarkedOptimalInputScene q))
  obtain ⟨S, hS, hlaw⟩ :=
    map_originalDilatedReserve_inputRestrictionLocal_eq_originalPoisson M N c d hc hd hunit hU
  let P := (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
    (N.law : Measure (LegalMarkedOptimalInputScene q))
  let Q := legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β
  have hvol : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) q)).ne'
  let : IsProbabilityMeasure Q := isProbabilityMeasure_legalInputPoissonWindowLaw q hS.le
    measurableSet_Icc (Subset.refl _) hvol α β
  let f : (LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) →
      LocalFiniteMeasure (LegalColoredInputPoint q) :=
    fun p ↦ legalInputRestrictionLocal U (legalOriginalDilatedReserveScene q c d hc hd p).2
  let z : (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) →
      LocalFiniteMeasure (LegalColoredInputPoint q) :=
    fun b ↦ legalInputRestrictionLocal U (legalInputTwoBlockLocal q b)
  have hf : Measurable f := (measurable_legalInputRestrictionLocal hU.measurableSet).comp
    (measurable_snd.comp (measurable_legalOriginalDilatedReserveScene q c d hc hd))
  have hz : Measurable z := (measurable_legalInputRestrictionLocal hU.measurableSet).comp
    (measurable_legalInputTwoBlockLocal q)
  have heq : P.map f = Q.map z := by
    have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
        legalInputRestrictionLocal U s.2) :=
      (measurable_legalInputRestrictionLocal hU.measurableSet).comp measurable_snd
    rw [show f = (fun s : LegalMarkedOptimalInputScene q ↦
      legalInputRestrictionLocal U s.2) ∘ legalOriginalDilatedReserveScene q c d hc hd from rfl,
      ← Measure.map_map hm (measurable_legalOriginalDilatedReserveScene q c d hc hd),
      map_original_pair_eq_dilatedReserveLaw M N c d hc hd]
    exact hlaw
  let L := 4 * (S + 1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hmargin : S + 1 < L / 2 := by dsimp [L]; linarith
  have hroot : (0 : Fin q → ℝ) ∈ haarRootCube (Fin q) (L / 2 - S - 1) := by
    constructor <;> intro i <;> dsimp <;> linarith
  let Q₀ := twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))
  let φ : TwoMarkedCloudSpace q ℝ ℝ →
      BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q) :=
    fun ω ↦ legalInputRootWindows q (Real.toNNReal L) (haarRootCube (Fin q) S) (0, ω)
  have hφ : Measurable φ :=
    (measurable_legalInputRootWindows q (Real.toNNReal L) measurableSet_Icc).comp
      measurable_prodMk_left
  have hφlaw : Q₀.map φ = Q :=
    map_legalInputRootWindows_eq_of_inner_root q hS.le hmargin measurableSet_Icc
      (Subset.refl _) hvol α β hroot
  have hraw : P.map f = Q₀.map (z ∘ φ) := by
    rw [← Measure.map_map hz hφ, hφlaw]
    exact heq
  obtain ⟨J₀, hl, hr, he⟩ := exists_joint_original_input_readout P Q₀ f (z ∘ φ) hf
    (hz.comp hφ) hraw
  let J : ProbabilityMeasure
      ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))) :=
    J₀.map (measurable_id.prodMap hφ).aemeasurable
  refine ⟨S, hS, J, ?_, ?_, ?_⟩
  · change ((J₀ : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
      TwoMarkedCloudSpace q ℝ ℝ)).map (Prod.map id φ)).map Prod.fst = _
    rw [Measure.map_map measurable_fst (measurable_id.prodMap hφ)]
    exact hl
  · change ((J₀ : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
      TwoMarkedCloudSpace q ℝ ℝ)).map (Prod.map id φ)).map Prod.snd = _
    rw [Measure.map_map measurable_snd (measurable_id.prodMap hφ)]
    rw [show Prod.snd ∘ Prod.map id φ = φ ∘ Prod.snd from rfl,
      ← Measure.map_map hφ measurable_snd, hr, hφlaw]
  · have hout : ∀ᵐ p ∂(J : Measure
        ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
        f p.1 = z p.2 :=
      (ae_map_iff (μ := (J₀ : Measure
        ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          TwoMarkedCloudSpace q ℝ ℝ)))
        (measurable_id.prodMap hφ).aemeasurable
        (measurableSet_eq_fun (hf.comp measurable_fst) (hz.comp measurable_snd))).mpr he
    simpa only [f, z] using hout

section FiniteAtoms
variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The actual reserve occupies precisely these unchanged full-array indices. -/
def originalReserveAtomIndices {m : ℕ} (ν : Measure X) (source : Fin m → X) :
    Finset (Fin m) := Finset.univ.filter fun i ↦ ν {source i} = 1

/-- A dominated unit-atom reserve is exactly the corresponding subarray of the
original finite input; the construction never resamples or reorders its points. -/
theorem measure_eq_sum_originalReserveAtomIndices {m : ℕ}
    (ν : Measure X) (source : Fin m → X) (hs : Injective source)
    (hdom : ν ≤ ∑ i, Measure.dirac (source i))
    (hunit : ∀ i, ν {source i} = 0 ∨ ν {source i} = 1) :
    ν = ∑ i ∈ originalReserveAtomIndices ν source, Measure.dirac (source i) := by
  let E := Finset.univ.image source
  have hnull : (∑ i, Measure.dirac (source i)) (E : Set X)ᶜ = 0 := by
    rw [Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Measure.dirac_apply' _ (Finset.measurableSet _).compl]
    exact indicator_of_notMem (by simp [E]) _
  have hAE : ∀ᵐ x ∂ν, x ∈ E := ae_iff.mpr
    (le_antisymm ((hdom _).trans_eq hnull) bot_le)
  calc
    ν = ∑ x ∈ E, ν {x} • Measure.dirac x := Measure.ae_mem_finset_iff.mp hAE
    _ = _ := by
      change (∑ x ∈ Finset.univ.image source, ν {x} • Measure.dirac x) = _
      rw [Finset.sum_image (fun _ _ _ _ h ↦ hs h), originalReserveAtomIndices,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      rcases hunit i with hzero | hone
      · simp only [hzero, zero_smul, zero_ne_one, ite_false]
      · simp only [hone, one_smul, ite_true]

/-- Enumerate the actual reserve indices in their unchanged original order. -/
def originalReserveAtomEmbedding {m : ℕ} (ν : Measure X) (source : Fin m → X) :
    Fin (originalReserveAtomIndices ν source).card ↪ Fin m where
  toFun i := ((originalReserveAtomIndices ν source).orderIsoOfFin rfl i).1
  inj' := by
    intro i j hij
    exact ((originalReserveAtomIndices ν source).orderIsoOfFin rfl).injective (Subtype.ext hij)

/-- The actual reserve observations are literal original array points. -/
def originalReserveAtomArray {m : ℕ} (ν : Measure X) (source : Fin m → X) : BlockData X :=
  ⟨(originalReserveAtomIndices ν source).card, fun i ↦ source (originalReserveAtomEmbedding ν source i)⟩

omit [MeasurableSingletonClass X] in
theorem originalReserveAtomEmbedding_image {m : ℕ} (ν : Measure X) (source : Fin m → X) :
    Finset.univ.image (originalReserveAtomEmbedding ν source) = originalReserveAtomIndices ν source := by
  ext i
  constructor
  · rintro hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact ((originalReserveAtomIndices ν source).orderIsoOfFin rfl j).2
  · intro hi
    refine Finset.mem_image.mpr ⟨((originalReserveAtomIndices ν source).orderIsoOfFin rfl).symm
      ⟨i, hi⟩, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val
      (((originalReserveAtomIndices ν source).orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)

/-- The reserve array contains exactly the true reserve measure, including
its complete physical points and both original coordinates. -/
theorem originalReserveAtomArray_measure_eq {m : ℕ}
    (ν : Measure X) (source : Fin m → X) (hs : Injective source)
    (hdom : ν ≤ ∑ i, Measure.dirac (source i))
    (hunit : ∀ i, ν {source i} = 0 ∨ ν {source i} = 1) :
    legalInputBlockMeasure (originalReserveAtomArray ν source) = ν := by
  calc
    legalInputBlockMeasure (originalReserveAtomArray ν source) =
        ∑ i ∈ originalReserveAtomIndices ν source, Measure.dirac (source i) := by
      change (∑ j : Fin (originalReserveAtomIndices ν source).card,
        Measure.dirac (source (((originalReserveAtomIndices ν source).orderIsoOfFin rfl j).1))) = _
      exact (((originalReserveAtomIndices ν source).orderIsoOfFin rfl).toEquiv.sum_comp
        (fun i ↦ Measure.dirac (source i.1))).trans
          (Finset.sum_coe_sort _ (fun i ↦ Measure.dirac (source i)))
    _ = ν := (measure_eq_sum_originalReserveAtomIndices ν source hs hdom hunit).symm

/-- Actual reserve atoms cannot have been consumed by a core whose endpoint
measure is dominated by the original retained-input part of the SAME full array. -/
theorem originalReserveAtomIndices_disjoint_used
    {m : ℕ} {I : Type*} [DecidableEq I]
    (E : Finset I) (row : I → Fin m) (source : Fin m → X) (hs : Injective source)
    (μ ν : Measure X) (htotal : μ + ν = ∑ i, Measure.dirac (source i))
    (hcore : (∑ e ∈ E, Measure.dirac (source (row e))) ≤ μ) :
    Disjoint (E.image row) (originalReserveAtomIndices ν source) := by
  apply Finset.disjoint_left.mpr
  intro i hi hr
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
  have hres : ν {source (row e)} = 1 := (Finset.mem_filter.mp hr).2
  have hfull : μ {source (row e)} + ν {source (row e)} = 1 := by
    rw [← Measure.add_apply, htotal]
    simp [Measure.finsetSum_apply, Measure.dirac_apply', Pi.single_apply, hs.eq_iff]
  have hzero : μ {source (row e)} = 0 :=
    (ENNReal.add_left_inj (a := (1 : ℝ≥0∞)) (by simp)).mp (by simpa only [hres, zero_add] using hfull)
  have hdir : Measure.dirac (source (row e)) ≤ μ :=
    (Finset.single_le_sum (fun _ _ ↦ Measure.zero_le _) he).trans hcore
  have h := hdir {source (row e)}
  simp [hzero] at h

end FiniteAtoms

/-- A true simple original colored input retains only zero or unit atoms
under a literal physical-window and unchanged-color readout. -/
theorem IsLegalSimpleCountingMeasure.color_window_singleton_zero_or_one
    {μ : LocalFiniteMeasure (LegalColoredInputPoint q)}
    (hs : IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q) μ)
    {U : Set (LegalMarkedPhysicalPoint q)} (_hU : MeasurableSet U) (c : Fin 2)
    (x : LegalMarkedPhysicalPoint q) :
    ((legalInputColorMeasure q μ c).restrict U) {x} = 0 ∨
      ((legalInputColorMeasure q μ c).restrict U) {x} = 1 := by
  by_cases hx : x ∈ U
  · rw [Measure.restrict_apply (measurableSet_singleton x), singleton_inter_of_mem hx,
      legalInputColorMeasure_singleton]
    obtain ⟨config, rfl, hunit⟩ := hs
    change LocalConfiguration.countingMeasure config {(x, c)} = 0 ∨
      LocalConfiguration.countingMeasure config {(x, c)} = 1
    rw [LocalConfiguration.countingMeasure_singleton]
    have h := hunit (x, c)
    have ho : LocalConfiguration.multiplicity config (x, c) = 0 ∨
        LocalConfiguration.multiplicity config (x, c) = 1 := by omega
    rcases ho with hz | ho
    · exact Or.inl (by simp [hz])
    · exact Or.inr (by simp [ho])
  · left
    rw [Measure.restrict_apply (measurableSet_singleton x), singleton_inter_of_notMem hx,
      measure_empty]

/-- The original superposed window readout decomposes the SAME original
finite arrays into the retained-origin input and genuine reserve-origin input. -/
theorem original_labelled_reserve_window_color_decomposition
    (s r : LegalMarkedOptimalInputScene q)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : MeasurableSet U)
    (hread : legalInputRestrictionLocal (U ×ˢ univ) (legalMarkedReserveInputScene q (s, r)).2 =
      legalInputRestrictionLocal (U ×ˢ univ) (legalInputTwoBlockLocal q b)) :
    (legalInputColorMeasure q s.2 0).restrict U +
        (legalInputColorMeasure q r.2 0).restrict U =
      legalInputBlockMeasure (legalOriginalBlockRestriction U b.1) ∧
    (legalInputColorMeasure q s.2 1).restrict U +
        (legalInputColorMeasure q r.2 1).restrict U =
      legalInputBlockMeasure (legalOriginalBlockRestriction U b.2) := by
  have hs := congrArg (fun ν ↦ legalInputColorMeasure q ν 0) hread
  have ht := congrArg (fun ν ↦ legalInputColorMeasure q ν 1) hread
  rw [legalInputColorMeasure_restrict_prod q _ 0 hU,
    legalInputColorMeasure_restrict_prod q _ 0 hU,
    legalInputColorMeasure_twoBlock_source] at hs
  rw [legalInputColorMeasure_restrict_prod q _ 1 hU,
    legalInputColorMeasure_restrict_prod q _ 1 hU,
    legalInputColorMeasure_twoBlock_target] at ht
  change (legalInputColorMeasure q (legalLocalFiniteMeasureSum (s.2, r.2)) 0).restrict U = _ at hs
  change (legalInputColorMeasure q (legalLocalFiniteMeasureSum (s.2, r.2)) 1).restrict U = _ at ht
  rw [legalInputColorMeasure_localFiniteMeasureSum, Measure.restrict_add] at hs ht
  rw [legalInputBlockMeasure_legalOriginalBlockRestriction b.1 hU,
    legalInputBlockMeasure_legalOriginalBlockRestriction b.2 hU]
  exact ⟨hs, ht⟩

/-- The actual finite reserve-capacity payload keeps one original core, its
unchanged complete-array indices, and both literal unused reserve subarrays. -/
def IsOriginalReserveWindowCore (q : ℕ) (U : Set (LegalMarkedPhysicalPoint q))
    (cost : LegalMarkedPhysicalEdge q → ℝ) (s r : LegalMarkedOptimalInputScene q)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) : Prop :=
    let source := legalOriginalBlockRestriction U b.1
    let target := legalOriginalBlockRestriction U b.2
    let νs := (legalInputColorMeasure q r.2 0).restrict U
    let νt := (legalInputColorMeasure q r.2 1).restrict U
    ∃ σ : OTSelector.PartialMatching source.1 target.1,
      PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ (source.2 i).2)
        (fun j ↦ (target.2 j).2)) σ ∧
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict (U ×ˢ U) =
        ∑ e ∈ σ.edges, Measure.dirac (source.2 e.1, target.2 e.2) ∧
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ U) = (σ.card : ℝ≥0∞) ∧
      Integrable cost ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict (U ×ˢ U)) ∧
      (∫ e in U ×ˢ U, cost e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))) =
        σ.cost (fun i j ↦ cost (source.2 i, target.2 j)) ∧
      legalInputBlockMeasure (originalReserveAtomArray νs source.2) = νs ∧
      legalInputBlockMeasure (originalReserveAtomArray νt target.2) = νt ∧
      Finset.univ.image (originalReserveAtomEmbedding νs source.2) ⊆ σ.freeRows ∧
      Finset.univ.image (originalReserveAtomEmbedding νt target.2) ⊆ σ.freeCols ∧
      ((σ.freeRows \ Finset.univ.image (originalReserveAtomEmbedding νs source.2)).card : ℝ) +
        ((Finset.univ.image (originalReserveAtomEmbedding νt target.2) \ σ.freeCols).card : ℝ) =
          ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ Uᶜ)).toReal

/-- A retained original integer core is extracted in the COMPLETE same-input
array, and every true reserve-origin index remains unused on BOTH sides. -/
theorem exists_original_windowCore_with_unused_reserve
    (s r : LegalMarkedOptimalInputScene q) (hs : IsFullOriginalInputMatching q s)
    (hr : IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q) r.2)
    (hf : ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2)
    (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    (hb : Injective b.1.2 ∧ Injective b.2.2)
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : MeasurableSet U)
    (hread : legalInputRestrictionLocal (U ×ˢ univ) (legalMarkedReserveInputScene q (s, r)).2 =
      legalInputRestrictionLocal (U ×ˢ univ) (legalInputTwoBlockLocal q b))
    (cost : LegalMarkedPhysicalEdge q → ℝ) :
    IsOriginalReserveWindowCore q U cost s r b := by
  dsimp only [IsOriginalReserveWindowCore]
  let source := legalOriginalBlockRestriction U b.1
  let target := legalOriginalBlockRestriction U b.2
  let μs := (legalInputColorMeasure q s.2 0).restrict U
  let μt := (legalInputColorMeasure q s.2 1).restrict U
  let νs := (legalInputColorMeasure q r.2 0).restrict U
  let νt := (legalInputColorMeasure q r.2 1).restrict U
  have htotal := original_labelled_reserve_window_color_decomposition s r b hU hread
  have hS : μs + νs = ∑ i : Fin source.1, Measure.dirac (source.2 i) := htotal.1
  have hT : μt + νt = ∑ j : Fin target.1, Measure.dirac (target.2 j) := htotal.2
  let core := legalInputRestrictionLocal (U ×ˢ U) s.1.1
  have hc : IsLegalCountingMeasure (0 : LegalMarkedPhysicalEdge q) core :=
    isLegalCountingMeasure_restrict _ s.1.1 ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1 _
  have hsrc : (core : Measure (LegalMarkedPhysicalEdge q)).fst ≤ μs := by
    change ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict (U ×ˢ U)).fst ≤
      (legalInputColorMeasure q s.2 0).restrict U
    rw [← hs.source_marginal]
    exact fst_restrict_prod_le_input_window (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) hU U
  have htgt : (core : Measure (LegalMarkedPhysicalEdge q)).snd ≤ μt := by
    change ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict (U ×ˢ U)).snd ≤
      (legalInputColorMeasure q s.2 1).restrict U
    rw [← hs.target_marginal]
    exact snd_restrict_prod_le_input_window (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) U hU
  have hsrcFull : (core : Measure (LegalMarkedPhysicalEdge q)).fst ≤
      ∑ i : Fin source.1, Measure.dirac (source.2 i) := by
    rw [← hS]
    exact hsrc.trans (Measure.le_add_right le_rfl)
  have htgtFull : (core : Measure (LegalMarkedPhysicalEdge q)).snd ≤
      ∑ j : Fin target.1, Measure.dirac (target.2 j) := by
    rw [← hT]
    exact htgt.trans (Measure.le_add_right le_rfl)
  have ha : ∀ᵐ e ∂(core : Measure (LegalMarkedPhysicalEdge q)), e.1.2 < e.2.2 := by
    apply ae_restrict_of_ae
    filter_upwards [Measure.support_mem_ae (μ := (s.1.1 : Measure (LegalMarkedPhysicalEdge q)))] with e he
    exact hf e he
  have hiS := legalOriginalBlockRestriction_injective U b.1 hb.1
  have hiT := legalOriginalBlockRestriction_injective U b.2 hb.2
  obtain ⟨σ, hσ, hmeasure, hmass, hcost, hvalue⟩ :=
    exists_originalIndex_legal_partialMatching_cost_of_integer_plan
      (0 : LegalMarkedPhysicalEdge q) core hc source.2 target.2 hiS hiT hsrcFull htgtFull
      (fun x y : LegalMarkedPhysicalPoint q ↦ x.2 < y.2) ha cost
  have hνs : νs ≤ ∑ i : Fin source.1, Measure.dirac (source.2 i) := by
    rw [← hS]
    exact Measure.le_add_left le_rfl
  have hνt : νt ≤ ∑ j : Fin target.1, Measure.dirac (target.2 j) := by
    rw [← hT]
    exact Measure.le_add_left le_rfl
  have hunitS (i : Fin source.1) : νs {source.2 i} = 0 ∨ νs {source.2 i} = 1 :=
    hr.color_window_singleton_zero_or_one hU 0 _
  have hunitT (j : Fin target.1) : νt {target.2 j} = 0 ∨ νt {target.2 j} = 1 :=
    hr.color_window_singleton_zero_or_one hU 1 _
  have hrows : Disjoint σ.rows (originalReserveAtomIndices νs source.2) := by
    apply originalReserveAtomIndices_disjoint_used σ.edges Prod.fst source.2 hiS μs νs hS
    rw [hmeasure] at hsrc
    simpa only [Measure.fst, Measure.map_finset_sum measurable_fst.aemeasurable,
      Measure.map_dirac] using hsrc
  have hcols : Disjoint σ.cols (originalReserveAtomIndices νt target.2) := by
    apply originalReserveAtomIndices_disjoint_used σ.edges Prod.snd target.2 hiT μt νt hT
    rw [hmeasure] at htgt
    simpa only [Measure.snd, Measure.map_finset_sum measurable_snd.aemeasurable,
      Measure.map_dirac] using htgt
  have hmass' : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ U) = (σ.card : ℝ≥0∞) := by
    simpa only [core, legalInputRestrictionLocal, Measure.restrict_apply_univ] using hmass
  have hFreeS : Finset.univ.image (originalReserveAtomEmbedding νs source.2) ⊆ σ.freeRows := by
    rw [originalReserveAtomEmbedding_image]
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hu ↦ Finset.disjoint_left.mp hrows hu hi⟩
  have hFreeT : Finset.univ.image (originalReserveAtomEmbedding νt target.2) ⊆ σ.freeCols := by
    rw [originalReserveAtomEmbedding_image]
    intro j hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hu ↦ Finset.disjoint_left.mp hcols hu hj⟩
  refine ⟨σ, hσ, hmeasure, hmass', hcost, hvalue,
    originalReserveAtomArray_measure_eq νs source.2 hiS hνs hunitS,
    originalReserveAtomArray_measure_eq νt target.2 hiT hνt hunitT, hFreeS, hFreeT, ?_⟩
  have hresmass : νs univ = ((originalReserveAtomIndices νs source.2).card : ℝ≥0∞) := by
    have he := congrArg (fun μ : Measure (LegalMarkedPhysicalPoint q) ↦ μ univ)
      (measure_eq_sum_originalReserveAtomIndices νs source.2 hiS hνs hunitS)
    simpa only [Measure.finsetSum_apply, Measure.dirac_apply_of_mem, mem_univ,
      Finset.sum_const, nsmul_eq_mul, mul_one] using he
  have htotmass : μs univ + νs univ = (source.1 : ℝ≥0∞) := by
    have he := congrArg (fun μ : Measure (LegalMarkedPhysicalPoint q) ↦ μ univ) hS
    simpa only [Measure.add_apply, Measure.finsetSum_apply, Measure.dirac_apply_of_mem,
      mem_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using he
  have hsplit : μs univ = (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ U) +
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ Uᶜ) := by
    change (legalInputColorMeasure q s.2 0).restrict U univ = _
    rw [Measure.restrict_apply_univ, ← hs.source_marginal, Measure.fst,
      Measure.map_apply measurable_fst hU]
    have heq : Prod.fst ⁻¹' U = (U ×ˢ U) ∪ (U ×ˢ Uᶜ) := by
      ext e
      simp only [mem_preimage, mem_union, mem_prod, mem_compl_iff]
      tauto
    rw [heq]
    exact measure_union (by
      apply disjoint_left.mpr
      intro e he he'
      exact he'.2 he.2) (hU.prod hU.compl)
  have hsum : (source.1 : ℝ≥0∞) = (σ.card : ℝ≥0∞) +
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ Uᶜ) +
        ((originalReserveAtomIndices νs source.2).card : ℝ≥0∞) := by
    rw [← htotmass, hsplit, hmass', hresmass]
  have hfinite : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (U ×ˢ Uᶜ) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENNReal.natCast_ne_top source.1)
    rw [hsum]
    exact (le_add_left le_rfl).trans (le_add_right le_rfl)
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_natCast, ENNReal.toReal_add
    (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, hfinite⟩) (ENNReal.natCast_ne_top _),
    ENNReal.toReal_add (ENNReal.natCast_ne_top _) hfinite, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast] at hreal
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hFreeT, Finset.card_empty, Nat.cast_zero,
    add_zero, Finset.card_sdiff_of_subset hFreeS,
    Nat.cast_sub (Finset.card_le_card hFreeS), σ.card_freeRows,
    Nat.cast_sub (σ.card_le.trans (min_le_left _ _)), originalReserveAtomEmbedding_image]
  linarith

/-- For a core that has not consumed genuine reserve indices, the actual
adaptive-removal budget contains only non-reserve unmatched original rows. -/
theorem PartialMatching.originalReserve_budget_eq_original_deficit
    {m n : ℕ} (σ : OTSelector.PartialMatching m n)
    (RS : Finset (Fin m)) (RT : Finset (Fin n))
    (hS : RS ⊆ σ.freeRows) (hT : RT ⊆ σ.freeCols) :
    ((σ.freeRows \ RS).card : ℝ) + ((RT \ σ.freeCols).card : ℝ) =
      (m : ℝ) - (σ.card : ℝ) - (RS.card : ℝ) := by
  rw [Finset.sdiff_eq_empty_iff_subset.mpr hT, Finset.card_empty, Nat.cast_zero, add_zero,
    Finset.card_sdiff_of_subset hS, Nat.cast_sub (Finset.card_le_card hS),
    σ.card_freeRows, Nat.cast_sub (σ.card_le.trans (min_le_left _ _))]

/-- Dilation changes only the physical positions; every actual original
support edge keeps its exact original strict forward clock order. -/
theorem IsFullOriginalInputMatching.forward_dilation
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (hf : ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2)
    (c : ℝ) (hc : c ≠ 0) :
    ∀ e ∈ ((legalMarkedInputSceneDilation q c hc s).1.1 :
      Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
  intro e he
  have hback := (mem_support_mapHomeomorph_iff_of_legalCounting
    (0 : LegalMarkedPhysicalEdge q) (legalMarkedEdgeDilation q c hc) s.1.1
    ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1 e).mp he
  exact hf ((legalMarkedEdgeDilation q c hc).symm e) hback

/-- Genuine independently sampled original retained/reserve scenes supply
literal reserve embeddings in the SAME finite Poisson arrays and a SAME first
core σ that consumes neither reserve color. All inputs are produced from the
original class, its compact window and its unchanged kernel cost. -/
theorem exists_original_labelled_reserve_windowCore
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g) (hq : 0 < q)
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0)
    (hunit : |(c ^ q)⁻¹| + |(d ^ q)⁻¹| = 1)
    {U : Set (LegalMarkedPhysicalPoint q)} (hU : IsCompact U)
    (cost : LegalMarkedPhysicalEdge q → ℝ) :
    ∃ S > 0, ∃ J : ProbabilityMeasure
        ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))),
      (J : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
          Prod.fst = (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
            (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (J : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
          Prod.snd = legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β ∧
      ∀ᵐ p ∂(J : Measure ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
        IsOriginalReserveWindowCore q U cost
          (legalMarkedInputSceneDilation q c hc p.1.1)
          (legalMarkedInputSceneDilation q d hd p.1.2) p.2 := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q M.law) := M.palm_probability
  let : IsProbabilityMeasure α := by
    rw [← M.source_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.fst.aemeasurable
  let : IsProbabilityMeasure β := by
    rw [← M.target_clock]
    exact Measure.isProbabilityMeasure_map measurable_fst.snd.aemeasurable
  obtain ⟨S, hS, J, hl, hr, hread⟩ := exists_original_labelled_reserve_windowCoupling M N
    c d hc hd hunit (hU.prod isCompact_univ)
  have hfull : ∀ᵐ p ∂(J : Measure
      ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
      IsFullOriginalInputMatching q (legalMarkedInputSceneDilation q c hc p.1.1) ∧
      IsFullOriginalInputMatching q (legalMarkedInputSceneDilation q d hd p.1.2) := by
    have h : ∀ᵐ p ∂(J : Measure
        ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
            Prod.fst,
        IsFullOriginalInputMatching q (legalMarkedInputSceneDilation q c hc p.1) ∧
        IsFullOriginalInputMatching q (legalMarkedInputSceneDilation q d hd p.2) := by
      rw [hl]
      exact (M.ae_original_dilated_reserve_core N c d hc hd).mono (fun _ hp ↦ ⟨hp.1, hp.2.1⟩)
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hfwd : ∀ᵐ p ∂(J : Measure
      ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
      ∀ e ∈ ((legalMarkedInputSceneDilation q c hc p.1.1).1.1 :
        Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
    have hfirst : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
        ∀ e ∈ ((legalMarkedInputSceneDilation q c hc s).1.1 :
          Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
      filter_upwards [M.full_matching, M.forward] with s hs hf
      exact hs.forward_dilation hf c hc
    have h : ∀ᵐ p ∂(J : Measure
        ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
            Prod.fst,
        ∀ e ∈ ((legalMarkedInputSceneDilation q c hc p.1).1.1 :
          Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
      rw [hl]
      exact ae_fst_of_ae hfirst
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hinj : ∀ᵐ p ∂(J : Measure
      ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
        (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))),
      Injective p.2.1.2 ∧ Injective p.2.2.2 := by
    have h : ∀ᵐ b ∂(J : Measure
        ((LegalMarkedOptimalInputScene q × LegalMarkedOptimalInputScene q) ×
          (BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)))).map
            Prod.snd, Injective b.1.2 ∧ Injective b.2.2 := by
      rw [hr]
      exact ae_injective_legalInputPoissonWindowLaw q hq hS α β
    exact ae_of_ae_map measurable_snd.aemeasurable h
  refine ⟨S, hS, J, hl, hr, ?_⟩
  filter_upwards [hread, hfull, hfwd, hinj] with p hp hs hf hi
  exact exists_original_windowCore_with_unused_reserve _ _ hs.1 hs.2.simple_inputs hf p.2 hi
    hU.measurableSet hp cost

end OTSelector.Reconstruction
