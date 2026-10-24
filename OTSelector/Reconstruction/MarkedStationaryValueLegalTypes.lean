import OTSelector.Probability.SubcouplingTypedIID
import OTSelector.Finite.LegalMatchingValue
import OTSelector.Finite.BlockMaxValueComparison
import OTSelector.Reconstruction.IIDTypedCountRepair
import OTSelector.Reconstruction.FinslerPopulationScalarBinIID
import OTSelector.Reconstruction.FinslerPopulationTypedFullRetention
import OTSelector.Reconstruction.FinslerPopulationTypedIIDFacts

/-!
# Original scalar types control legal finite matching defects

The existing block matchings lie inside the true forward clock graph when each
same-type rectangle is legal. Their cardinality bounds the actual legal maximum,
with no realized type-balance assumption. The original scalar-bin RN marking
supplies these legal rectangles from the population support gap. Its exact
forgetful law returns the square-root deficit estimate to the unchanged physical
iid samples, including the integrability and natural-number form needed for
physical finite completion.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The existing block optimum uses only the same-type legal rectangles. -/
theorem blockPartialMatching_isLegal {m n : ℕ} {T : Type*} [Fintype T] [DecidableEq T]
    (typeS : Fin m → T) (typeT : Fin n → T) (c : Fin m → Fin n → ℝ)
    (allowed : Finset (Fin m × Fin n))
    (hlegal : ∀ i j, typeS i = typeT j → (i, j) ∈ allowed) :
    PartialMatching.IsLegal allowed (blockPartialMatching typeS typeT c) := by
  intro e he
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp he
  have hs := fst_mem_blockEdgesAmbient typeS typeT c ht
  have ht := snd_mem_blockEdgesAmbient typeS typeT c ht
  simp only [blockFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
  exact hlegal e.1 e.2 (hs.trans ht.symm)

/-- Hall deficiency is controlled by the actual unbalanced type counts. -/
theorem legalMaximumCard_defect_le_type_discrepancy
    {m n : ℕ} {T : Type*} [Fintype T] [DecidableEq T]
    (typeS : Fin m → T) (typeT : Fin n → T)
    (allowed : Finset (Fin m × Fin n))
    (hlegal : ∀ i j, typeS i = typeT j → (i, j) ∈ allowed) :
    (2 : ℝ) * ((min m n - PartialMatching.legalMaximumCard allowed : ℕ) : ℝ) ≤
      ∑ t, |(blockSizeS typeS t : ℝ) - (blockSizeT typeT t : ℝ)| := by
  let J : ℕ := ∑ t, min (blockSizeS typeS t) (blockSizeT typeT t)
  have hJ : J ≤ PartialMatching.legalMaximumCard allowed := by
    have h := PartialMatching.card_le_legalMaximumCard
      (blockPartialMatching_isLegal typeS typeT (fun _ _ ↦ 0) allowed hlegal)
    simpa only [card_blockPartialMatching] using h
  have hc := PartialMatching.legalMaximumCard_le_min allowed
  have hdef : min m n - PartialMatching.legalMaximumCard allowed ≤
      min (m - J) (n - J) := by omega
  have hh := two_mul_min_residual_le_sum_abs
    (blockSizeS typeS) (blockSizeT typeT)
  rw [show (∑ t, blockSizeS typeS t) = m from sum_card_blockFinset typeS,
    show (∑ t, blockSizeT typeT t) = n from sum_card_blockFinset typeT] at hh
  exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hdef) (by norm_num)).trans hh

/-- The cardinality of a typed sample block equals the original Bernoulli count. -/
theorem cast_blockSize_eq_iidTypeCount {Ω X T : Type*} {n : ℕ} [DecidableEq T]
    (sample : Fin n → Ω → X) (tag : X → T) (ω : Ω) (t : T) :
    (blockSizeS (fun i ↦ tag (sample i ω)) t : ℝ) =
      iidTypeCount sample {x | tag x = t} ω := by
  classical
  unfold blockSizeS blockFinset iidTypeCount
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  simp only [Nat.cast_one, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : tag (sample i ω) = t <;> simp [h]


/-- Measurable finite graph events also make the actual legal cardinality measurable. -/
theorem measurable_legalMaximumCard_cast {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (allowed : Ω → Finset (Fin m × Fin n))
    (hallowed : ∀ E, MeasurableSet {ω | allowed ω = E}) :
    Measurable (fun ω ↦ (PartialMatching.legalMaximumCard (allowed ω) : ℝ)) := by
  classical
  have hrepr : (fun ω ↦ (PartialMatching.legalMaximumCard (allowed ω) : ℝ)) = fun ω ↦
      ∑ E : Finset (Fin m × Fin n),
        if allowed ω = E then (PartialMatching.legalMaximumCard E : ℝ) else 0 := by
    funext ω
    simp
  rw [hrepr]
  exact Finset.measurable_sum _ (fun E _ ↦ measurable_const.ite (hallowed E) measurable_const)

/-- The legal finite graph read directly on original scalar sample arrays. -/
def scalarClockLegalGraph {m n : ℕ} (source : Fin m → ℝ) (target : Fin n → ℝ) :
    Finset (Fin m × Fin n) :=
  Finset.univ.filter (fun e ↦ source e.1 < target e.2)

/-- Every event determining an original scalar-clock graph is measurable. -/
theorem measurableSet_scalarClockLegalGraph_eq {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (source : Fin m → Ω → ℝ) (target : Fin n → Ω → ℝ)
    (hs : ∀ i, Measurable (source i)) (ht : ∀ j, Measurable (target j))
    (E : Finset (Fin m × Fin n)) :
    MeasurableSet {ω | scalarClockLegalGraph (fun i ↦ source i ω) (fun j ↦ target j ω) = E} := by
  classical
  have hrepr : {ω | scalarClockLegalGraph (fun i ↦ source i ω) (fun j ↦ target j ω) = E} =
      ⋂ e : Fin m × Fin n, {ω | (source e.1 ω < target e.2 ω) ↔ e ∈ E} := by
    ext ω
    simp [Finset.ext_iff, scalarClockLegalGraph]
  rw [hrepr]
  apply MeasurableSet.iInter
  intro e
  by_cases he : e ∈ E
  · simpa only [he, iff_true] using measurableSet_lt (hs e.1) (ht e.2)
  · simpa only [he, iff_false, not_lt] using measurableSet_le (ht e.2) (hs e.1)

/-- A finite realized legal-cardinality defect is integrable under any probability law. -/
theorem integrable_legalMaximumCard_defect {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (allowed : Ω → Finset (Fin n × Fin n))
    (hallowed : ∀ E, MeasurableSet {ω | allowed ω = E}) :
    Integrable (fun ω ↦ (n : ℝ) - PartialMatching.legalMaximumCard (allowed ω)) P := by
  apply Integrable.of_bound
    (measurable_const.sub
      (measurable_legalMaximumCard_cast allowed hallowed)).aestronglyMeasurable n
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact sub_le_self _ (Nat.cast_nonneg _)
  · exact sub_nonneg.mpr (Nat.cast_le.mpr (by
      simpa only [min_self] using PartialMatching.legalMaximumCard_le_min (allowed ω)))

/-- Equal original type laws give the expected legal-cardinality defect without
requiring equal realized counts in any type. -/
theorem integral_legalMaximumCard_defect_le_of_iid_types
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] [DecidableEq T] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (L : Measure T) [IsProbabilityMeasure L]
    (xs ys : Fin n → Ω → T) (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = L) (hyl : ∀ i, P.map (ys i) = L)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω j ↦ ys j ω) P)
    (allowed : Ω → Finset (Fin n × Fin n))
    (hlegal : ∀ᵐ ω ∂P, ∀ i j, xs i ω = ys j ω → (i, j) ∈ allowed ω) :
    (∫ ω, (n : ℝ) - PartialMatching.legalMaximumCard (allowed ω) ∂P) ≤
      (1 / 2 : ℝ) * Real.sqrt (2 * (n : ℝ) * Fintype.card T) := by
  have hmass : (∑ t : T, L.real {t}) = 1 := by
    simp
  obtain ⟨hdisc, hmean⟩ := iidTypeCount_total_difference_bound P L L xs ys hx hy
    hxi hyi hxl hyl hxy (fun t ↦ {t}) (fun t ↦ {t})
    (fun _ ↦ measurableSet_singleton _) (fun _ ↦ measurableSet_singleton _)
    (fun _ ↦ rfl) hmass
  have hpt : ∀ᵐ ω ∂P, (n : ℝ) - PartialMatching.legalMaximumCard (allowed ω) ≤
      (1 / 2 : ℝ) * ∑ t : T, |iidTypeCount xs {t} ω - iidTypeCount ys {t} ω| := by
    filter_upwards [hlegal] with ω hω
    have h := legalMaximumCard_defect_le_type_discrepancy
      (fun i ↦ xs i ω) (fun j ↦ ys j ω) (allowed ω) hω
    have hcard : PartialMatching.legalMaximumCard (allowed ω) ≤ n :=
      (PartialMatching.legalMaximumCard_le_min _).trans (min_le_left _ _)
    simp only [min_self, Nat.cast_sub hcard] at h
    have hcount (zs : Fin n → Ω → T) (t : T) :
        (blockSizeS (fun i ↦ zs i ω) t : ℝ) = iidTypeCount zs {t} ω := by
      simpa only [id_eq, Set.ofPred_eq_eq_singleton] using
        cast_blockSize_eq_iidTypeCount zs id ω t
    have hcountT (zs : Fin n → Ω → T) (t : T) :
        (blockSizeT (fun i ↦ zs i ω) t : ℝ) = iidTypeCount zs {t} ω := hcount zs t
    simp only [hcount, hcountT] at h
    linarith
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ (n : ℝ) - PartialMatching.legalMaximumCard (allowed ω) :=
    Filter.Eventually.of_forall fun ω ↦ sub_nonneg.mpr (Nat.cast_le.mpr (by
      simpa using PartialMatching.legalMaximumCard_le_min (allowed ω)))
  refine (integral_mono_of_nonneg hnonneg (hdisc.const_mul (1 / 2)) hpt).trans ?_
  rw [integral_const_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hmean (by norm_num : (0 : ℝ) ≤ 1 / 2)


/-- The actual original coupling and scalar-bin RN marking produce the legal
count-defect estimate on the unchanged physical iid samples. -/
theorem scalarBinPopulationTypes_integral_legalMaximumCard_defect
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
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1) (n : ℕ) :
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    let deficit := fun ω : (Fin n → X) × (Fin n → Y) ↦
      (n : ℝ) - PartialMatching.legalMaximumCard
        (scalarClockLegalGraph (fun i ↦ source (ω.1 i)) (fun j ↦ target (ω.2 j)))
    Integrable deficit P₀ ∧
      (∫ ω, deficit ω ∂P₀) ≤ (1 / 2 : ℝ) *
        Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (J × Fin D.count × Fin D.count))) := by
  classical
  let Types := scalarBinPopulationTypes D chart source target π hchart hs ht
  let Tag := Option (J × Fin D.count × Fin D.count)
  let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
  let allowed := fun ω : (Fin n → X) × (Fin n → Y) ↦
    scalarClockLegalGraph (fun i ↦ source (ω.1 i)) (fun j ↦ target (ω.2 j))
  let deficit := fun ω ↦ (n : ℝ) - PartialMatching.legalMaximumCard (allowed ω)
  have hallowed (E) : MeasurableSet {ω | allowed ω = E} :=
    measurableSet_scalarClockLegalGraph_eq
      (fun i (ω : (Fin n → X) × (Fin n → Y)) ↦ source (ω.1 i))
      (fun j (ω : (Fin n → X) × (Fin n → Y)) ↦ target (ω.2 j))
      (fun _ ↦ hs.comp (by fun_prop)) (fun _ ↦ ht.comp (by fun_prop)) E
  have hdi : Integrable deficit P₀ := integrable_legalMaximumCard_defect P₀ allowed hallowed
  have hdm : Measurable deficit :=
    measurable_const.sub (measurable_legalMaximumCard_cast allowed hallowed)
  have hprob := Types.marked_probabilities hπ
  let : IsProbabilityMeasure (Types.sourceMarkedLaw μ) := hprob.1
  let : IsProbabilityMeasure (Types.targetMarkedLaw ν) := hprob.2.1
  let : IsProbabilityMeasure Types.typeLaw := hprob.2.2
  let P := (Measure.pi (fun _ : Fin n ↦ Types.sourceMarkedLaw μ)).prod
    (Measure.pi (fun _ : Fin n ↦ Types.targetMarkedLaw ν))
  let xs : Fin n → ((Fin n → X × Tag) × (Fin n → Y × Tag)) → Tag :=
    fun i ω ↦ (ω.1 i).2
  let ys : Fin n → ((Fin n → X × Tag) × (Fin n → Y × Tag)) → Tag :=
    fun j ω ↦ (ω.2 j).2
  have hxs : Measurable (fun ω i ↦ xs i ω) := by fun_prop
  have hys : Measurable (fun ω j ↦ ys j ω) := by fun_prop
  obtain ⟨hxi, hyi, hxl, hyl, hxy⟩ := iid_facts_of_array_product_law P Types.typeLaw
    (fun ω i ↦ xs i ω) (fun ω j ↦ ys j ω) hxs hys (Types.iid_type_law hπ)
  have hfull : ∑ t, Types.component t = π :=
    scalarBinPopulationTypes_sum_eq D chart source target π hchart hs ht hI
  have hsome := Types.iid_marked_ae_some_of_sum_eq (I := Fin n) (J := Fin n) hπ hfull
  have hhalf := scalarBinPopulationTypes_iid_half_gap D chart source target π
    (μ := μ) (ν := ν) hchart hs ht (NS := Fin n) (NT := Fin n) hgap
  let forget : ((Fin n → X × Tag) × (Fin n → Y × Tag)) →
      ((Fin n → X) × (Fin n → Y)) :=
    fun ω ↦ (fun i ↦ (ω.1 i).1, fun j ↦ (ω.2 j).1)
  have hf : Measurable forget := by fun_prop
  have hlegal : ∀ᵐ ω ∂P, ∀ i j, xs i ω = ys j ω → (i, j) ∈ allowed (forget ω) := by
    filter_upwards [hsome, hhalf] with ω hωs hωg
    intro i j hij
    obtain ⟨t, hit⟩ := hωs.1 i
    have hjt : (ω.2 j).2 = some t := hij.symm.trans hit
    have hgap' := hωg i j t hit hjt
    have hforward : source (ω.1 i).1 < target (ω.2 j).1 := by linarith
    simpa only [allowed, forget, scalarClockLegalGraph,
      Finset.mem_filter, Finset.mem_univ, true_and] using hforward
  have hbound := integral_legalMaximumCard_defect_le_of_iid_types P Types.typeLaw xs ys
    (fun i ↦ (measurable_pi_apply i).comp hxs)
    (fun j ↦ (measurable_pi_apply j).comp hys)
    hxi hyi hxl hyl hxy (fun ω ↦ allowed (forget ω)) hlegal
  have hmap : P.map forget = P₀ := Types.iid_physical_law hπ
  have hid : (∫ ω, deficit ω ∂P₀) = ∫ ω, deficit (forget ω) ∂P := by
    rw [← hmap, integral_map hf.aemeasurable hdm.aestronglyMeasurable]
  exact ⟨hdi, hid.trans_le hbound⟩


/-- The same original-sample estimate in the natural-number deficit form used
by finite physical completion, with a constant independent of sample size. -/
theorem scalarBinPopulationTypes_integral_legalMaximumCard_defect_nat
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
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1) (n : ℕ) :
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    let deficit := fun ω : (Fin n → X) × (Fin n → Y) ↦
      ((n - PartialMatching.legalMaximumCard
        (scalarClockLegalGraph (fun i ↦ source (ω.1 i)) (fun j ↦ target (ω.2 j))) : ℕ) : ℝ)
    Integrable deficit P₀ ∧ (∫ ω, deficit ω ∂P₀) ≤
      ((1 / 2 : ℝ) * Real.sqrt
        (2 * (Fintype.card (Option (J × Fin D.count × Fin D.count)) : ℝ))) * Real.sqrt n := by
  have h := scalarBinPopulationTypes_integral_legalMaximumCard_defect D hδ chart source
    target π μ ν hπ hchart hs ht hI hgap n
  have heq : (fun ω : (Fin n → X) × (Fin n → Y) ↦
      ((n - PartialMatching.legalMaximumCard
        (scalarClockLegalGraph (fun i ↦ source (ω.1 i)) (fun j ↦ target (ω.2 j))) : ℕ) : ℝ)) =
      fun ω ↦ (n : ℝ) - PartialMatching.legalMaximumCard
        (scalarClockLegalGraph (fun i ↦ source (ω.1 i)) (fun j ↦ target (ω.2 j))) := by
    funext ω
    rw [Nat.cast_sub (by simpa only [min_self] using
      (PartialMatching.legalMaximumCard_le_min
        (scalarClockLegalGraph (fun i ↦ source (ω.1 i)) (fun j ↦ target (ω.2 j)))))]
  rw [heq]
  refine ⟨h.1, h.2.trans_eq ?_⟩
  rw [show 2 * (n : ℝ) * Fintype.card (Option (J × Fin D.count × Fin D.count)) =
      (2 * (Fintype.card (Option (J × Fin D.count × Fin D.count)) : ℝ)) * n by ring,
    Real.sqrt_mul (by positivity :
      0 ≤ 2 * (Fintype.card (Option (J × Fin D.count × Fin D.count)) : ℝ))]
  ring

end OTSelector.Reconstruction
