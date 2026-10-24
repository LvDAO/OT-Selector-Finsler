import OTSelector.Reconstruction.FinslerConcreteUpperClassPressure
import OTSelector.Reconstruction.FinslerConcreteUpperClassReference

/-!
Raw original clocks are observed through their original finite bins. Positive
retained pair classes identify their two bins exactly, while zero classes may
keep arbitrary fallbacks. The resulting fixed class law is independent of the
original spatial label and has exactly the original pair weights.
-/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- The original finite bin index, with a fixed unused value outside its range. -/
def FiniteScalarBins.classify {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (fallback : Fin Q.count) (x : ℝ) : Fin Q.count :=
  if h : ∃ i, x ∈ Q.cell i then h.choose else fallback

theorem FiniteScalarBins.classify_eq_of_mem {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (fallback i : Fin Q.count) {x : ℝ} (hx : x ∈ Q.cell i) :
    Q.classify fallback x = i := by
  let h : ∃ j, x ∈ Q.cell j := ⟨i, hx⟩
  have hi : h.choose = i := by
    by_contra hne
    exact disjoint_left.mp (Q.disjoint hne) h.choose_spec hx
  simp only [classify, dite_eq_left h, hi]

theorem FiniteScalarBins.measurable_classify {range : Set ℝ} {width : ℝ}
    (Q : FiniteScalarBins range width) (fallback : Fin Q.count) : Measurable (Q.classify fallback) := by
  intro s _
  have heq : Q.classify fallback ⁻¹' s =
      (rangeᶜ ∩ (if fallback ∈ s then univ else ∅)) ∪
        ⋃ i, if i ∈ s then Q.cell i else ∅ := by
    ext x
    by_cases hx : x ∈ range
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (Q.union_eq.symm ▸ hx)
      simp only [mem_preimage, Q.classify_eq_of_mem fallback i hi, mem_union, mem_inter_iff,
        mem_compl_iff, hx, not_true_eq_false, false_and, false_or]
      constructor
      · intro his
        exact mem_iUnion.mpr ⟨i, by simpa only [ite_eq_left his] using hi⟩
      · intro h
        obtain ⟨j, hj⟩ := mem_iUnion.mp h
        by_cases hjs : j ∈ s
        · have hxj : x ∈ Q.cell j := by simpa only [ite_eq_left hjs] using hj
          have hij : i = j := by
            by_contra hne
            exact disjoint_left.mp (Q.disjoint hne) hi hxj
          exact hij.symm ▸ hjs
        · simp only [ite_eq_right hjs, mem_empty_iff_false] at hj
    · have hn : ¬∃ i, x ∈ Q.cell i := fun ⟨i, hi⟩ ↦ hx (Q.subset i hi)
      simp only [classify, dite_eq_right hn, mem_preimage, mem_union, mem_inter_iff,
        mem_compl_iff, hx, not_false_eq_true, true_and]
      have hout : x ∉ ⋃ i, if i ∈ s then Q.cell i else ∅ := by
        intro h
        obtain ⟨i, hi⟩ := mem_iUnion.mp h
        by_cases his : i ∈ s
        · exact hn ⟨i, by simpa only [ite_eq_left his] using hi⟩
        · simp only [ite_eq_right his, mem_empty_iff_false] at hi
      simp only [hout, or_false]
      by_cases hf : fallback ∈ s <;> simp only [hf, ite_true, ite_false, mem_univ, mem_empty_iff_false]
  rw [heq]
  apply MeasurableSet.union
  · exact (Q.union_eq ▸ MeasurableSet.iUnion Q.measurable_cell).compl.inter (by split_ifs <;> simp)
  · exact MeasurableSet.iUnion fun i ↦ by split_ifs <;> simp_all only [Q.measurable_cell, MeasurableSet.empty]

variable {Z X Y I J : Type*} [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
  [Fintype I] [Fintype J] [MeasurableSpace I] [MeasurableSpace J]
  [MeasurableSingletonClass I] [MeasurableSingletonClass J]

/-- Exact finite pair-class observation uses only positive original bin masses
for nonzero retained pair weights. It permits arbitrary zero-class fallbacks. -/
theorem finiteClassPopulationCoupling_map_actual_classes
    (κs : Kernel Z X) (κt : Kernel Z Y)
    [∀ z, IsFiniteMeasure (κs z)] [∀ z, IsFiniteMeasure (κt z)]
    (S : I → Set X) (T : J → Set Y)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (fallbackS : I → X) (fallbackT : J → Y)
    (classS : X → I) (classT : Y → J) (hmS : Measurable classS) (hmT : Measurable classT)
    (hclassS : ∀ i x, x ∈ S i → classS x = i) (hclassT : ∀ j y, y ∈ T j → classT y = j)
    (P : I → J → ℝ) (z : Z)
    (hpositive : ∀ i j, P i j ≠ 0 → κs z (S i) ≠ 0 ∧ κt z (T j) ≠ 0) :
    (finiteClassPopulationCoupling P
      (fun i ↦ normalizedActualBinKernel κs (S i) (hS i) (fallbackS i) z)
      (fun j ↦ normalizedActualBinKernel κt (T j) (hT j) (fallbackT j) z)).map
      (Prod.map classS classT) = clockClassPairMeasure P := by
  unfold finiteClassPopulationCoupling clockClassPairMeasure
  rw [Measure.map_finset_sum' (hmS.prodMap hmT).aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.map_finset_sum' (hmS.prodMap hmT).aemeasurable]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_smul]
  by_cases hp : P i j = 0
  · simp only [hp, ENNReal.ofReal_zero, zero_smul]
  · rw [← Measure.map_prod_map _ _ hmS hmT]
    have hs : classS =ᵐ[normalizedActualBinKernel κs (S i) (hS i) (fallbackS i) z] (fun _ ↦ i) :=
      (normalizedActualBinKernel_supported_of_mass_ne_zero κs (S i) (hS i) (fallbackS i) z
        (hpositive i j hp).1).mono fun x hx ↦ hclassS i x hx
    have ht : classT =ᵐ[normalizedActualBinKernel κt (T j) (hT j) (fallbackT j) z] (fun _ ↦ j) :=
      (normalizedActualBinKernel_supported_of_mass_ne_zero κt (T j) (hT j) (fallbackT j) z
        (hpositive i j hp).2).mono fun y hy ↦ hclassT j y hy
    rw [Measure.map_congr hs, Measure.map_congr ht, Measure.map_const, Measure.map_const,
      measure_univ, measure_univ, one_smul, one_smul]

/-- A fixed pair-class flow over the original cell has a literal independent
spatial-label/class law. The two class coordinates may remain correlated. -/
theorem fixedPairClassKernel_original_cell_law
    (μ : Measure Z) [SFinite μ] (κs : Kernel Z X) (κt : Kernel Z Y)
    [∀ z, IsFiniteMeasure (κs z)] [∀ z, IsFiniteMeasure (κt z)]
    (S : I → Set X) (T : J → Set Y)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (fallbackS : I → X) (fallbackT : J → Y)
    (classS : X → I) (classT : Y → J) (hmS : Measurable classS) (hmT : Measurable classT)
    (hclassS : ∀ i x, x ∈ S i → classS x = i) (hclassT : ∀ j y, y ∈ T j → classT y = j)
    (P : I → J → ℝ)
    (hpositive : ∀ᵐ z ∂μ, ∀ i j, P i j ≠ 0 → κs z (S i) ≠ 0 ∧ κt z (T j) ≠ 0) :
    (μ ⊗ₘ finiteClassPopulationKernel (fun _ i j ↦ P i j)
      (fun i ↦ normalizedActualBinKernel κs (S i) (hS i) (fallbackS i))
      (fun j ↦ normalizedActualBinKernel κt (T j) (hT j) (fallbackT j))).map
      (Prod.map id (Prod.map classS classT)) = μ.prod (clockClassPairMeasure P) := by
  rw [← Measure.compProd_map (hmS.prodMap hmT)]
  have heq : (finiteClassPopulationKernel (fun _ i j ↦ P i j)
      (fun i ↦ normalizedActualBinKernel κs (S i) (hS i) (fallbackS i))
      (fun j ↦ normalizedActualBinKernel κt (T j) (hT j) (fallbackT j))).map
        (Prod.map classS classT) =ᵐ[μ] Kernel.const Z (clockClassPairMeasure P) := by
    filter_upwards [hpositive] with z hz
    rw [Kernel.map_apply _ (hmS.prodMap hmT),
      finiteClassPopulationKernel_apply (fun _ i j ↦ P i j) (fun _ _ ↦ measurable_const)
        (fun i ↦ normalizedActualBinKernel κs (S i) (hS i) (fallbackS i))
        (fun j ↦ normalizedActualBinKernel κt (T j) (hT j) (fallbackT j)) z,
      Kernel.const_apply]
    exact finiteClassPopulationCoupling_map_actual_classes κs κt S T hS hT fallbackS fallbackT
      classS classT hmS hmT hclassS hclassT P z hz
  rw [Measure.compProd_congr heq, Measure.compProd_const]

/-- Normalizing the observed original cell law gives the original normalized
spatial law times the exact fixed P/totalP pair-class reference. -/
theorem fixedPairClassKernel_normalized_original_cell_law
    (μ : Measure Z) [IsFiniteMeasure μ] (κs : Kernel Z X) (κt : Kernel Z Y)
    [∀ z, IsFiniteMeasure (κs z)] [∀ z, IsFiniteMeasure (κt z)]
    (S : I → Set X) (T : J → Set Y)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (fallbackS : I → X) (fallbackT : J → Y)
    (classS : X → I) (classT : Y → J) (hmS : Measurable classS) (hmT : Measurable classT)
    (hclassS : ∀ i x, x ∈ S i → classS x = i) (hclassT : ∀ j y, y ∈ T j → classT y = j)
    (P : I → J → ℝ)
    (hpositive : ∀ᵐ z ∂μ, ∀ i j, P i j ≠ 0 → κs z (S i) ≠ 0 ∧ κt z (T j) ≠ 0) :
    (normalizedFiniteLaw (μ ⊗ₘ finiteClassPopulationKernel (fun _ i j ↦ P i j)
      (fun i ↦ normalizedActualBinKernel κs (S i) (hS i) (fallbackS i))
      (fun j ↦ normalizedActualBinKernel κt (T j) (hT j) (fallbackT j)))).map
      (Prod.map id (Prod.map classS classT)) =
      (normalizedFiniteLaw μ).prod (normalizedClockClassPairMeasure P) := by
  let raw := μ ⊗ₘ finiteClassPopulationKernel (fun _ i j ↦ P i j)
    (fun i ↦ normalizedActualBinKernel κs (S i) (hS i) (fallbackS i))
    (fun j ↦ normalizedActualBinKernel κt (T j) (hT j) (fallbackT j))
  let observe : Z × (X × Y) → Z × (I × J) := Prod.map id (Prod.map classS classT)
  have hm : Measurable observe := measurable_id.prodMap (hmS.prodMap hmT)
  have hmass : (raw.map observe).real univ = raw.real univ := by
    simp only [measureReal_def, Measure.map_apply hm MeasurableSet.univ, preimage_univ]
  have hnormalize : (normalizedFiniteLaw raw).map observe = normalizedFiniteLaw (raw.map observe) := by
    simp only [normalizedFiniteLaw, hmass, Measure.map_smul]
  rw [hnormalize, fixedPairClassKernel_original_cell_law μ κs κt S T hS hT fallbackS fallbackT
    classS classT hmS hmT hclassS hclassT P hpositive, normalizedFiniteLaw_prod_eq]
  rfl


/-- The actual exact finite marginal split makes every nonzero frozen pair
class have positive ORIGINAL bin mass. No in-bin fallback condition is needed. -/
theorem fixed_reference_bin_masses_ne_zero_of_original_split
    (μ : Measure Z) (κs : Kernel Z X) (κt : Kernel Z Y)
    (S : I → Set X) (T : J → Set Y) (P : I → J → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (density : Z → ℝ) (residual : Z → I → J → ℝ)
    (hdensity : ∀ᵐ z ∂μ, 0 < density z)
    (hresidual : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ residual z i j)
    (hrow : ∀ᵐ z ∂μ, ∀ i, ∑ j, (P i j / density z + residual z i j) = (κs z).real (S i))
    (hcol : ∀ᵐ z ∂μ, ∀ j, ∑ i, (P i j / density z + residual z i j) = (κt z).real (T j)) :
    ∀ᵐ z ∂μ, ∀ i j, P i j ≠ 0 → κs z (S i) ≠ 0 ∧ κt z (T j) ≠ 0 := by
  filter_upwards [hdensity, hresidual, hrow, hcol] with z hd hres hr hc
  intro i j hp
  have hpositive : 0 < P i j := lt_of_le_of_ne (hP i j) (Ne.symm hp)
  have hwhole : ∀ i j, 0 ≤ P i j / density z + residual z i j := fun i j ↦
    add_nonneg (div_nonneg (hP i j) hd.le) (hres i j)
  have hij : 0 < P i j / density z + residual z i j :=
    add_pos_of_pos_of_nonneg (div_pos hpositive hd) (hres i j)
  have hbin := positive_classFlow_marginals
    (fun i j ↦ P i j / density z + residual z i j)
    (fun i ↦ (κs z).real (S i)) (fun j ↦ (κt z).real (T j)) hwhole hr hc i j hij
  constructor
  · intro hzero
    have heq : (κs z).real (S i) = 0 := by simp only [measureReal_def, hzero, ENNReal.toReal_zero]
    exact hbin.1.ne' heq
  · intro hzero
    have heq : (κt z).real (T j) = 0 := by simp only [measureReal_def, hzero, ENNReal.toReal_zero]
    exact hbin.2.ne' heq

/-- For the actual produced full clock bins, exact original finite marginal
restoration supplies a measurable class observation and the normalized
spatial/class product law, with no positive-bin assumption supplied. -/
theorem FiniteScalarBins.exists_original_split_class_observation
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (μ : Measure Z) [IsFiniteMeasure μ] (κs κt : Kernel Z ℝ)
    [∀ z, IsFiniteMeasure (κs z)] [∀ z, IsFiniteMeasure (κt z)]
    (fallbackS fallbackT : Fin Q.count → ℝ)
    (P : Fin Q.count → Fin Q.count → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hmass : 0 < ∑ i, ∑ j, P i j)
    (density : Z → ℝ) (residual : Z → Fin Q.count → Fin Q.count → ℝ)
    (hdensity : ∀ᵐ z ∂μ, 0 < density z)
    (hresidual : ∀ᵐ z ∂μ, ∀ i j, 0 ≤ residual z i j)
    (hrow : ∀ᵐ z ∂μ, ∀ i, ∑ j, (P i j / density z + residual z i j) = (κs z).real (Q.cell i))
    (hcol : ∀ᵐ z ∂μ, ∀ j, ∑ i, (P i j / density z + residual z i j) = (κt z).real (Q.cell j)) :
    ∃ classify : ℝ → Fin Q.count, Measurable classify ∧
      (∀ i x, x ∈ Q.cell i → classify x = i) ∧
      (normalizedFiniteLaw (μ ⊗ₘ finiteClassPopulationKernel (fun _ i j ↦ P i j)
        (fun i ↦ normalizedActualBinKernel κs (Q.cell i) (Q.measurable_cell i) (fallbackS i))
        (fun j ↦ normalizedActualBinKernel κt (Q.cell j) (Q.measurable_cell j) (fallbackT j)))).map
        (Prod.map id (Prod.map classify classify)) =
        (normalizedFiniteLaw μ).prod (normalizedClockClassPairMeasure P) := by
  classical
  have hnonempty : Nonempty (Fin Q.count) := by
    by_contra hn
    haveI : IsEmpty (Fin Q.count) := not_nonempty_iff.mp hn
    have hzero : (∑ i, ∑ j, P i j) = 0 := by simp
    linarith
  let classify := Q.classify (Classical.choice hnonempty)
  have hm : Measurable classify := Q.measurable_classify _
  have hclass : ∀ i x, x ∈ Q.cell i → classify x = i := fun i x hx ↦
    Q.classify_eq_of_mem _ i hx
  refine ⟨classify, hm, hclass, ?_⟩
  exact fixedPairClassKernel_normalized_original_cell_law μ κs κt Q.cell Q.cell
    Q.measurable_cell Q.measurable_cell fallbackS fallbackT classify classify hm hm hclass hclass P
    (fixed_reference_bin_masses_ne_zero_of_original_split μ κs κt Q.cell Q.cell P hP
      density residual hdensity hresidual hrow hcol)

end OTSelector.Reconstruction
