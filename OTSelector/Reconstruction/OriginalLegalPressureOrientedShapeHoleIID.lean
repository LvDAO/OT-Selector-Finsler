import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHoleTagged
import OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHoleLabels
import OTSelector.Reconstruction.FinslerPopulationTypedIIDFacts
import OTSelector.Reconstruction.OriginalFiniteOrderedMonochromeClasses

/-! Arbitrary actual spatial laws and the original clock coupling give legal fixed-sample hole rates. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace OTSelector.Reconstruction

/-- The actual two independent equal-size endpoint clouds on the same arbitrary spatial law. -/
def originalShapeHoleIIDLaw {q : ℕ} (space : Measure (DyadicUnitCube q))
    (α β : Measure ℝ) (n : ℕ) :
    Measure ((Fin n → DyadicUnitCube q × ℝ) × (Fin n → DyadicUnitCube q × ℝ)) :=
  (Measure.pi (fun _ : Fin n ↦ space.prod α)).prod (Measure.pi (fun _ : Fin n ↦ space.prod β))

/-- The unchanged original scalar graph's true maximum-cardinality value. -/
def originalShapeHoleIIDValue {q n : ℕ}
    (cost : (DyadicUnitCube q × ℝ) → (DyadicUnitCube q × ℝ) → ℝ)
    (sample : (Fin n → DyadicUnitCube q × ℝ) × (Fin n → DyadicUnitCube q × ℝ)) : ℝ :=
  PartialMatching.legalMaximumValue (scalarClockLegalGraph (fun i ↦ (sample.1 i).2)
    (fun j ↦ (sample.2 j).2)) (fun i j ↦ cost (sample.1 i) (sample.2 j))

/-- Independent latent arrays retain their true two-array product law under
arbitrary separate endpoint readouts. -/
theorem originalShapeHole_map_two_iid_arrays {Z X Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure Z) [IsProbabilityMeasure law] (n : ℕ)
    (left : Z → X) (right : Z → Y) (hl : Measurable left) (hr : Measurable right) :
    ((Measure.pi (fun _ : Fin n ↦ law)).prod (Measure.pi (fun _ : Fin n ↦ law))).map
      (fun sample ↦ ((fun i ↦ left (sample.1 i)),fun j ↦ right (sample.2 j))) =
      (Measure.pi (fun _ : Fin n ↦ law.map left)).prod (Measure.pi (fun _ : Fin n ↦ law.map right)) := by
  change ((Measure.pi (fun _ : Fin n ↦ law)).prod (Measure.pi (fun _ : Fin n ↦ law))).map
    (Prod.map (fun xs i ↦ left (xs i)) (fun ys j ↦ right (ys j))) = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.pi_map_pi (fun _ ↦ hl.aemeasurable),Measure.pi_map_pi (fun _ ↦ hr.aemeasurable)]

/-- The actual mark coupling constructs all latent finite types internally,
then forgetting hidden clocks returns exactly the two independent original
endpoint laws. Arbitrary spatial probabilities, including atoms and holes,
obey the true legal-maximum rate without a density or balanced-count premise. -/
theorem originalShapeHole_integral_legalMaximumValue_le_of_space_clock_law
    {q n : ℕ} (hq : 4 < q) (space : Measure (DyadicUnitCube q)) [IsProbabilityMeasure space]
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (π : Measure (ℝ × ℝ)) (hπ : Vlasov.IsCoupling π α β)
    {I : Set ℝ} {gap diameter : ℝ} (bins : FiniteScalarBins I gap) (hgap : 0 < gap)
    (hsep : ConditionalClockSupportBounds α β gap diameter)
    (hI : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I) (horder : ∀ᵐ p ∂π, p.1 ≤ p.2)
    (cost : (DyadicUnitCube q × ℝ) → (DyadicUnitCube q × ℝ) → ℝ)
    (hc : Measurable (Function.uncurry cost)) {C : ℝ} (hC : 0 ≤ C)
    (hcn : ∀ x y, 0 ≤ cost x y)
    (hquadratic : ∀ x y, cost x y ≤ C*‖dyadicCubePoint x.1-dyadicCubePoint y.1‖^2) :
    Integrable (originalShapeHoleIIDValue cost) (originalShapeHoleIIDLaw space α β n) ∧
      (∫ sample,originalShapeHoleIIDValue cost sample ∂originalShapeHoleIIDLaw space α β n) ≤
        C*dyadicMatchingConstant q*((bins.count+1 : ℕ) : ℝ)^(2/(q : ℝ))*(n : ℝ)^(1-2/(q : ℝ)) +
        (C+2*((bins.count : ℝ)+1)*C)*Real.sqrt (2*(n : ℝ)*(bins.count+1)) := by
  have : IsProbabilityMeasure (π.map Prod.fst) := by rw [hπ.1]; infer_instance
  have : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map Prod.fst
  let Z := DyadicUnitCube q × (ℝ × ℝ)
  let Λ : Measure Z := space.prod π
  let P := (Measure.pi (fun _ : Fin n ↦ Λ)).prod (Measure.pi (fun _ : Fin n ↦ Λ))
  let readS : Z → DyadicUnitCube q × ℝ := fun z ↦ (z.1,z.2.1)
  let readT : Z → DyadicUnitCube q × ℝ := fun z ↦ (z.1,z.2.2)
  have hs : Measurable readS := by fun_prop
  have ht : Measurable readT := by fun_prop
  let observe : Z → Fin (bins.count+1) × DyadicUnitCube q :=
    fun z ↦ (originalShapeHoleScalarLabel bins z.2.2,z.1)
  have ho : Measurable observe :=
    ((measurable_originalShapeHoleScalarLabel bins).comp measurable_snd.snd).prodMk measurable_fst
  let L := Λ.map observe
  have : IsProbabilityMeasure L := Measure.isProbabilityMeasure_map ho.aemeasurable
  let xs := fun (i : Fin n) (ω : (Fin n → Z) × (Fin n → Z)) ↦ observe (ω.1 i)
  let ys := fun (j : Fin n) (ω : (Fin n → Z) × (Fin n → Z)) ↦ observe (ω.2 j)
  have hx (i : Fin n) : Measurable (xs i) := ho.comp ((measurable_pi_apply i).comp measurable_fst)
  have hy (j : Fin n) : Measurable (ys j) := ho.comp ((measurable_pi_apply j).comp measurable_snd)
  obtain ⟨hxi,hyi,hxl,hyl,hxy⟩ := iid_facts_of_array_product_law P L
    (fun ω i ↦ xs i ω) (fun ω j ↦ ys j ω) (by fun_prop) (by fun_prop)
    (originalShapeHole_map_two_iid_arrays Λ n observe observe ho ho)
  have hSsupport : ∀ᵐ p ∂π, p.1 ∈ α.support := ae_of_ae_map measurable_fst.aemeasurable
    (by rw [hπ.1]; exact Measure.support_mem_ae)
  have hTsupport : ∀ᵐ p ∂π, p.2 ∈ β.support := ae_of_ae_map measurable_snd.aemeasurable
    (by rw [hπ.2]; exact Measure.support_mem_ae)
  have hpairs : ∀ᵐ p ∂π, p.1 ∈ I ∧ p.2 ∈ I ∧ gap ≤ p.2-p.1 ∧ p.1 ∈ α.support ∧ p.2 ∈ β.support := by
    filter_upwards [hI,horder,hSsupport,hTsupport] with p hI ho hs ht
    have hg := hsep.separated p.1 hs p.2 ht
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr ho),neg_sub] at hg
    exact ⟨hI.1,hI.2,hg,hs,ht⟩
  have hZ : ∀ᵐ z ∂Λ, z.2.1 ∈ I ∧ z.2.2 ∈ I ∧ gap ≤ z.2.2-z.2.1 ∧
      z.2.1 ∈ α.support ∧ z.2.2 ∈ β.support := Measure.quasiMeasurePreserving_snd.ae hpairs
  have hzS := ae_all_iff.mpr (fun i : Fin n ↦
    ((measurePreserving_eval (fun _ : Fin n ↦ Λ) i).comp
      (measurePreserving_fst (μ := Measure.pi (fun _ : Fin n ↦ Λ))
        (ν := Measure.pi (fun _ : Fin n ↦ Λ)))).quasiMeasurePreserving.ae hZ)
  have hzT := ae_all_iff.mpr (fun j : Fin n ↦
    ((measurePreserving_eval (fun _ : Fin n ↦ Λ) j).comp
      (measurePreserving_snd (μ := Measure.pi (fun _ : Fin n ↦ Λ))
        (ν := Measure.pi (fun _ : Fin n ↦ Λ)))).quasiMeasurePreserving.ae hZ)
  have hbound (x y : DyadicUnitCube q × ℝ) : cost x y ≤ C := by
    have hd := dyadicCube_dist_le_one x.1 y.1
    have hsq : ‖dyadicCubePoint x.1-dyadicCubePoint y.1‖^2 ≤ 1 := by nlinarith [norm_nonneg (dyadicCubePoint x.1-dyadicCubePoint y.1)]
    exact (hquadratic x y).trans ((mul_le_mul_of_nonneg_left hsq hC).trans_eq (mul_one C))
  obtain ⟨hVI,hV⟩ := originalShapeHole_integral_legalMaximumValue_le_of_tagged_iid hq P L xs ys hx hy hxi hyi hxl hyl hxy
    bins hgap (fun i ω ↦ (readS (ω.1 i)).2) (fun j ω ↦ (readT (ω.2 j)).2) (by fun_prop) (by fun_prop)
    (by filter_upwards [hzS] with ω hω; exact fun i ↦ (hω i).1)
    (by
      filter_upwards [hzS,hzT] with ω hωS hωT
      intro i j
      simpa only [readS,readT,Function.comp_apply,Real.dist_eq,abs_sub_comm] using hsep.separated _ (hωS i).2.2.2.1 _ (hωT j).2.2.2.2)
    (by
      filter_upwards [hzS] with ω hω
      intro i j he
      exact originalShapeHole_forward_of_same_target_label bins hgap (hω i).2.1 (hω i).2.2.1 he)
    (fun ω i j ↦ cost (readS (ω.1 i)) (readT (ω.2 j)))
    (fun i j ↦ hc.comp (((hs.comp ((measurable_pi_apply i).comp measurable_fst))).prodMk
      (ht.comp ((measurable_pi_apply j).comp measurable_snd)))) hC hC
    (Filter.Eventually.of_forall (fun ω i j ↦ hcn _ _)) (Filter.Eventually.of_forall (fun ω i j ↦ hbound _ _))
    (fun _ ↦ Filter.Eventually.of_forall (fun ω i j _ _ ↦ hquadratic _ _))
  have hmapS : Λ.map readS = space.prod α := by
    change (space.prod π).map (Prod.map id Prod.fst) = _
    rw [← Measure.map_prod_map space π measurable_id measurable_fst,Measure.map_id,hπ.1]
  have hmapT : Λ.map readT = space.prod β := by
    change (space.prod π).map (Prod.map id Prod.snd) = _
    rw [← Measure.map_prod_map space π measurable_id measurable_snd,Measure.map_id,hπ.2]
  let read := fun ω : (Fin n → Z) × (Fin n → Z) ↦
    ((fun i ↦ readS (ω.1 i)),fun j ↦ readT (ω.2 j))
  have hmread : Measurable read := by fun_prop
  have hread : MeasurePreserving read P (originalShapeHoleIIDLaw space α β n) := by
    refine ⟨hmread,?_⟩
    simpa only [hmapS,hmapT,originalShapeHoleIIDLaw] using
      originalShapeHole_map_two_iid_arrays Λ n readS readT hs ht
  have : IsProbabilityMeasure (originalShapeHoleIIDLaw space α β n) := by
    unfold originalShapeHoleIIDLaw
    infer_instance
  have hvm : Measurable (originalShapeHoleIIDValue cost (q := q) (n := n)) := by
    unfold originalShapeHoleIIDValue
    apply PartialMatching.measurable_legalMaximumValue _
      (measurableSet_scalarClockLegalGraph_eq
        (fun (i : Fin n) (sample : (Fin n → DyadicUnitCube q × ℝ) × (Fin n → DyadicUnitCube q × ℝ)) ↦ (sample.1 i).2)
        (fun (j : Fin n) (sample : (Fin n → DyadicUnitCube q × ℝ) × (Fin n → DyadicUnitCube q × ℝ)) ↦ (sample.2 j).2)
        (by fun_prop) (by fun_prop))
      (fun sample i j ↦ cost (sample.1 i) (sample.2 j))
    intro i j
    exact hc.comp (show Measurable (fun sample : (Fin n → DyadicUnitCube q × ℝ) × (Fin n → DyadicUnitCube q × ℝ) ↦ (sample.1 i,sample.2 j)) by fun_prop)
  have hrawI : Integrable (originalShapeHoleIIDValue cost (q := q) (n := n)) (originalShapeHoleIIDLaw space α β n) := by
    apply Integrable.of_bound hvm.aestronglyMeasurable ((n : ℝ)*C)
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    simpa only [originalShapeHoleIIDValue,min_self] using
      PartialMatching.abs_legalMaximumValue_le_min
        (scalarClockLegalGraph (fun i ↦ (ω.1 i).2) (fun j ↦ (ω.2 j).2))
        (fun i j ↦ cost (ω.1 i) (ω.2 j)) hC
        (fun i j ↦ by rw [abs_of_nonneg (hcn _ _)]; exact hbound _ _)
  refine ⟨hrawI,?_⟩
  have he := hread.hasLaw.integral_comp hvm.aestronglyMeasurable
  rw [← he]
  simpa only [Function.comp_apply,originalShapeHoleIIDValue,read,readS,readT,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hV

end OTSelector.Reconstruction
