import OTSelector.Reconstruction.FinslerConcreteUpperClassPressure

/-! The literal common spatial and pair-class law, with exact color projections
and optional finite spatial types. No selected endpoints are assigned a new iid law. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {X I J C : Type*} [MeasurableSpace X]
  [Fintype I] [Fintype J] [MeasurableSpace I] [MeasurableSpace J]
  [MeasurableSingletonClass I] [MeasurableSingletonClass J]

/-- Source observation of a genuine spatial and paired-class point. -/
def pairedClassObservationSource (z : X × (I × J)) : X × I := (z.1, z.2.1)

/-- Target observation of the same spatial and paired-class point. -/
def pairedClassObservationTarget (z : X × (I × J)) : X × J := (z.1, z.2.2)

theorem measurable_pairedClassObservationSource :
    Measurable (pairedClassObservationSource (X := X) (I := I) (J := J)) := by
  exact measurable_fst.prodMk (measurable_fst.comp measurable_snd)

theorem measurable_pairedClassObservationTarget :
    Measurable (pairedClassObservationTarget (X := X) (I := I) (J := J)) := by
  exact measurable_fst.prodMk (measurable_snd.comp measurable_snd)

/-- Spatial independence preserves the actual source class marginal. -/
theorem pairedClassObservationSource_map (μ : Measure X) (π : Measure (I × J))
    [SFinite μ] [SFinite π] :
    (μ.prod π).map pairedClassObservationSource = μ.prod (π.map Prod.fst) := by
  change (μ.prod π).map (Prod.map id Prod.fst) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_fst, Measure.map_id]

/-- Spatial independence preserves the actual target class marginal. -/
theorem pairedClassObservationTarget_map (μ : Measure X) (π : Measure (I × J))
    [SFinite μ] [SFinite π] :
    (μ.prod π).map pairedClassObservationTarget = μ.prod (π.map Prod.snd) := by
  change (μ.prod π).map (Prod.map id Prod.snd) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id]

/-- A spatial optional type retains both literal class indices when active. -/
def pairedClassTag (θ : X → Option C) (z : X × (I × J)) : Option (C × (I × J)) :=
  (θ z.1).map (fun c ↦ (c, z.2))

variable [Fintype C] [MeasurableSpace (Option C)]
  [MeasurableSingletonClass (Option C)]
  [MeasurableSpace (Option (C × (I × J)))]
  [MeasurableSingletonClass (Option (C × (I × J)))]

theorem measurable_pairedClassTag {θ : X → Option C} (hθ : Measurable θ) :
    Measurable (pairedClassTag (I := I) (J := J) θ) := by
  let attach : Option C × (I × J) → Option (C × (I × J)) :=
    fun p ↦ p.1.map (fun c ↦ (c, p.2))
  exact (measurable_of_countable attach).comp
    ((hθ.comp measurable_fst).prodMk measurable_snd)

@[simp]
theorem pairedClassTag_isSome (θ : X → Option C) (z : X × (I × J)) :
    (pairedClassTag θ z).isSome = (θ z.1).isSome := by
  cases h : θ z.1 <;> simp [pairedClassTag, h]

/-- Both colors use this single finite type law after the unused class index
is retained in the latent point. -/
theorem pairedClassTag_map (μ : Measure X) (π : Measure (I × J))
    [SFinite μ] [SFinite π] {θ : X → Option C} (hθ : Measurable θ) :
    (μ.prod π).map (pairedClassTag θ) =
      ((μ.map θ).prod π).map (fun p ↦ p.1.map (fun c ↦ (c, p.2))) := by
  let attach : Option C × (I × J) → Option (C × (I × J)) :=
    fun p ↦ p.1.map (fun c ↦ (c, p.2))
  have hprod : (μ.prod π).map (Prod.map θ id) = (μ.map θ).prod π := by
    rw [← Measure.map_prod_map _ _ hθ measurable_id, Measure.map_id]
  rw [← hprod, Measure.map_map (measurable_of_countable attach)
    (hθ.prodMap measurable_id)]
  rfl

/-- Only active spatial labels and the two original class indices are counted. -/
theorem pairedClassTag_type_card :
    Fintype.card (C × (I × J)) = Fintype.card C * Fintype.card I * Fintype.card J := by
  simp [Nat.mul_assoc]

/-- A literal joint type fiber is a spatial fiber times its actual class atom. -/
theorem pairedClassTag_real_fiber (μ : Measure X) (π : Measure (I × J))
    [SFinite μ] [SFinite π] (θ : X → Option C) (c : C) (p : I × J) :
    (μ.prod π).real (pairedClassTag θ ⁻¹' {some (c, p)}) =
      μ.real (θ ⁻¹' {some c}) * π.real {p} := by
  have heq : pairedClassTag (I := I) (J := J) θ ⁻¹' {some (c, p)} =
      (θ ⁻¹' {some c}) ×ˢ {p} := by
    ext z
    cases h : θ z.1 <;> simp [pairedClassTag, h]
  rw [heq, measureReal_prod_prod]

/-- The finite sum of active optional fibers is precisely the active mass. -/
theorem sum_optional_real_fibers (μ : Measure X) [IsFiniteMeasure μ]
    {θ : X → Option C} (hθ : Measurable θ) :
    (∑ c : C, μ.real (θ ⁻¹' {some c})) = μ.real {x | (θ x).isSome} := by
  have heq : {x | (θ x).isSome} = ⋃ c : C, θ ⁻¹' {some c} := by
    ext x
    cases h : θ x <;> simp [h]
  rw [heq, measureReal_iUnion_fintype]
  · intro c d hcd
    apply disjoint_left.mpr
    intro x hx hy
    apply hcd
    exact Option.some.inj (hx.symm.trans hy)
  · intro c
    exact (measurableSet_singleton _).preimage hθ

/-- Paired classes do not change the total active spatial mass. -/
theorem pairedClassTag_total_some_mass (μ : Measure X) [IsFiniteMeasure μ]
    (π : Measure (I × J)) [IsProbabilityMeasure π]
    {θ : X → Option C} (hθ : Measurable θ) :
    (∑ a : C × (I × J), (μ.prod π).real (pairedClassTag θ ⁻¹' {some a})) =
      μ.real {x | (θ x).isSome} := by
  rw [Fintype.sum_prod_type]
  simp_rw [pairedClassTag_real_fiber]
  have hπ : (∑ p : I × J, π.real {p}) = 1 := by
    simp
  simp_rw [← Finset.mul_sum, hπ, mul_one]
  exact sum_optional_real_fibers μ hθ

/-- The original fixed class weights give a common probability model whose
observations have the actual two class marginals, and whose finite optional
spatial types are legal and retain exactly their original spatial active mass. -/
theorem exists_pairedClass_spatial_type_law
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P₀ : I → J → ℝ) (hP₀ : ∀ i j, 0 ≤ P₀ i j)
    (hmass : 0 < ∑ i, ∑ j, P₀ i j)
    (allowed : I → J → Prop) (hzero : ∀ i j, ¬allowed i j → P₀ i j = 0)
    {θ : X → Option C} (hθ : Measurable θ) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    ∃ ρ : Measure (X × (I × J)), IsProbabilityMeasure ρ ∧
      ρ.map pairedClassObservationSource = μ.prod (α : Measure I) ∧
      ρ.map pairedClassObservationTarget = μ.prod (β : Measure J) ∧
      (∀ᵐ z ∂ρ, allowed z.2.1 z.2.2) ∧
      Measurable (pairedClassTag (I := I) (J := J) θ) ∧
      (∀ c : C, ∀ p : I × J,
        ρ.real (pairedClassTag θ ⁻¹' {some (c, p)}) =
          μ.real (θ ⁻¹' {some c}) * (P₀ p.1 p.2 / (∑ i, ∑ j, P₀ i j))) ∧
      (∑ a : C × (I × J), ρ.real (pairedClassTag θ ⁻¹' {some a})) =
        μ.real {x | (θ x).isSome} := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let ρ := μ.prod (π : Measure (I × J))
  refine ⟨ρ, inferInstance, pairedClassObservationSource_map μ _,
    pairedClassObservationTarget_map μ _, ?_, measurable_pairedClassTag hθ, ?_,
    pairedClassTag_total_some_mass μ _ hθ⟩
  · have hlegal : ∀ᵐ p ∂(π : Measure (I × J)), allowed p.1 p.2 :=
      normalizedClockClassPairMeasure_legal P₀ allowed hzero
    have hlegalSet : MeasurableSet {p : I × J | allowed p.1 p.2} :=
      (Set.to_countable _).measurableSet
    apply (Measure.ae_prod_iff_ae_ae (hlegalSet.preimage measurable_snd)).mpr
    exact Filter.Eventually.of_forall fun _ ↦ hlegal
  · intro c p
    rw [pairedClassTag_real_fiber]
    exact congrArg (fun r : ℝ ↦ μ.real (θ ⁻¹' {some c}) * r)
      (normalizedClockClassPairMeasure_real_singleton P₀ hP₀ p.1 p.2)

end OTSelector.Reconstruction
