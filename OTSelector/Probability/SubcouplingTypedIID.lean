import OTSelector.Probability.RadonNikodymMarking
import OTSelector.Probability.SubcouplingTypeMarking
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationTypedIID.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationTypedIID`; the selected original proof blocks follow. -/
section

/-!
# Probability.SubcouplingTypedIID

## Lemma skeleton

* **Conditions:** Finite typed subcoupling decomposition with RN marking, finite iid sample index sets and strictly positive type masses for conditional normalization.
* **Objects:** Exact physical/type iid laws, type probabilities, raw assignment restrictions and independent conditional label products, including the residual tag.
* **Proof detail:** Compute tagged rectangle restrictions and type singleton masses, take finite products, normalize by the product of positive assignment masses and identify the common component label law.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14): Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set.

Source relation (composition): Actual marked product-law assembly. Named finite-measure instances are adapters and zero-type assignments are not normalized.
-/

/-!
# Independent type marks and conditional label products

The RN extension preserves the original two-color iid law. Its type arrays have
one common iid law, and every positive-mass type assignment gives independent
labels with the original normalized component label laws. All identities are
proved from the raw type restrictions, including the residual original type.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

instance finiteRNMarkComponent_isFinite {X T : Type*} [MeasurableSpace X] [Fintype T]
    (μ : Measure X) [IsFiniteMeasure μ] (m : T → Measure X)
    [∀ t, IsFiniteMeasure (m t)] (tag : Option T) :
    IsFiniteMeasure (finiteRNMarkComponent μ m tag) := by
  cases tag <;> unfold finiteRNMarkComponent <;> infer_instance

/-- Normalizing a finite product of positive finite component measures preserves
its independent product structure. -/
theorem pi_normalized_component_laws {I : Type*} [Fintype I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (ρ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (ρ i)]
    (hρ : ∀ i, ρ i univ ≠ 0) :
    (∏ i, ρ i univ)⁻¹ • Measure.pi ρ =
      Measure.pi (fun i ↦ (ρ i univ)⁻¹ • ρ i) := by
  let (i : I) : IsFiniteMeasure ((ρ i univ)⁻¹ • ρ i) :=
    (ρ i).smul_finite (ENNReal.inv_ne_top.mpr (hρ i))
  apply (Measure.pi_eq (fun s _ ↦ ?_)).symm
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi,
    ENNReal.prod_inv_distrib (fun i _ _ _ _ ↦ Or.inl (hρ i))]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- The raw labels of a prescribed assignment retain the product of the original
component label measures, allowing a different coordinate map at every index. -/
theorem finiteRNMarkLaw_iid_restrict_label_assignment
    {X T I : Type*} [MeasurableSpace X] [Fintype T] [Fintype I]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    {Z : I → Type*} [∀ i, MeasurableSpace (Z i)]
    (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)]
    (assignment : I → Option T) (a : ∀ i, X → Z i) (ha : ∀ i, Measurable (a i)) :
    ((Measure.pi (fun _ : I ↦ finiteRNMarkLaw μ m)).restrict
      (univ.pi (fun i ↦ Prod.snd ⁻¹' {assignment i}))).map
        (fun x i ↦ a i (x i).1) =
      Measure.pi (fun i ↦ (finiteRNMarkComponent μ m (assignment i)).map (a i)) := by
  rw [Measure.restrict_pi_pi, Measure.pi_map_pi (fun i ↦
    (show Measurable (fun p : X × Option T ↦ a i p.1) from
      (ha i).comp measurable_fst).aemeasurable)]
  congr 1
  funext i
  change ((finiteRNMarkLaw μ m).restrict (Prod.snd ⁻¹' {assignment i})).map
    (a i ∘ Prod.fst) = _
  rw [← Measure.map_map (ha i) measurable_fst,
    finiteRNMarkLaw_restrict_type_map_fst]

/-- Conditional on any positive-mass assignment, the labels are independent with
the normalized original component laws. -/
theorem finiteRNMarkLaw_iid_normalized_label_assignment
    {X T I : Type*} [MeasurableSpace X] [Fintype T] [Fintype I]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    {Z : I → Type*} [∀ i, MeasurableSpace (Z i)]
    (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)]
    (assignment : I → Option T) (a : ∀ i, X → Z i) (ha : ∀ i, Measurable (a i))
    (hpos : ∀ i, finiteRNMarkComponent μ m (assignment i) univ ≠ 0) :
    let P := Measure.pi (fun _ : I ↦ finiteRNMarkLaw μ m)
    let E := univ.pi (fun i ↦ Prod.snd ⁻¹' {assignment i})
    ((P E)⁻¹ • P.restrict E).map (fun x i ↦ a i (x i).1) =
      Measure.pi (fun i ↦ (finiteRNMarkComponent μ m (assignment i) univ)⁻¹ •
        (finiteRNMarkComponent μ m (assignment i)).map (a i)) := by
  dsimp only
  rw [Measure.map_smul, finiteRNMarkLaw_iid_restrict_label_assignment μ m assignment a ha,
    finiteRNMarkLaw_iid_assignment_mass]
  have hm (i : I) : ((finiteRNMarkComponent μ m (assignment i)).map (a i)) univ =
      finiteRNMarkComponent μ m (assignment i) univ :=
    Measure.map_apply (ha i) MeasurableSet.univ
  simpa only [hm] using pi_normalized_component_laws
    (fun i ↦ (finiteRNMarkComponent μ m (assignment i)).map (a i))
      (fun i ↦ (hm i).trans_ne (hpos i))

namespace PopulationSubcouplingTypes
variable {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Fintype T]
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  {π : Measure (X × Y)} [IsFiniteMeasure π]
  (D : PopulationSubcouplingTypes π T)
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The common type distribution retains all original pairing masses. -/
def typeLaw : Measure (Option T) := (finiteRNMarkLaw π D.component).map Prod.snd

theorem typeLaw_singleton (tag : Option T) : D.typeLaw {tag} = D.completed tag univ :=
  finiteRNMarkLaw_type_mass π D.component tag

instance typeLaw_isFinite : IsFiniteMeasure D.typeLaw := by
  unfold typeLaw
  infer_instance

/-- Both RN extensions produce the common original type distribution. -/
theorem marked_type_laws (hπ : Vlasov.IsCoupling π μ ν) :
    (D.sourceMarkedLaw μ).map Prod.snd = D.typeLaw ∧
      (D.targetMarkedLaw ν).map Prod.snd = D.typeLaw := by
  constructor <;> apply Measure.ext_of_singleton <;> intro tag
  · rw [sourceMarkedLaw, finiteRNMarkLaw_type_mass, D.typeLaw_singleton,
      (D.common_type_mass hπ tag).1]
  · rw [targetMarkedLaw, finiteRNMarkLaw_type_mass, D.typeLaw_singleton,
      (D.common_type_mass hπ tag).2]

/-- The type arrays are independent iid samples from the same original type law,
with no constraint on their realized counts. -/
theorem iid_type_law {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν) :
    ((Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν))).map
        (Prod.map (fun x i ↦ (x i).2) (fun y j ↦ (y j).2)) =
      (Measure.pi (fun _ : I ↦ D.typeLaw)).prod (Measure.pi (fun _ : J ↦ D.typeLaw)) := by
  rw [← Measure.map_prod_map _ _
    (show Measurable (fun x : I → X × Option T ↦ fun i ↦ (x i).2) from by fun_prop)
    (show Measurable (fun y : J → Y × Option T ↦ fun j ↦ (y j).2) from by fun_prop),
    Measure.pi_map_pi (fun _ ↦ measurable_snd.aemeasurable),
    Measure.pi_map_pi (fun _ ↦ measurable_snd.aemeasurable)]
  simp only [(D.marked_type_laws hπ).1, (D.marked_type_laws hπ).2]

/-- The actual RN kernels produce the prescribed two-color marked laws. -/
theorem rn_marking_laws (hπ : Vlasov.IsCoupling π μ ν) :
    μ ⊗ₘ finiteRNMarkKernel μ D.source = D.sourceMarkedLaw μ ∧
      ν ⊗ₘ finiteRNMarkKernel ν D.target = D.targetMarkedLaw ν :=
  ⟨compProd_finiteRNMarkKernel μ D.source (D.marginal_domination hπ).1,
    compProd_finiteRNMarkKernel ν D.target (D.marginal_domination hπ).2⟩

/-- One full-measure set in each original population carries the exact RN
probabilities of every retained or residual type simultaneously. -/
theorem rn_type_probabilities (hπ : Vlasov.IsCoupling π μ ν) :
    (∀ᵐ x ∂μ, ∀ tag, finiteRNMarkKernel μ D.source x {tag} =
      (finiteRNMarkComponent μ D.source tag).rnDeriv μ x) ∧
    (∀ᵐ y ∂ν, ∀ tag, finiteRNMarkKernel ν D.target y {tag} =
      (finiteRNMarkComponent ν D.target tag).rnDeriv ν y) := by
  constructor
  · exact ae_all_iff.mpr fun tag ↦
      finiteRNMarkKernel_eq_rnDeriv μ D.source (D.marginal_domination hπ).1 tag
  · exact ae_all_iff.mpr fun tag ↦
      finiteRNMarkKernel_eq_rnDeriv ν D.target (D.marginal_domination hπ).2 tag

/-- The original probability populations generate probability marked laws and a
common probability type law. -/
theorem marked_probabilities [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling π μ ν) :
    IsProbabilityMeasure (D.sourceMarkedLaw μ) ∧
      IsProbabilityMeasure (D.targetMarkedLaw ν) ∧ IsProbabilityMeasure D.typeLaw := by
  have hs : IsProbabilityMeasure (D.sourceMarkedLaw μ) :=
    finiteRNMarkLaw_isProbability μ D.source (D.marginal_domination hπ).1
  have ht : IsProbabilityMeasure (D.targetMarkedLaw ν) :=
    finiteRNMarkLaw_isProbability ν D.target (D.marginal_domination hπ).2
  refine ⟨hs, ht, ?_⟩
  rw [← (D.marked_type_laws hπ).1]
  exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable

/-- Conditional on the same positive type attribution, both colors have
independent labels with the same normalized original type-label laws. Coordinate
maps may depend on the sample index and its assigned original chart. -/
theorem iid_normalized_label_laws {I : Type*} [Fintype I]
    {Z : I → Type*} [∀ i, MeasurableSpace (Z i)]
    (hπ : Vlasov.IsCoupling π μ ν) (assignment : I → Option T)
    (a : ∀ i, X → Z i) (b : ∀ i, Y → Z i)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (hroot : ∀ i, ∀ᵐ p ∂π, a i p.1 = b i p.2)
    (hpos : ∀ i, D.completed (assignment i) univ ≠ 0) :
    let Ps := Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)
    let Pt := Measure.pi (fun _ : I ↦ D.targetMarkedLaw ν)
    let Es := univ.pi (fun i ↦ Prod.snd ⁻¹' {assignment i})
    let Et := univ.pi (fun i ↦ Prod.snd ⁻¹' {assignment i})
    let L := Measure.pi (fun i ↦ (D.completed (assignment i) univ)⁻¹ •
      (D.completed (assignment i)).map (fun p ↦ a i p.1))
    ((Ps Es)⁻¹ • Ps.restrict Es).map (fun x i ↦ a i (x i).1) = L ∧
      ((Pt Et)⁻¹ • Pt.restrict Et).map (fun y i ↦ b i (y i).1) = L := by
  dsimp only
  constructor
  · rw [sourceMarkedLaw, finiteRNMarkLaw_iid_normalized_label_assignment
      μ D.source assignment a ha (fun i ↦
        ((D.common_type_mass hπ (assignment i)).1).trans_ne (hpos i))]
    congr 1
    funext i
    rw [(D.common_type_mass hπ (assignment i)).1,
      ← (D.completed_marginals hπ (assignment i)).1,
      Measure.map_map (ha i) measurable_fst]
    rfl
  · rw [targetMarkedLaw, finiteRNMarkLaw_iid_normalized_label_assignment
      ν D.target assignment b hb (fun i ↦
        ((D.common_type_mass hπ (assignment i)).2).trans_ne (hpos i))]
    congr 1
    funext i
    rw [(D.common_type_mass hπ (assignment i)).2,
      ← D.common_type_label hπ (a i) (b i) (ha i) (hb i) (hroot i) (assignment i),
      ← (D.completed_marginals hπ (assignment i)).1,
      Measure.map_map (ha i) measurable_fst]
    rfl

end PopulationSubcouplingTypes
end OTSelector.Reconstruction

end
end
