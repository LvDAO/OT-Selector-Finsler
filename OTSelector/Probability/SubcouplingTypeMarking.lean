import LeanPool.Vlasov.OT.Coupling
import OTSelector.Probability.RadonNikodymMarking
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationTypedRecovery.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationTypedRecovery`; the selected original proof blocks follow. -/
section

/-!
# Probability.SubcouplingTypeMarking

## Lemma skeleton

* **Conditions:** A finite family of subcoupling components whose sum is dominated by a paired law; finite actual marginals and measurable common labels where specified.
* **Objects:** Completed residual type components, exact marginal/type masses, common conditional labels and iid physical/assignment laws.
* **Proof detail:** Add the measure difference as a None tag, project each component, use RN marked-law recovery and positive-type conditional normalization, then take finite products.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf): Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14): Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set.

Source relation (composition): Finite typed decomposition/marking assembly preserving residual mass. Named finite-measure instances register actual dominated marginals, rather than extra axioms.
-/

/-!
# Original subcouplings produce two-color iid type laws

Finite subcouplings of the original population coupling determine both marginal
RN marking kernels. Each type has the same original mass in both colors. If the
original coupling preserves its actual root label, each positive-mass type has
the same normalized label law as well. The unused original mass remains a type.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The original deterministic pairing mass retained in finitely many types. -/
structure PopulationSubcouplingTypes {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (π : Measure (X × Y)) (T : Type*) [Fintype T] where
  component : T → Measure (X × Y)
  dominated : ∑ t, component t ≤ π

namespace PopulationSubcouplingTypes
variable {X Y Z T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z] [Fintype T] {π : Measure (X × Y)}
  (D : PopulationSubcouplingTypes π T)

/-- Every original type is dominated by the unchanged original coupling. -/
theorem component_le (t : T) : D.component t ≤ π :=
  (Finset.single_le_sum (fun _ _ ↦ Measure.zero_le _) (Finset.mem_univ t)).trans D.dominated

instance component_isFinite [IsFiniteMeasure π] (t : T) : IsFiniteMeasure (D.component t) :=
  isFiniteMeasure_of_le π (D.component_le t)

/-- The actual physical source and target subpopulations of each type. -/
def source (t : T) : Measure X := (D.component t).map Prod.fst

def target (t : T) : Measure Y := (D.component t).map Prod.snd

instance source_isFinite [IsFiniteMeasure π] (t : T) : IsFiniteMeasure (D.source t) := by
  unfold source
  infer_instance

instance target_isFinite [IsFiniteMeasure π] (t : T) : IsFiniteMeasure (D.target t) := by
  unfold target
  infer_instance

/-- The actual unused pairing is the residual type, with no new matching choice. -/
def completed (tag : Option T) : Measure (X × Y) :=
  finiteRNMarkComponent π D.component tag

instance completed_isFinite [IsFiniteMeasure π] (tag : Option T) :
    IsFiniteMeasure (D.completed tag) := by
  cases tag <;> unfold completed finiteRNMarkComponent <;> infer_instance

theorem completed_le (tag : Option T) : D.completed tag ≤ π := by
  cases tag with
  | none => exact Measure.sub_le
  | some t => exact D.component_le t

/-- Pushforward respects a dominated finite measure difference. -/
theorem map_sub_of_le {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (ρ σ : Measure A) [IsFiniteMeasure σ] (h : σ ≤ ρ)
    (f : A → B) (hf : Measurable f) :
    (ρ - σ).map f = ρ.map f - σ.map f := by
  ext U hU
  rw [Measure.map_apply hf hU, Measure.sub_apply (hf hU) h,
    Measure.sub_apply hU (Measure.map_mono h hf),
    Measure.map_apply hf hU, Measure.map_apply hf hU]

/-- Both original type families are dominated by their original physical marginals. -/
theorem marginal_domination {μ : Measure X} {ν : Measure Y}
    (hπ : Vlasov.IsCoupling π μ ν) :
    (∑ t, D.source t) ≤ μ ∧ (∑ t, D.target t) ≤ ν := by
  constructor
  · simpa only [Measure.map_finset_sum' measurable_fst.aemeasurable, hπ.1, source]
      using Measure.map_mono D.dominated measurable_fst
  · simpa only [Measure.map_finset_sum' measurable_snd.aemeasurable, hπ.2, target]
      using Measure.map_mono D.dominated measurable_snd

/-- Completing the marginal types agrees with taking the actual residual
pairing's physical marginals. -/
theorem completed_marginals [IsFiniteMeasure π] {μ : Measure X} {ν : Measure Y}
    (hπ : Vlasov.IsCoupling π μ ν) (tag : Option T) :
    (D.completed tag).map Prod.fst = finiteRNMarkComponent μ D.source tag ∧
    (D.completed tag).map Prod.snd = finiteRNMarkComponent ν D.target tag := by
  cases tag with
  | some t => exact ⟨rfl, rfl⟩
  | none =>
    constructor
    · simp only [completed, finiteRNMarkComponent,
        map_sub_of_le π _ D.dominated Prod.fst measurable_fst,
        Measure.map_finset_sum' measurable_fst.aemeasurable, hπ.1, source]
    · simp only [completed, finiteRNMarkComponent,
        map_sub_of_le π _ D.dominated Prod.snd measurable_snd,
        Measure.map_finset_sum' measurable_snd.aemeasurable, hπ.2, target]

/-- Every type, including unused mass, has the same actual mass in both colors. -/
theorem common_type_mass [IsFiniteMeasure π] {μ : Measure X} {ν : Measure Y}
    (hπ : Vlasov.IsCoupling π μ ν) (tag : Option T) :
    finiteRNMarkComponent μ D.source tag univ = D.completed tag univ ∧
    finiteRNMarkComponent ν D.target tag univ = D.completed tag univ := by
  obtain ⟨hleft, hright⟩ := D.completed_marginals hπ tag
  constructor
  · rw [← hleft, Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
  · rw [← hright, Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ]

/-- An actual root-preserving original coupling gives the same raw label law in
every source and target type, including the unused original component. -/
theorem common_type_label [IsFiniteMeasure π] {μ : Measure X} {ν : Measure Y}
    (hπ : Vlasov.IsCoupling π μ ν) (a : X → Z) (b : Y → Z)
    (ha : Measurable a) (hb : Measurable b)
    (hroot : ∀ᵐ p ∂π, a p.1 = b p.2) (tag : Option T) :
    (finiteRNMarkComponent μ D.source tag).map a =
      (finiteRNMarkComponent ν D.target tag).map b := by
  obtain ⟨hleft, hright⟩ := D.completed_marginals hπ tag
  rw [← hleft, ← hright, Measure.map_map ha measurable_fst,
    Measure.map_map hb measurable_snd]
  exact Measure.map_congr (ae_mono (D.completed_le tag) hroot)

section Marked
variable [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
  [IsFiniteMeasure π] {μ : Measure X} {ν : Measure Y}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The two original physical populations with their produced RN type marks. -/
def sourceMarkedLaw (μ : Measure X) : Measure (X × Option T) :=
  finiteRNMarkLaw μ D.source

def targetMarkedLaw (ν : Measure Y) : Measure (Y × Option T) :=
  finiteRNMarkLaw ν D.target

instance sourceMarkedLaw_isFinite : IsFiniteMeasure (D.sourceMarkedLaw μ) := by
  unfold sourceMarkedLaw
  infer_instance

instance targetMarkedLaw_isFinite : IsFiniteMeasure (D.targetMarkedLaw ν) := by
  unfold targetMarkedLaw
  infer_instance

omit [MeasurableSingletonClass (Option T)] in
/-- Forgetting the types recovers both original physical laws exactly. -/
theorem marked_physical_laws (hπ : Vlasov.IsCoupling π μ ν) :
    (D.sourceMarkedLaw μ).map Prod.fst = μ ∧
      (D.targetMarkedLaw ν).map Prod.fst = ν := by
  obtain ⟨hsource, htarget⟩ := D.marginal_domination hπ
  exact ⟨finiteRNMarkLaw_map_fst μ D.source hsource,
    finiteRNMarkLaw_map_fst ν D.target htarget⟩

/-- The two independently marked physical populations have the same type law. -/
theorem common_marked_type_law (hπ : Vlasov.IsCoupling π μ ν) :
    (D.sourceMarkedLaw μ).map Prod.snd = (D.targetMarkedLaw ν).map Prod.snd := by
  apply Measure.ext_of_singleton
  intro tag
  rw [sourceMarkedLaw, targetMarkedLaw, finiteRNMarkLaw_type_mass,
    finiteRNMarkLaw_type_mass, (D.common_type_mass hπ tag).1,
    (D.common_type_mass hπ tag).2]

/-- Each positive-mass type has the same original conditional label law in both
colors, normalized only when taking this conditional distribution. -/
theorem common_conditional_label [StandardBorelSpace Z] [Nonempty Z]
    (hπ : Vlasov.IsCoupling π μ ν) (a : X → Z) (b : Y → Z)
    (ha : Measurable a) (hb : Measurable b)
    (hroot : ∀ᵐ p ∂π, a p.1 = b p.2) (tag : Option T)
    (htag : D.completed tag univ ≠ 0) :
    condDistrib (fun p : X × Option T ↦ a p.1) Prod.snd (D.sourceMarkedLaw μ) tag =
        (D.completed tag univ)⁻¹ • (D.completed tag).map (fun p ↦ a p.1) ∧
    condDistrib (fun p : Y × Option T ↦ b p.1) Prod.snd (D.targetMarkedLaw ν) tag =
        (D.completed tag univ)⁻¹ • (D.completed tag).map (fun p ↦ a p.1) := by
  obtain ⟨hleft, hright⟩ := D.completed_marginals hπ tag
  obtain ⟨hleftmass, hrightmass⟩ := D.common_type_mass hπ tag
  constructor
  · change condDistrib (fun p : X × Option T ↦ a p.1) Prod.snd
        (finiteRNMarkLaw μ D.source) tag = _
    rw [finiteRNMarkLaw_condDistrib_label μ D.source a ha tag
      (hleftmass.trans_ne htag), hleftmass, ← hleft, Measure.map_map ha measurable_fst]
    rfl
  · change condDistrib (fun p : Y × Option T ↦ b p.1) Prod.snd
        (finiteRNMarkLaw ν D.target) tag = _
    rw [finiteRNMarkLaw_condDistrib_label ν D.target b hb tag
      (hrightmass.trans_ne htag), hrightmass,
      ← D.common_type_label hπ a b ha hb hroot tag,
      ← hleft, Measure.map_map ha measurable_fst]
    rfl

omit [MeasurableSingletonClass (Option T)] in
/-- The two independent marked iid arrays project to the unchanged original
independent physical arrays. -/
theorem iid_physical_law {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν) :
    ((Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν))).map
        (Prod.map (fun x i ↦ (x i).1) (fun y j ↦ (y j).1)) =
      (Measure.pi (fun _ : I ↦ μ)).prod (Measure.pi (fun _ : J ↦ ν)) := by
  obtain ⟨hsource, htarget⟩ := D.marginal_domination hπ
  rw [← Measure.map_prod_map _ _ (show Measurable (fun x : I → X × Option T ↦ fun i ↦ (x i).1) from by fun_prop)
    (show Measurable (fun y : J → Y × Option T ↦ fun j ↦ (y j).1) from by fun_prop)]
  rw [sourceMarkedLaw, targetMarkedLaw,
    finiteRNMarkLaw_iid_map_fst μ D.source hsource,
    finiteRNMarkLaw_iid_map_fst ν D.target htarget]

/-- Arbitrary source and target type assignments retain their exact raw
component product laws. Their realized type counts need not agree. -/
theorem iid_assignment_law {I J : Type*} [Fintype I] [Fintype J]
    (sourceAssignment : I → Option T) (targetAssignment : J → Option T) :
    (((Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν))).restrict
        ((univ.pi (fun i ↦ Prod.snd ⁻¹' {sourceAssignment i})) ×ˢ
          (univ.pi (fun j ↦ Prod.snd ⁻¹' {targetAssignment j})))).map
        (Prod.map (fun x i ↦ (x i).1) (fun y j ↦ (y j).1)) =
      (Measure.pi (fun i ↦ finiteRNMarkComponent μ D.source (sourceAssignment i))).prod
        (Measure.pi (fun j ↦ finiteRNMarkComponent ν D.target (targetAssignment j))) := by
  rw [← Measure.prod_restrict,
    ← Measure.map_prod_map _ _ (show Measurable (fun x : I → X × Option T ↦ fun i ↦ (x i).1) from by fun_prop)
    (show Measurable (fun y : J → Y × Option T ↦ fun j ↦ (y j).1) from by fun_prop)]
  rw [sourceMarkedLaw, targetMarkedLaw,
    finiteRNMarkLaw_iid_restrict_assignment, finiteRNMarkLaw_iid_restrict_assignment]

/-- The probability weights of arbitrary type attributions use the same original
type masses for both colors. -/
theorem iid_assignment_mass {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν)
    (sourceAssignment : I → Option T) (targetAssignment : J → Option T) :
    ((Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν)))
        ((univ.pi (fun i ↦ Prod.snd ⁻¹' {sourceAssignment i})) ×ˢ
          (univ.pi (fun j ↦ Prod.snd ⁻¹' {targetAssignment j}))) =
      (∏ i, D.completed (sourceAssignment i) univ) *
        ∏ j, D.completed (targetAssignment j) univ := by
  rw [Measure.prod_prod, sourceMarkedLaw, targetMarkedLaw,
    finiteRNMarkLaw_iid_assignment_mass, finiteRNMarkLaw_iid_assignment_mass]
  simp only [(D.common_type_mass hπ _).1, (D.common_type_mass hπ _).2]

end Marked

end PopulationSubcouplingTypes
end OTSelector.Reconstruction

end
end
