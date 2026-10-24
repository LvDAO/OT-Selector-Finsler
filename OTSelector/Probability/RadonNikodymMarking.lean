import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Radon Nikodym Marking

Conditions: Finite μ and finitely many finite component measures m_t; sum_t m_t ≤ μ when preservation of the base law or RN identification is asserted. Finite measurable tag space Option T records a residual none tag.

Objects: The marked extension, its actual conditional Markov kernel, RN type probabilities, raw component restrictions and iid assignment products, and normalized positive-mass tag conditionals.

Proof detail: Place each component on its tag graph and retain μ−sum m_t at none. Projecting away tags recovers μ. Disintegrate the marked law and identify tag-cell densities by RN uniqueness. Apply product-measure restriction identities for iid assignments and sum the finite disjoint assignment partition.

Relation to primary sources: This finite RN marking is a locally constructed specialization of kernel marking. Keeping none preserves the original law. Product restrictions and assignment masses are raw; normalization occurs only in the explicitly positive-mass tag conditional-distribution theorem. No Poisson-process conclusion is claimed.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF), Appendix A.4, Theorem A.4.8 and its uniqueness proof, p. 470. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=478
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
* Günter Last and Mathew Penrose, Lectures on the Poisson Process (2017 author manuscript), Section 5.2, Definition 5.3 and equations (5.5)–(5.6), pp. 40–41. https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=52
* Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF), Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56
* Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF), Section 4.1.1, Example 4.1.5, p. 208: conditional means on a measurable positive-probability partition cell. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=216
-/
/-!
# RN type marks preserving the original population laws

A finite dominated family of original component measures determines a Markov
marking kernel. Its conditional type probabilities are their Radon--Nikodym
densities. The unused original mass is retained as the extra `none` type.
Independent marks preserve the original iid sample law, while restrictions to
prescribed types retain the exact raw product masses.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {X T : Type*} [MeasurableSpace X] [Fintype T]
  [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]

/-- The original unused mass is the extra unmarked type. -/
def finiteRNMarkComponent (μ : Measure X) (m : T → Measure X) : Option T → Measure X
  | none => μ - ∑ t, m t
  | some t => m t

/-- The marked extension assigns the prescribed finite component measures to
their types and keeps all remaining original mass in the unmarked type. -/
def finiteRNMarkLaw (μ : Measure X) (m : T → Measure X) : Measure (X × Option T) :=
  (μ - ∑ t, m t).map (fun x ↦ (x, (none : Option T))) +
    ∑ t, (m t).map (fun x ↦ (x, some t))

instance finiteRNMarkLaw_isFinite (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] : IsFiniteMeasure (finiteRNMarkLaw μ m) := by
  unfold finiteRNMarkLaw
  infer_instance

omit [MeasurableSingletonClass (Option T)] in
/-- Forgetting the marks recovers the exact original physical law. -/
theorem finiteRNMarkLaw_map_fst (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] (hm : ∑ t, m t ≤ μ) :
    (finiteRNMarkLaw μ m).map Prod.fst = μ := by
  have he (ρ : Measure X) (s : Option T) :
      (ρ.map (fun x ↦ (x, s))).map Prod.fst = ρ := by
    rw [Measure.map_map measurable_fst (show Measurable (fun x : X ↦ (x, s)) from
      measurable_id.prodMk measurable_const)]
    exact Measure.map_id
  rw [finiteRNMarkLaw, Measure.map_add _ _ measurable_fst,
    Measure.map_finset_sum' measurable_fst.aemeasurable]
  simpa only [he] using Measure.sub_add_cancel_of_le hm

/-- The conditional type kernel is a genuine Markov kernel everywhere, and its
type probabilities agree with the original component RN densities almost everywhere. -/
def finiteRNMarkKernel (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] : Kernel X (Option T) :=
  condDistrib Prod.snd Prod.fst (finiteRNMarkLaw μ m)

instance finiteRNMarkKernel_isMarkov (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] :
    IsMarkovKernel (finiteRNMarkKernel μ m) := by
  unfold finiteRNMarkKernel
  infer_instance

/-- Independent marking via the produced kernel gives exactly the prescribed
component mixture while preserving the original base law. -/
theorem compProd_finiteRNMarkKernel (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] (hm : ∑ t, m t ≤ μ) :
    μ ⊗ₘ finiteRNMarkKernel μ m = finiteRNMarkLaw μ m := by
  have h := compProd_map_condDistrib
    (μ := finiteRNMarkLaw μ m) (mβ := ‹MeasurableSpace X›)
    (X := Prod.fst) measurable_snd.aemeasurable
  rw [finiteRNMarkLaw_map_fst μ m hm] at h
  exact h.trans Measure.map_id

/-- Restricting to a type recovers precisely its original component measure. -/
theorem finiteRNMarkLaw_apply_cell (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)]
    (tag : Option T) {A : Set X} (hA : MeasurableSet A) :
    finiteRNMarkLaw μ m (A ×ˢ {tag}) = finiteRNMarkComponent μ m tag A := by
  have he (ρ : Measure X) (s : Option T) :
      ρ.map (fun x ↦ (x, s)) (A ×ˢ {tag}) = if s = tag then ρ A else 0 := by
    rw [Measure.map_apply (show Measurable (fun x : X ↦ (x, s)) from
      measurable_id.prodMk measurable_const)
      (hA.prod (measurableSet_singleton tag))]
    by_cases h : s = tag <;> simp [h]
  rw [finiteRNMarkLaw, Measure.add_apply, Measure.finsetSum_apply]
  simp_rw [he]
  cases tag <;> simp [finiteRNMarkComponent]

/-- Each produced marking probability is exactly the RN density of its original
component, including the unmarked residual component. -/
theorem finiteRNMarkKernel_withDensity (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] (hm : ∑ t, m t ≤ μ)
    (tag : Option T) :
    μ.withDensity (fun x ↦ finiteRNMarkKernel μ m x {tag}) = finiteRNMarkComponent μ m tag := by
  ext A hA
  rw [withDensity_apply _ hA,
    ← Measure.compProd_apply_prod hA (measurableSet_singleton tag),
    compProd_finiteRNMarkKernel μ m hm, finiteRNMarkLaw_apply_cell μ m tag hA]

theorem finiteRNMarkKernel_eq_rnDeriv (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] (hm : ∑ t, m t ≤ μ)
    (tag : Option T) :
    (fun x ↦ finiteRNMarkKernel μ m x {tag}) =ᵐ[μ]
      (finiteRNMarkComponent μ m tag).rnDeriv μ := by
  apply Measure.eq_rnDeriv ((finiteRNMarkKernel μ m).measurable_coe (measurableSet_singleton tag))
    Measure.MutuallySingular.zero_left
  rw [zero_add, finiteRNMarkKernel_withDensity μ m hm tag]

/-- Each raw marked type has exactly its prescribed original mass. -/
theorem finiteRNMarkLaw_type_mass (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] (tag : Option T) :
    (finiteRNMarkLaw μ m).map Prod.snd {tag} = finiteRNMarkComponent μ m tag univ := by
  rw [Measure.map_apply measurable_snd (measurableSet_singleton tag)]
  simpa only [univ_prod] using finiteRNMarkLaw_apply_cell μ m tag MeasurableSet.univ

/-- The physical restriction of a marked type is the original component. -/
theorem finiteRNMarkLaw_restrict_type_map_fst (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] (tag : Option T) :
    ((finiteRNMarkLaw μ m).restrict (Prod.snd ⁻¹' {tag})).map Prod.fst =
      finiteRNMarkComponent μ m tag := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA,
    Measure.restrict_apply (measurable_fst hA)]
  exact finiteRNMarkLaw_apply_cell μ m tag hA

omit [MeasurableSingletonClass (Option T)] in
/-- A dominated marking of a probability law is itself a probability law. -/
theorem finiteRNMarkLaw_isProbability (μ : Measure X) [IsProbabilityMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] (hm : ∑ t, m t ≤ μ) :
    IsProbabilityMeasure (finiteRNMarkLaw μ m) := by
  apply (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mp
  rw [finiteRNMarkLaw_map_fst μ m hm]
  infer_instance

omit [MeasurableSingletonClass (Option T)] in
/-- Forgetting independently generated marks restores the complete original iid law. -/
theorem finiteRNMarkLaw_iid_map_fst {I : Type*} [Fintype I]
    (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] (hm : ∑ t, m t ≤ μ) :
    (Measure.pi (fun _ : I ↦ finiteRNMarkLaw μ m)).map (fun x i ↦ (x i).1) =
      Measure.pi (fun _ : I ↦ μ) := by
  rw [Measure.pi_map_pi (fun _ ↦ measurable_fst.aemeasurable)]
  simp only [finiteRNMarkLaw_map_fst μ m hm]

/-- A prescribed type for each sample yields the product of the original raw
component laws; its mass is retained, rather than normalized away. -/
theorem finiteRNMarkLaw_iid_restrict_assignment {I : Type*} [Fintype I]
    (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] (assignment : I → Option T) :
    ((Measure.pi (fun _ : I ↦ finiteRNMarkLaw μ m)).restrict
      (univ.pi (fun i ↦ Prod.snd ⁻¹' {assignment i}))).map (fun x i ↦ (x i).1) =
      Measure.pi (fun i ↦ finiteRNMarkComponent μ m (assignment i)) := by
  rw [Measure.restrict_pi_pi,
    Measure.pi_map_pi (fun _ ↦ measurable_fst.aemeasurable)]
  simp only [finiteRNMarkLaw_restrict_type_map_fst]

/-- At a positive-mass type, the original label conditional is precisely the
normalized label image of its prescribed component. -/
theorem finiteRNMarkLaw_condDistrib_label
    {Z : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
    (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)]
    (a : X → Z) (ha : Measurable a) (tag : Option T)
    (htag : finiteRNMarkComponent μ m tag univ ≠ 0) :
    condDistrib (fun p : X × Option T ↦ a p.1) Prod.snd (finiteRNMarkLaw μ m) tag =
      (finiteRNMarkComponent μ m tag univ)⁻¹ • (finiteRNMarkComponent μ m tag).map a := by
  ext A hA
  rw [condDistrib_apply_of_ne_zero
    (show Measurable (fun p : X × Option T ↦ a p.1) from ha.comp measurable_fst) tag
    (by rwa [finiteRNMarkLaw_type_mass]), finiteRNMarkLaw_type_mass,
    Measure.smul_apply, smul_eq_mul, Measure.map_apply ha hA,
    Measure.map_apply (show Measurable (fun p : X × Option T ↦ (p.2, a p.1)) from
      measurable_snd.prodMk (ha.comp measurable_fst))
      ((measurableSet_singleton tag).prod hA)]
  congr 1
  convert finiteRNMarkLaw_apply_cell μ m tag (ha hA) using 1
  congr 1
  ext p
  simp only [mem_preimage, mem_prod, mem_singleton_iff, and_comm]

/-- Raw type assignment probabilities are the products of their original
component masses. -/
theorem finiteRNMarkLaw_iid_assignment_mass {I : Type*} [Fintype I]
    (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] (assignment : I → Option T) :
    (Measure.pi (fun _ : I ↦ finiteRNMarkLaw μ m))
      (univ.pi (fun i ↦ Prod.snd ⁻¹' {assignment i})) =
        ∏ i, finiteRNMarkComponent μ m (assignment i) univ := by
  rw [Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [univ_prod] using
    finiteRNMarkLaw_apply_cell μ m (assignment i) MeasurableSet.univ

/-- Summing all type attributions, including the residual type, exactly recovers
the entire marked iid experiment. -/
theorem finiteRNMarkLaw_iid_decomposition {I : Type*} [Fintype I]
    (μ : Measure X) [IsFiniteMeasure μ]
    (m : T → Measure X) [∀ t, IsFiniteMeasure (m t)] :
    (∑ assignment : I → Option T,
      (Measure.pi (fun _ : I ↦ finiteRNMarkLaw μ m)).restrict
        (univ.pi (fun i ↦ Prod.snd ⁻¹' {assignment i}))) =
      Measure.pi (fun _ : I ↦ finiteRNMarkLaw μ m) := by
  have hm (assignment : I → Option T) :
      MeasurableSet (univ.pi (fun i ↦ Prod.snd ⁻¹' {assignment i}) : Set (I → X × Option T)) :=
    MeasurableSet.univ_pi (fun _ ↦ measurable_snd (measurableSet_singleton _))
  have hd : Pairwise (fun assignment assignment' : I → Option T ↦
      Disjoint (univ.pi (fun i ↦ Prod.snd ⁻¹' {assignment i}) : Set (I → X × Option T))
        (univ.pi (fun i ↦ Prod.snd ⁻¹' {assignment' i}))) := by
    intro assignment assignment' hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ((disjoint_singleton.mpr hi).preimage Prod.snd).set_pi (mem_univ i)
  have hc : (⋃ assignment : I → Option T,
      (univ.pi (fun i ↦ Prod.snd ⁻¹' {assignment i}) : Set (I → X × Option T))) = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    exact mem_iUnion.mpr ⟨fun i ↦ (x i).2, fun _ _ ↦ rfl⟩
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hd hm, hc, Measure.restrict_univ]

end OTSelector.Reconstruction
