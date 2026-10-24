import OTSelector.Reconstruction.FinslerConcreteUpperClassPaired
import OTSelector.Reconstruction.MarkedStationaryValueLegalActiveTypes

/-! Literal active legal graphs on full arrays of spatial and pair-class points.
The latent opposite class certifies legal same-type comparators without changing
any observed edge or assigning a sampling law to unmatched points. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {X I J C : Type*}

/-- Literal active graph, using the observed source and target class indices. -/
def pairedClassActiveGraph {m n : ℕ} (θ : X → Option C) (allowed : I → J → Prop)
    (xs : Fin m → X × (I × J)) (ys : Fin n → X × (I × J)) :
    Finset (Fin m × Fin n) :=
  Finset.univ.filter fun e ↦ (θ (xs e.1).1).isSome ∧ (θ (ys e.2).1).isSome ∧
    allowed (xs e.1).2.1 (ys e.2).2.2

@[simp]
theorem mem_pairedClassActiveGraph {m n : ℕ} (θ : X → Option C)
    (allowed : I → J → Prop) (xs : Fin m → X × (I × J))
    (ys : Fin n → X × (I × J)) (e : Fin m × Fin n) :
    e ∈ pairedClassActiveGraph θ allowed xs ys ↔
      (θ (xs e.1).1).isSome ∧ (θ (ys e.2).1).isSome ∧
        allowed (xs e.1).2.1 (ys e.2).2.2 := by
  simp [pairedClassActiveGraph]

/-- Inactivity is a distinct source row class; active rows keep their actual
source class only. -/
def pairedClassActiveSourceClass (θ : X → Option C) (z : X × (I × J)) : Option I :=
  (θ z.1).map (fun _ ↦ z.2.1)

/-- All rows of one active source class have the same original neighborhood. -/
def pairedClassActiveSourceAllows {n : ℕ} (θ : X → Option C)
    (allowed : I → J → Prop) (ys : Fin n → X × (I × J))
    (a : Option I) (j : Fin n) : Prop :=
  ∃ i, a = some i ∧ (θ (ys j).1).isSome ∧ allowed i (ys j).2.2

theorem pairedClassActiveGraph_row_factorization {m n : ℕ}
    (θ : X → Option C) (allowed : I → J → Prop)
    (xs : Fin m → X × (I × J)) (ys : Fin n → X × (I × J)) (i : Fin m) (j : Fin n) :
    (i, j) ∈ pairedClassActiveGraph θ allowed xs ys ↔
      pairedClassActiveSourceAllows θ allowed ys (pairedClassActiveSourceClass θ (xs i)) j := by
  cases h : θ (xs i).1 <;>
    simp [pairedClassActiveSourceAllows, pairedClassActiveSourceClass, h]

/-- The literal paired type records exactly the spatial label and both class
indices, including individual zero-mass class pairs. -/
theorem pairedClassTag_eq_some_iff (θ : X → Option C) (z : X × (I × J))
    (c : C) (p : I × J) :
    pairedClassTag θ z = some (c, p) ↔ θ z.1 = some c ∧ z.2 = p := by
  cases h : θ z.1 <;> simp [pairedClassTag, h]

/-- A legal own pair on the source point turns an equal paired type into an
actual legal edge and equality of the original spatial labels. -/
theorem pairedClassActiveGraph_same_type {m n : ℕ}
    (θ : X → Option C) (allowed : I → J → Prop)
    (xs : Fin m → X × (I × J)) (ys : Fin n → X × (I × J))
    (hown : ∀ i, allowed (xs i).2.1 (xs i).2.2)
    (i : Fin m) (j : Fin n) (a : C × (I × J))
    (hi : pairedClassTag θ (xs i) = some a)
    (hj : pairedClassTag θ (ys j) = some a) :
    (i, j) ∈ pairedClassActiveGraph θ allowed xs ys ∧
      θ (xs i).1 = θ (ys j).1 := by
  obtain ⟨hiθ, hip⟩ := (pairedClassTag_eq_some_iff θ (xs i) a.1 a.2).mp hi
  obtain ⟨hjθ, hjp⟩ := (pairedClassTag_eq_some_iff θ (ys j) a.1 a.2).mp hj
  refine ⟨(mem_pairedClassActiveGraph θ allowed xs ys (i, j)).mpr ?_, hiθ.trans hjθ.symm⟩
  refine ⟨by simp [hiθ], by simp [hjθ], ?_⟩
  have hpair : (xs i).2 = (ys j).2 := hip.trans hjp.symm
  rw [← congrArg Prod.snd hpair]
  exact hown i

variable [MeasurableSpace X] [Fintype I] [Fintype J] [Fintype C]
  [MeasurableSpace I] [MeasurableSpace J]
  [MeasurableSingletonClass I] [MeasurableSingletonClass J]
  [MeasurableSpace (Option C)] [MeasurableSingletonClass (Option C)]

/-- Membership in the literal original active graph is measurable under any
measurable arrays. No independence or replacement population is assumed. -/
theorem measurableSet_mem_pairedClassActiveGraph
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    {θ : X → Option C} (hθ : Measurable θ) (allowed : I → J → Prop)
    (xs : Fin m → Ω → X × (I × J)) (ys : Fin n → Ω → X × (I × J))
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ j, Measurable (ys j)) (e : Fin m × Fin n) :
    MeasurableSet {ω | e ∈ pairedClassActiveGraph θ allowed
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)} := by
  have hactive : MeasurableSet {a : Option C | a.isSome} :=
    (Set.to_countable _).measurableSet
  have hA := hactive.preimage (hθ.comp (measurable_fst.comp (hx e.1)))
  have hB := hactive.preimage (hθ.comp (measurable_fst.comp (hy e.2)))
  have hlegal : MeasurableSet {p : I × J | allowed p.1 p.2} :=
    (Set.to_countable _).measurableSet
  have hL := hlegal.preimage
    ((measurable_fst.comp (measurable_snd.comp (hx e.1))).prodMk
      (measurable_snd.comp (measurable_snd.comp (hy e.2))))
  simp only [mem_pairedClassActiveGraph, Set.ofPred_and]
  exact hA.inter (hB.inter hL)

/-- Original own-pair legality on the source array supplies all same-type edge
comparators at once, without an assumption on adaptive unmatched endpoints. -/
theorem pairedClassActiveGraph_same_type_ae
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (P : Measure Ω) (θ : X → Option C) (allowed : I → J → Prop)
    (xs : Fin m → Ω → X × (I × J)) (ys : Fin n → Ω → X × (I × J))
    (hown : ∀ i, ∀ᵐ ω ∂P, allowed (xs i ω).2.1 (xs i ω).2.2) :
    ∀ᵐ ω ∂P, ∀ i j a,
      pairedClassTag θ (xs i ω) = some a → pairedClassTag θ (ys j ω) = some a →
        (i, j) ∈ pairedClassActiveGraph θ allowed
          (fun i ↦ xs i ω) (fun j ↦ ys j ω) ∧ θ (xs i ω).1 = θ (ys j ω).1 := by
  filter_upwards [ae_all_iff.mpr hown] with ω hω
  intro i j a hi hj
  exact pairedClassActiveGraph_same_type θ allowed (fun i ↦ xs i ω) (fun j ↦ ys j ω)
    hω i j a hi hj

end OTSelector.Reconstruction
