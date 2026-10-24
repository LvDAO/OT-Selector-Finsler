import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedActiveLaw
import OTSelector.Reconstruction.FinslerRelativeLawActualMicrocellShapeExpectation
import OTSelector.Reconstruction.FinslerConcreteUpperClassActive

/-! Exact legal values read from the full optional class observations. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

variable {W I J : Type*}

/-- An inactive vertex has an arbitrary fixed class; its graph row is empty. -/
def optionalClassIndex (fallback : I) (x : Option (W × I)) : I :=
  x.elim fallback Prod.snd

/-- The position of an inactive vertex is immaterial to its empty graph row. -/
def optionalClassPoint [Zero W] (x : Option (W × I)) : W := x.elim 0 Prod.fst

/-- The literal active graph on the whole observed arrays. -/
def optionalClassGraph {m n : ℕ} (i₀ : I) (j₀ : J) (mask : I → J → Prop)
    (xs : Fin m → Option (W × I)) (ys : Fin n → Option (W × J)) :
    Finset (Fin m × Fin n) :=
  Finset.univ.filter fun e ↦ (xs e.1).isSome ∧ (ys e.2).isSome ∧
    mask (optionalClassIndex i₀ (xs e.1)) (optionalClassIndex j₀ (ys e.2))

/-- The signed active finite value, with no iid claim for selected vertices. -/
def optionalClassValue [Zero W] {m n : ℕ}
    (i₀ : I) (j₀ : J) (mask : I → J → Prop)
    (score : (W × I) → (W × J) → ℝ)
    (sample : (Fin m → Option (W × I)) × (Fin n → Option (W × J))) : ℝ :=
  PartialMatching.legalMaximumValue (optionalClassGraph i₀ j₀ mask sample.1 sample.2)
    (fun i j ↦ score
      (optionalClassPoint (sample.1 i), optionalClassIndex i₀ (sample.1 i))
      (optionalClassPoint (sample.2 j), optionalClassIndex j₀ (sample.2 j)))

section Measurability
variable [MeasurableSpace W] [Zero W] [Fintype I] [Fintype J]
  [MeasurableSpace I] [MeasurableSpace J]
  [MeasurableSingletonClass I] [MeasurableSingletonClass J]

theorem measurable_optionalClassIndex (i₀ : I) :
    Measurable (optionalClassIndex (W := W) i₀) :=
  MeasureTheory.Option.measurable_elim i₀ measurable_snd

theorem measurable_optionalClassPoint : Measurable (optionalClassPoint (W := W) (I := I)) :=
  MeasureTheory.Option.measurable_elim 0 measurable_fst

/-- Finite class labels and activity alone determine every graph event. -/
theorem measurable_optionalClassGraph {m n : ℕ} (i₀ : I) (j₀ : J) (mask : I → J → Prop) :
    Measurable (fun sample : (Fin m → Option (W × I)) × (Fin n → Option (W × J)) ↦
      optionalClassGraph i₀ j₀ mask sample.1 sample.2) := by
  let labels := fun sample : (Fin m → Option (W × I)) × (Fin n → Option (W × J)) ↦
    ((fun i ↦ ((sample.1 i).isSome, optionalClassIndex i₀ (sample.1 i))),
      (fun j ↦ ((sample.2 j).isSome, optionalClassIndex j₀ (sample.2 j))))
  have hm : Measurable labels := by
    apply Measurable.prodMk
    · exact measurable_pi_lambda _ (fun i ↦
        ((MeasureTheory.Option.measurable_isSome).comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
          ((measurable_optionalClassIndex i₀).comp ((measurable_pi_apply i).comp measurable_fst)))
    · exact measurable_pi_lambda _ (fun j ↦
        ((MeasureTheory.Option.measurable_isSome).comp ((measurable_pi_apply j).comp measurable_snd)).prodMk
          ((measurable_optionalClassIndex j₀).comp ((measurable_pi_apply j).comp measurable_snd)))
  exact (measurable_of_countable (fun labels :
    (Fin m → Bool × I) × (Fin n → Bool × J) ↦ Finset.univ.filter fun e : Fin m × Fin n ↦
      (labels.1 e.1).1 ∧ (labels.2 e.2).1 ∧ mask (labels.1 e.1).2 (labels.2 e.2).2)).comp hm

/-- The full optional-cloud signed legal value is measurable. -/
theorem measurable_optionalClassValue {m n : ℕ} (i₀ : I) (j₀ : J) (mask : I → J → Prop)
    {score : (W × I) → (W × J) → ℝ} (hs : Measurable (Function.uncurry score)) :
    Measurable (optionalClassValue (m := m) (n := n) i₀ j₀ mask score) := by
  let graph := fun sample : (Fin m → Option (W × I)) × (Fin n → Option (W × J)) ↦
    optionalClassGraph i₀ j₀ mask sample.1 sample.2
  let cost := fun (sample : (Fin m → Option (W × I)) × (Fin n → Option (W × J))) i j ↦
    score (optionalClassPoint (sample.1 i), optionalClassIndex i₀ (sample.1 i))
      (optionalClassPoint (sample.2 j), optionalClassIndex j₀ (sample.2 j))
  have hg : ∀ S, MeasurableSet {sample | graph sample = S} := fun S ↦
    (measurable_optionalClassGraph (m := m) (n := n) i₀ j₀ mask) (measurableSet_singleton S)
  have hc : ∀ i j, Measurable (fun sample ↦ cost sample i j) := by
    intro i j
    exact hs.comp (((measurable_optionalClassPoint.comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
      ((measurable_optionalClassIndex i₀).comp ((measurable_pi_apply i).comp measurable_fst))).prodMk
      ((measurable_optionalClassPoint.comp ((measurable_pi_apply j).comp measurable_snd)).prodMk
        ((measurable_optionalClassIndex j₀).comp ((measurable_pi_apply j).comp measurable_snd))))
  exact PartialMatching.measurable_legalMaximumValue graph hg cost hc

end Measurability

/-- Gating the actual original endpoints factors the literal retained graph. -/
theorem originalRetainedCellGraph_eq_optionalClassGraph
    {X Z T : Type*} {N : ℕ} (a : X → Z) (L : Set Z) (root : X → W)
    (markS : X → I) (markT : X → J) (i₀ : I) (j₀ : J) (mask : I → J → Prop)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) :
    let readS := fun p : X × Option (Bool × T) ↦
      if p ∈ retainedMarkedCellEvent (a ⁻¹' L) then some (root p.1, markS p.1) else none
    let readT := fun p : X × Option (Bool × T) ↦
      if p ∈ retainedMarkedCellEvent (a ⁻¹' L) then some (root p.1, markT p.1) else none
    originalRetainedCellGraph a (fun _ : Unit ↦ L)
      (fun _ cloud ↦ Finset.univ.filter (fun e : Fin N × Fin N ↦
        mask (markS (cloud.1 e.1).1) (markT (cloud.2 e.2).1))) () sample =
      optionalClassGraph i₀ j₀ mask (fun i ↦ readS (sample.1 i)) (fun j ↦ readT (sample.2 j)) := by
  dsimp only
  ext e
  simp only [originalRetainedCellGraph,optionalClassGraph,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hs : sample.1 e.1 ∈ retainedMarkedCellEvent (a ⁻¹' L) <;>
    by_cases ht : sample.2 e.2 ∈ retainedMarkedCellEvent (a ⁻¹' L) <;>
      simp only [hs,ht,ite_true,ite_false,optionalClassIndex,Option.elim_some,Option.elim_none,
        Option.isSome_some,Option.isSome_none,true_and,Bool.false_eq_true,false_and,and_false]
  all_goals
    simp only [retainedMarkedCellEvent,mem_ofPred_eq,mem_preimage] at hs ht
    tauto

/-- The original first optimizer's cost is the value of exactly its gated
whole-cloud observation; its tie choice has no effect on the legal value. -/
theorem originalRetainedSeedClassCost_eq_optionalClassValue
    {X Z T : Type*} [AddCommGroup W] [Module ℝ W] {q N : ℕ}
    (a : X → Z) (L : Set Z) (root : X → W) (e : W →ₗ[ℝ] (Fin q → ℝ))
    (markS : X → I) (markT : X → J) (i₀ : I) (j₀ : J) (mask : I → J → Prop)
    (scale : ℝ) (kin : I → J → (Fin q → ℝ) → ℝ) (probe : I → J → ℝ) (tilt : ℝ)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) :
    let readS := fun p : X × Option (Bool × T) ↦
      if p ∈ retainedMarkedCellEvent (a ⁻¹' L) then some (root p.1, markS p.1) else none
    let readT := fun p : X × Option (Bool × T) ↦
      if p ∈ retainedMarkedCellEvent (a ⁻¹' L) then some (root p.1, markT p.1) else none
    originalRetainedSeedClassCost a L root e markS markT mask scale kin probe tilt sample =
      optionalClassValue i₀ j₀ mask
        (fun p p' ↦ scale * kin p.2 p'.2 (e (p'.1 - p.1)) + tilt * probe p.2 p'.2)
        ((fun i ↦ readS (sample.1 i)), fun j ↦ readT (sample.2 j)) := by
  classical
  dsimp only
  let extra := fun (_ : Unit) (cloud : (Fin N → X × Option (Bool × T)) ×
      (Fin N → X × Option (Bool × T))) ↦ Finset.univ.filter (fun ij : Fin N × Fin N ↦
    mask (markS (cloud.1 ij.1).1) (markT (cloud.2 ij.2).1))
  let score := fun (_ : Unit) (cloud : (Fin N → X × Option (Bool × T)) ×
      (Fin N → X × Option (Bool × T))) i j ↦ scale * kin (markS (cloud.1 i).1)
      (markT (cloud.2 j).1) (e (root (cloud.2 j).1 - root (cloud.1 i).1)) +
      tilt * probe (markS (cloud.1 i).1) (markT (cloud.2 j).1)
  change (originalRetainedCellOptimizer a (fun _ : Unit ↦ L) extra score () sample).cost (score () sample) = _
  rw [(originalRetainedCellOptimizer_isLegalOptimal a (fun _ : Unit ↦ L) extra score () sample).2.2]
  unfold optionalClassValue
  rw [← originalRetainedCellGraph_eq_optionalClassGraph a L root markS markT i₀ j₀ mask sample]
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j hij
  have h := Finset.mem_filter.mp hij
  have hs : sample.1 i ∈ retainedMarkedCellEvent (a ⁻¹' L) := ⟨h.2.1,h.2.2.2.1⟩
  have ht : sample.2 j ∈ retainedMarkedCellEvent (a ⁻¹' L) := ⟨h.2.2.1,h.2.2.2.2⟩
  simp only [hs, ht, ite_true, optionalClassPoint, optionalClassIndex, Option.elim_some]
  rfl

/-- Forgetting the latent opposite class leaves exactly the paired active
model value, with the same original endpoint differences on all legal edges. -/
theorem optionalClassValue_paired_read_eq
    [AddCommGroup W] [Module ℝ W] {q m n : ℕ}
    (i₀ : I) (j₀ : J) (mask : I → J → Prop) (e : W →ₗ[ℝ] (Fin q → ℝ))
    (scale : ℝ) (kin : I → J → (Fin q → ℝ) → ℝ) (probe : I → J → ℝ) (tilt : ℝ)
    (sample : (Fin m → Option W × (I × J)) × (Fin n → Option W × (I × J))) :
    optionalClassValue i₀ j₀ mask
      (fun p p' ↦ scale * kin p.2 p'.2 (e (p'.1 - p.1)) + tilt * probe p.2 p'.2)
      ((fun i ↦ pairedActiveSourceRead (sample.1 i)), fun j ↦ pairedActiveTargetRead (sample.2 j)) =
    PartialMatching.legalMaximumValue
      (pairedClassActiveGraph (fun o : Option W ↦ o.map (fun _ ↦ ())) mask sample.1 sample.2)
      (fun i j ↦ scale * kin (sample.1 i).2.1 (sample.2 j).2.2
        (e ((sample.2 j).1.elim 0 id - (sample.1 i).1.elim 0 id)) +
        tilt * probe (sample.1 i).2.1 (sample.2 j).2.2) := by
  have hg : optionalClassGraph i₀ j₀ mask
      (fun i ↦ pairedActiveSourceRead (sample.1 i)) (fun j ↦ pairedActiveTargetRead (sample.2 j)) =
      pairedClassActiveGraph (fun o : Option W ↦ o.map (fun _ ↦ ())) mask sample.1 sample.2 := by
    ext ij
    cases hs : (sample.1 ij.1).1 <;> cases ht : (sample.2 ij.2).1 <;>
      simp [optionalClassGraph, pairedClassActiveGraph, pairedActiveSourceRead,
        pairedActiveTargetRead, optionalClassIndex, hs,ht]
  unfold optionalClassValue
  rw [hg]
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j hij
  have h := (mem_pairedClassActiveGraph _ _ _ _ (i,j)).mp hij
  cases hs : (sample.1 i).1 <;> cases ht : (sample.2 j).1 <;>
    simp_all [pairedActiveSourceRead,pairedActiveTargetRead,optionalClassPoint,optionalClassIndex]

end OTSelector.Reconstruction
