import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedActiveValue
import OTSelector.Reconstruction.MarkedStationaryValueLegalSpatialDefect

/-! Spatial blocks read from the same whole original optional observations. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {W I J : Type*}

/-- The signed value of one deterministic spatial block of the whole optional cloud. -/
def optionalClassSpatialValue [Zero W] {B : Type*} [Fintype B] [DecidableEq B] {m n : ℕ}
    (i₀ : I) (j₀ : J) (mask : I → J → Prop)
    (score : (W × I) → (W × J) → ℝ) (label : W → B) (leaf : B)
    (sample : (Fin m → Option (W × I)) × (Fin n → Option (W × J))) : ℝ :=
  PartialMatching.legalMaximumValue
    (PartialMatching.spatialLegalBlock (optionalClassGraph i₀ j₀ mask sample.1 sample.2)
      (fun i ↦ label (optionalClassPoint (sample.1 i)))
      (fun j ↦ label (optionalClassPoint (sample.2 j))) leaf)
    (fun i j ↦ score (optionalClassPoint (sample.1 i),optionalClassIndex i₀ (sample.1 i))
      (optionalClassPoint (sample.2 j),optionalClassIndex j₀ (sample.2 j)))

/-- The spatially restricted signed value is measurable on the original whole cloud. -/
theorem measurable_optionalClassSpatialValue
    [MeasurableSpace W] [Zero W] [Fintype I] [Fintype J]
    [MeasurableSpace I] [MeasurableSpace J]
    [MeasurableSingletonClass I] [MeasurableSingletonClass J]
    {B : Type*} [Fintype B] [DecidableEq B] [MeasurableSpace B] [MeasurableSingletonClass B]
    {m n : ℕ} (i₀ : I) (j₀ : J) (mask : I → J → Prop)
    {score : (W × I) → (W × J) → ℝ} (hscore : Measurable (uncurry score))
    {label : W → B} (hlabel : Measurable label) (leaf : B) :
    Measurable (optionalClassSpatialValue (m := m) (n := n) i₀ j₀ mask score label leaf) := by
  let graph := fun sample : (Fin m → Option (W × I)) × (Fin n → Option (W × J)) ↦
    PartialMatching.spatialLegalBlock (optionalClassGraph i₀ j₀ mask sample.1 sample.2)
      (fun i ↦ label (optionalClassPoint (sample.1 i)))
      (fun j ↦ label (optionalClassPoint (sample.2 j))) leaf
  let cost := fun (sample : (Fin m → Option (W × I)) × (Fin n → Option (W × J))) i j ↦
    score (optionalClassPoint (sample.1 i),optionalClassIndex i₀ (sample.1 i))
      (optionalClassPoint (sample.2 j),optionalClassIndex j₀ (sample.2 j))
  have hlabels : Measurable (fun sample : (Fin m → Option (W × I)) × (Fin n → Option (W × J)) ↦
      ((fun i ↦ label (optionalClassPoint (sample.1 i))),
        (fun j ↦ label (optionalClassPoint (sample.2 j))))) :=
    (measurable_pi_lambda _ (fun i ↦ hlabel.comp
      (measurable_optionalClassPoint.comp ((measurable_pi_apply i).comp measurable_fst)))).prodMk
      (measurable_pi_lambda _ (fun j ↦ hlabel.comp
        (measurable_optionalClassPoint.comp ((measurable_pi_apply j).comp measurable_snd))))
  have hg : Measurable graph :=
    (measurable_of_countable (fun p : Finset (Fin m × Fin n) × ((Fin m → B) × (Fin n → B)) ↦
      PartialMatching.spatialLegalBlock p.1 p.2.1 p.2.2 leaf)).comp
        ((measurable_optionalClassGraph i₀ j₀ mask).prodMk hlabels)
  have hc : ∀ i j, Measurable (fun sample ↦ cost sample i j) := by
    intro i j
    exact hscore.comp (((measurable_optionalClassPoint.comp ((measurable_pi_apply i).comp measurable_fst)).prodMk
      ((measurable_optionalClassIndex i₀).comp ((measurable_pi_apply i).comp measurable_fst))).prodMk
      ((measurable_optionalClassPoint.comp ((measurable_pi_apply j).comp measurable_snd)).prodMk
        ((measurable_optionalClassIndex j₀).comp ((measurable_pi_apply j).comp measurable_snd))))
  exact PartialMatching.measurable_legalMaximumValue graph
    (fun V ↦ hg (measurableSet_singleton V)) cost hc

/-- Every fixed spatial block of a full optional observed graph is precisely
the original retained graph in its deterministic spatial subcell. -/
theorem originalRetainedCellGraph_eq_optionalClassSpatialBlock
    {X Z T B : Type*} [Fintype B] [DecidableEq B] [Zero W] {N : ℕ}
    (a : X → Z) (L : Set Z) (root : X → W) (label : W → B) (leaf : B)
    (markS : X → I) (markT : X → J) (i₀ : I) (j₀ : J) (mask : I → J → Prop)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) :
    let readS := fun p : X × Option (Bool × T) ↦
      if p ∈ retainedMarkedCellEvent (a ⁻¹' L) then some (root p.1, markS p.1) else none
    let readT := fun p : X × Option (Bool × T) ↦
      if p ∈ retainedMarkedCellEvent (a ⁻¹' L) then some (root p.1, markT p.1) else none
    originalRetainedCellGraph a (fun _ : Unit ↦ L)
      (fun _ cloud ↦ Finset.univ.filter (fun e : Fin N × Fin N ↦
        mask (markS (cloud.1 e.1).1) (markT (cloud.2 e.2).1) ∧
        label (root (cloud.1 e.1).1) = leaf ∧ label (root (cloud.2 e.2).1) = leaf)) () sample =
      PartialMatching.spatialLegalBlock
        (optionalClassGraph i₀ j₀ mask (fun i ↦ readS (sample.1 i)) (fun j ↦ readT (sample.2 j)))
        (fun i ↦ label (optionalClassPoint (readS (sample.1 i))))
        (fun j ↦ label (optionalClassPoint (readT (sample.2 j)))) leaf := by
  dsimp only
  ext e
  simp only [originalRetainedCellGraph,optionalClassGraph,PartialMatching.spatialLegalBlock,
    Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hs : sample.1 e.1 ∈ retainedMarkedCellEvent (a ⁻¹' L) <;>
    by_cases ht : sample.2 e.2 ∈ retainedMarkedCellEvent (a ⁻¹' L) <;>
      simp only [hs,ht,ite_true,ite_false,optionalClassIndex,optionalClassPoint,
        Option.elim_some,Option.elim_none,Option.isSome_some,Option.isSome_none,
        true_and,Bool.false_eq_true,false_and,and_false]
  all_goals
    simp only [retainedMarkedCellEvent,mem_ofPred_eq,mem_preimage] at hs ht
    tauto

/-- Reading a spatial label after forgetting the latent opposite class gives
the same literal spatial block of the paired active graph. -/
theorem optionalClassSpatialBlock_paired_read_eq
    [Zero W] {B : Type*} [Fintype B] [DecidableEq B] {m n : ℕ}
    (i₀ : I) (j₀ : J) (mask : I → J → Prop) (label : W → B) (leaf : B)
    (sample : (Fin m → Option W × (I × J)) × (Fin n → Option W × (I × J))) :
    PartialMatching.spatialLegalBlock
      (optionalClassGraph i₀ j₀ mask
        (fun i ↦ pairedActiveSourceRead (sample.1 i)) (fun j ↦ pairedActiveTargetRead (sample.2 j)))
      (fun i ↦ label (optionalClassPoint (pairedActiveSourceRead (sample.1 i))))
      (fun j ↦ label (optionalClassPoint (pairedActiveTargetRead (sample.2 j)))) leaf =
    PartialMatching.spatialLegalBlock
      (pairedClassActiveGraph (fun o : Option W ↦ o.map (fun _ ↦ ())) mask sample.1 sample.2)
      (fun i ↦ label ((sample.1 i).1.elim 0 id))
      (fun j ↦ label ((sample.2 j).1.elim 0 id)) leaf := by
  ext e
  cases hs : (sample.1 e.1).1 <;> cases ht : (sample.2 e.2).1 <;>
    simp [PartialMatching.spatialLegalBlock,optionalClassGraph,pairedClassActiveGraph,
      pairedActiveSourceRead,pairedActiveTargetRead,optionalClassIndex,optionalClassPoint,hs,ht]

/-- Spatial gating can be written as a literal original label subcell. -/
theorem originalRetainedCellGraph_spatial_subcell_eq
    {X Z T B : Type*} {N : ℕ} (a : X → Z) (L : Set Z) (root : Z → W)
    (label : W → B) (leaf : B) (markS : X → I) (markT : X → J) (mask : I → J → Prop)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) :
    originalRetainedCellGraph a (fun _ : Unit ↦ L ∩ (label ∘ root) ⁻¹' {leaf})
      (fun _ cloud ↦ Finset.univ.filter fun ij : Fin N × Fin N ↦
        mask (markS (cloud.1 ij.1).1) (markT (cloud.2 ij.2).1)) () sample =
    originalRetainedCellGraph a (fun _ : Unit ↦ L)
      (fun _ cloud ↦ Finset.univ.filter fun ij : Fin N × Fin N ↦
        mask (markS (cloud.1 ij.1).1) (markT (cloud.2 ij.2).1) ∧
        label (root (a (cloud.1 ij.1).1)) = leaf ∧
        label (root (a (cloud.2 ij.2).1)) = leaf) () sample := by
  ext ij
  simp only [originalRetainedCellGraph,Finset.mem_filter,Finset.mem_univ,true_and,
    mem_inter_iff,mem_preimage,mem_singleton_iff,Function.comp_apply]
  tauto

/-- The original canonical spatial-subcell cost reads the literal block of
its full macrocell optional observation. -/
theorem originalRetainedSeedClassCost_eq_optionalClassSpatialValue
    {X Z T B : Type*} [Fintype B] [DecidableEq B] [AddCommGroup W] [Module ℝ W] {q N : ℕ}
    (a : X → Z) (L : Set Z) (root : Z → W) (e : W →ₗ[ℝ] (Fin q → ℝ))
    (label : W → B) (leaf : B) (markS : X → I) (markT : X → J)
    (i₀ : I) (j₀ : J) (mask : I → J → Prop)
    (scale : ℝ) (kin : I → J → (Fin q → ℝ) → ℝ) (probe : I → J → ℝ) (tilt : ℝ)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) :
    let readS := fun p : X × Option (Bool × T) ↦
      if p ∈ retainedMarkedCellEvent (a ⁻¹' L) then some (root (a p.1),markS p.1) else none
    let readT := fun p : X × Option (Bool × T) ↦
      if p ∈ retainedMarkedCellEvent (a ⁻¹' L) then some (root (a p.1),markT p.1) else none
    originalRetainedSeedClassCost a (L ∩ (label ∘ root) ⁻¹' {leaf}) (fun x ↦ root (a x))
      e markS markT mask scale kin probe tilt sample =
    optionalClassSpatialValue i₀ j₀ mask
      (fun p p' ↦ scale * kin p.2 p'.2 (e (p'.1-p.1)) + tilt * probe p.2 p'.2) label leaf
      ((fun j ↦ readS (sample.1 j)),fun k ↦ readT (sample.2 k)) := by
  classical
  dsimp only
  unfold originalRetainedSeedClassCost originalRetainedCellOptimizer
  rw [(PartialMatching.firstLegalOptimalMatching_isLegalOptimal _ _).2.2]
  unfold optionalClassSpatialValue
  have hg : originalRetainedCellGraph a (fun _ : Unit ↦ L ∩ (label ∘ root) ⁻¹' {leaf})
      (fun _ cloud ↦ Finset.univ.filter fun ij : Fin N × Fin N ↦
        mask (markS (cloud.1 ij.1).1) (markT (cloud.2 ij.2).1)) () sample =
      PartialMatching.spatialLegalBlock
        (optionalClassGraph i₀ j₀ mask
          (fun i ↦ if sample.1 i ∈ retainedMarkedCellEvent (a ⁻¹' L) then
            some (root (a (sample.1 i).1),markS (sample.1 i).1) else none)
          (fun j ↦ if sample.2 j ∈ retainedMarkedCellEvent (a ⁻¹' L) then
            some (root (a (sample.2 j).1),markT (sample.2 j).1) else none))
        (fun i ↦ label (optionalClassPoint (if sample.1 i ∈ retainedMarkedCellEvent (a ⁻¹' L) then
          some (root (a (sample.1 i).1),markS (sample.1 i).1) else none)))
        (fun j ↦ label (optionalClassPoint (if sample.2 j ∈ retainedMarkedCellEvent (a ⁻¹' L) then
          some (root (a (sample.2 j).1),markT (sample.2 j).1) else none))) leaf := by
    ext ij
    simp only [originalRetainedCellGraph,PartialMatching.spatialLegalBlock,optionalClassGraph,
      Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases hs : sample.1 ij.1 ∈ retainedMarkedCellEvent (a ⁻¹' L) <;>
      by_cases ht : sample.2 ij.2 ∈ retainedMarkedCellEvent (a ⁻¹' L) <;>
        simp only [hs,ht,ite_true,ite_false,optionalClassIndex,optionalClassPoint,
          Option.elim_some,Option.elim_none,Option.isSome_some,Option.isSome_none,
          true_and,Bool.false_eq_true,false_and,and_false]
    all_goals
      simp only [retainedMarkedCellEvent,mem_ofPred_eq,mem_preimage] at hs ht
      simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,Function.comp_apply]
      tauto
  rw [hg]
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j hij
  by_cases hs : sample.1 i ∈ retainedMarkedCellEvent (a ⁻¹' L) <;>
    by_cases ht : sample.2 j ∈ retainedMarkedCellEvent (a ⁻¹' L)
  · simp only [hs,ht,ite_true,optionalClassPoint,optionalClassIndex,Option.elim_some]
  all_goals
    simp [PartialMatching.spatialLegalBlock,optionalClassGraph,hs,ht] at hij

/-- The paired spatial block retains exactly its original raw displacement. -/
theorem optionalClassSpatialValue_paired_read_eq
    [AddCommGroup W] [Module ℝ W] {B : Type*} [Fintype B] [DecidableEq B] {q m n : ℕ}
    (i₀ : I) (j₀ : J) (mask : I → J → Prop) (e : W →ₗ[ℝ] (Fin q → ℝ))
    (label : W → B) (leaf : B) (scale : ℝ)
    (kin : I → J → (Fin q → ℝ) → ℝ) (probe : I → J → ℝ) (tilt : ℝ)
    (sample : (Fin m → Option W × (I × J)) × (Fin n → Option W × (I × J))) :
    optionalClassSpatialValue i₀ j₀ mask
      (fun p p' ↦ scale * kin p.2 p'.2 (e (p'.1 - p.1)) + tilt * probe p.2 p'.2) label leaf
      ((fun i ↦ pairedActiveSourceRead (sample.1 i)),fun j ↦ pairedActiveTargetRead (sample.2 j)) =
    PartialMatching.legalMaximumValue
      (PartialMatching.spatialLegalBlock
        (pairedClassActiveGraph (fun o : Option W ↦ o.map (fun _ ↦ ())) mask sample.1 sample.2)
        (fun i ↦ label ((sample.1 i).1.elim 0 id))
        (fun j ↦ label ((sample.2 j).1.elim 0 id)) leaf)
      (fun i j ↦ scale * kin (sample.1 i).2.1 (sample.2 j).2.2
        (e ((sample.2 j).1.elim 0 id - (sample.1 i).1.elim 0 id)) +
        tilt * probe (sample.1 i).2.1 (sample.2 j).2.2) := by
  unfold optionalClassSpatialValue
  rw [optionalClassSpatialBlock_paired_read_eq]
  apply PartialMatching.legalMaximumValue_congr_on_allowed
  intro i j hij
  have h := (mem_pairedClassActiveGraph _ _ _ _ (i,j)).mp (Finset.mem_filter.mp hij).1
  cases hs : (sample.1 i).1 <;> cases ht : (sample.2 j).1 <;>
    simp_all [pairedActiveSourceRead,pairedActiveTargetRead,optionalClassPoint,optionalClassIndex]

end OTSelector.Reconstruction
