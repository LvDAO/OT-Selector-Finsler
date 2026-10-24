import OTSelector.Reconstruction.OriginalLegalWeightedCarrierPortCapacity
import OTSelector.Reconstruction.MarkedStationaryValueLegalActiveHierarchy
import OTSelector.Reconstruction.FinslerConcreteUpperModel
import OTSelector.Reconstruction.OriginalLegalWeightedClockCarrierRecovery

/-!
# Original matrix cost of completing the actual free carrier ports

The legal Hall completion is optimized only on its actual residual rows and
unused columns. The retained original core stays fixed. Hierarchical costs
use original spatial coordinates and a compact bound on the original matrix.
-/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace PartialMatching
variable {m n : ℕ}

/-- The literal residual graph restricted to the actual rows being completed. -/
def activeResidualAllowed (allowed : Finset (Fin m × Fin n))
    (σ : OTSelector.PartialMatching m n) (active : Finset (Fin m)) :
    Finset (Fin m × Fin n) :=
  (residualAllowed allowed σ).filter (fun p ↦ p.1 ∈ active)

/-- A witness matching all active ports proves their exact residual rank. -/
theorem legalMaximumCard_activeResidualAllowed
    (allowed : Finset (Fin m × Fin n)) (σ ρ : OTSelector.PartialMatching m n)
    (active : Finset (Fin m))
    (hρ : IsLegal (residualAllowed allowed σ) ρ) (hrows : ρ.rows = active) :
    legalMaximumCard (activeResidualAllowed allowed σ active) = active.card := by
  have hρa : IsLegal (activeResidualAllowed allowed σ active) ρ := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨hρ hp, hrows ▸ Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  apply le_antisymm
  · obtain ⟨τ,hτ,hcard⟩ := exists_legalMaximumCard (activeResidualAllowed allowed σ active)
    rw [← hcard, ← τ.card_rows]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp (hτ hp)).2
  · have hc : ρ.card = active.card := by rw [← ρ.card_rows,hrows]
    simpa only [hc] using card_le_legalMaximumCard hρa

/-- Among the actual residual port completions choose one minimizing the
original signed cost. Every old core edge is preserved. -/
theorem exists_minCost_active_completion
    (allowed : Finset (Fin m × Fin n)) (σ ρ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ) (active : Finset (Fin m))
    (hρ : IsLegal (residualAllowed allowed σ) ρ) (hrows : ρ.rows = active)
    (c : Fin m → Fin n → ℝ) :
    ∃ τ δ : OTSelector.PartialMatching m n,
      IsLegal allowed τ ∧ σ.edges ⊆ τ.edges ∧
      IsLegal (residualAllowed allowed σ) δ ∧ δ.rows = active ∧
      δ.card = active.card ∧ τ.edges = σ.edges ∪ δ.edges ∧
      τ.card = σ.card + active.card ∧
      δ.cost c = legalMaximumValue (activeResidualAllowed allowed σ active) c ∧
      τ.cost c = σ.cost c + legalMaximumValue (activeResidualAllowed allowed σ active) c := by
  let G := activeResidualAllowed allowed σ active
  have hrank := legalMaximumCard_activeResidualAllowed allowed σ ρ active hρ hrows
  obtain ⟨δ,hδ,hcard,hcost⟩ := exists_cost_eq_legalMaximumValue G c
  have hδr : IsLegal (residualAllowed allowed σ) δ :=
    fun p hp ↦ (Finset.mem_filter.mp (hδ hp)).1
  have hdsub : δ.rows ⊆ active := by
    intro i hi
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp (hδ hp)).2
  have hdcard : δ.card = active.card := hcard.trans hrank
  have hdrows : δ.rows = active := Finset.eq_of_subset_of_card_le hdsub
    (by rw [δ.card_rows,hdcard])
  obtain ⟨hr,hc⟩ := residualAllowed_disjoint σ δ hδr
  let τ := σ.union δ hr hc
  refine ⟨τ,δ,isLegal_union_residual σ δ hσ hδr,Finset.subset_union_left,
    hδr,hdrows,hdcard,rfl,?_,hcost,?_⟩
  · exact (OTSelector.PartialMatching.card_union σ δ hr hc).trans (by rw [hdcard])
  · rw [OTSelector.PartialMatching.cost_union, hcost]

/-- Active residual source classes are produced by restricting the original
classes; used target columns are excluded in their actual neighborhoods. -/
theorem activeResidualAllowed_exists_classes
    {J : Type*} (allowed : Finset (Fin m × Fin n))
    (σ : OTSelector.PartialMatching m n) (active : Finset (Fin m))
    (label : Fin m → J) (allows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i,j) ∈ allowed ↔ allows (label i) j) :
    ∃ tag : Fin m → Option J, ∃ accepts : Option J → Fin n → Prop,
      ∀ i j, (i,j) ∈ activeResidualAllowed allowed σ active ↔ accepts (tag i) j := by
  let tag : Fin m → Option J := fun i ↦
    if i ∈ active ∧ i ∉ σ.rows then some (label i) else none
  let accepts : Option J → Fin n → Prop := fun a j ↦
    match a with
    | none => False
    | some a => j ∉ σ.cols ∧ allows a j
  refine ⟨tag,accepts,fun i j ↦ ?_⟩
  by_cases hi : i ∈ active ∧ i ∉ σ.rows
  · simp [activeResidualAllowed,residualAllowed,hallowed,tag,accepts,hi.1,hi.2,and_comm]
  · simp [activeResidualAllowed,residualAllowed,hallowed,tag,accepts,hi]
    tauto

/-- Only actual active source rows enter the hierarchy. Old used rows and
outside-carrier rows make no contribution to any child deficiency. -/
theorem activeResidualAllowed_value_le_hierarchy
    {J : Type*} [Fintype J]
    {C : ℕ → Type*} [∀ k,Fintype (C k)] [∀ k,DecidableEq (C k)]
    (allowed : Finset (Fin m × Fin n)) (σ : OTSelector.PartialMatching m n)
    (active : Finset (Fin m))
    (s : (k:ℕ) → Fin m → C k) (t : (k:ℕ) → Fin n → C k)
    (parent : (k:ℕ) → C (k+1) → C k) (K : ℕ)
    (hs : ∀ k,k<K → ∀ i,parent k (s (k+1) i)=s k i)
    (ht : ∀ k,k<K → ∀ j,parent k (t (k+1) j)=t k j)
    (label : Fin m → J) (allows : J → Fin n → Prop)
    (hallowed : ∀ i j,(i,j)∈allowed ↔ allows (label i) j)
    (c : Fin m → Fin n → ℝ) (B : ℕ → ℝ) (hB0 : ∀ k,0≤B k)
    (hB : ∀ k,k<K → ∀ i j,(i,j)∈allowed → s k i=t k j → |c i j|≤B k)
    (root : C 0) (hsroot : ∀ i,s 0 i=root) (htroot : ∀ j,t 0 j=root) :
    legalMaximumValue (activeResidualAllowed allowed σ active) c ≤
      (∑ b:C K,legalMaximumValue (spatialLegalBlock
        (activeResidualAllowed allowed σ active) (s K) (t K) b) c) +
      ∑ k∈Finset.range K,
        ((active.card:ℝ)-∑ b:C (k+1),(legalMaximumCard (spatialLegalBlock
          (activeResidualAllowed allowed σ active) (s (k+1)) (t (k+1)) b):ℝ)) *
            (2*((Fintype.card J+2:ℕ):ℝ)*B k) := by
  let tagS : Fin m → Option Unit := fun i ↦ if i∈active then some () else none
  let tagT : Fin n → Option Unit := fun j ↦ if j∈σ.freeCols then some () else none
  obtain ⟨lab,acc,hclass⟩ := activeResidualAllowed_exists_classes allowed σ active label allows hallowed
  have hactive : ∀ p∈activeResidualAllowed allowed σ active,
      (tagS p.1).isSome=true ∧ (tagT p.2).isSome=true := by
    intro p hp
    obtain ⟨hp,ha⟩ := Finset.mem_filter.mp hp
    have hc := (Finset.mem_filter.mp hp).2.2
    simp [tagS,tagT,ha,OTSelector.PartialMatching.freeCols,hc]
  have hcount : (∑ a:Unit,(blockSizeS tagS (some a):ℝ))=(active.card:ℝ) := by
    have heq : blockFinset tagS (some ())=active := by
      ext i
      simp [blockFinset,tagS]
    simp [blockSizeS,heq]
  have hv := legalMaximumValue_le_active_hierarchical_blocks_upto
    (activeResidualAllowed allowed σ active) tagS tagT hactive s t parent K hs ht
    lab acc hclass c B hB0
    (fun k hk i j hij hcell ↦ hB k hk i j
      (Finset.mem_filter.mp (Finset.mem_filter.mp hij).1).1 hcell)
    root hsroot htroot
  have hc : Fintype.card (Option (Option J)) = Fintype.card J + 2 := by
    simp only [Fintype.card_option]
  simpa only [hcount,hc] using hv


/-- The exact hierarchical residual rank budget, on the original indices and
spatial cells. Its coefficient comes from the original matrix, not a chosen
completion-cost bound. -/
def activeMatrixHierarchyBudget
    {q : ℕ} {C : ℕ → Type*} [∀ k,Fintype (C k)] [∀ k,DecidableEq (C k)]
    (allowed : Finset (Fin m × Fin n)) (σ : OTSelector.PartialMatching m n)
    (active : Finset (Fin m)) (s : (k:ℕ) → Fin m → C k)
    (t : (k:ℕ) → Fin n → C k) (K bins : ℕ) (Q : ℝ) (diam : ℕ → ℝ) : ℝ :=
  (∑ b:C K,(legalMaximumCard (spatialLegalBlock
    (activeResidualAllowed allowed σ active) (s K) (t K) b):ℝ)) *
      (Q*q*(diam K)^2) +
  ∑ k∈Finset.range K,
    ((active.card:ℝ)-∑ b:C (k+1),(legalMaximumCard (spatialLegalBlock
      (activeResidualAllowed allowed σ active) (s (k+1)) (t (k+1)) b):ℝ)) *
        (2*((bins+2:ℕ):ℝ)*(Q*q*(diam k)^2))

/-- The full original q-dimensional matrix kinetic entry at the actual
source and target coordinates. No scalar replacement of the matrix is made. -/
def carrierMatrixKinetic {q : ℕ}
    (A : (ℝ×ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  matrixQuadratic (A (source i,target j)) (y j-x i)

/-- The real coordinate diameter of a cell controls the original kinetic
entry, with the same matrix and every one of its q coordinates. -/
theorem abs_carrierMatrixKinetic_le_cell
    {q : ℕ} (A : (ℝ×ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ)
    {Q d : ℝ} (hQ : 0≤Q) (i : Fin m) (j : Fin n)
    (hquad : ∀ v,|matrixQuadratic (A (source i,target j)) v|≤Q*∑ l,v l^2)
    (hd : ∀ l,|y j l-x i l|≤d) :
    |carrierMatrixKinetic A source target x y i j|≤Q*q*d^2 := by
  have hsum : ∑ l,(y j l-x i l)^2 ≤ (q:ℝ)*d^2 := by
    calc
      _ ≤ ∑ _l:Fin q,d^2 := by
        apply Finset.sum_le_sum
        intro l _
        have h := hd l
        have hd0 : 0≤d := (abs_nonneg _).trans h
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hd0).mpr h
      _ = _ := by simp
  exact (hquad (y j-x i)).trans (by
    simpa only [Pi.sub_apply,mul_assoc] using mul_le_mul_of_nonneg_left hsum hQ)

/-- An explicit original-matrix cell bound turns the existing legal hierarchy
into a bound for the actual active residual value. -/
theorem activeResidualAllowed_matrix_value_le_budget
    {q : ℕ} {J : Type*} [Fintype J]
    {C : ℕ → Type*} [∀ k,Fintype (C k)] [∀ k,DecidableEq (C k)]
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n) (active : Finset (Fin m))
    (s : (k:ℕ) → Fin m → C k) (t : (k:ℕ) → Fin n → C k)
    (parent : (k:ℕ) → C (k+1) → C k) (K : ℕ)
    (hs : ∀ k,k<K → ∀ i,parent k (s (k+1) i)=s k i)
    (ht : ∀ k,k<K → ∀ j,parent k (t (k+1) j)=t k j)
    (label : Fin m → J) (allows : J → Fin n → Prop)
    (hallowed : ∀ i j,(i,j)∈scalarClockLegalGraph source target ↔ allows (label i) j)
    (A : (ℝ×ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ)
    {Q : ℝ} (hQ : 0≤Q)
    (hquad : ∀ i j,source i<target j → ∀ v,
      |matrixQuadratic (A (source i,target j)) v|≤Q*∑ l,v l^2)
    (diam : ℕ → ℝ)
    (hd : ∀ k,k≤K → ∀ i j,source i<target j → s k i=t k j →
      ∀ l,|y j l-x i l|≤diam k)
    (root : C 0) (hsroot : ∀ i,s 0 i=root) (htroot : ∀ j,t 0 j=root) :
    legalMaximumValue (activeResidualAllowed (scalarClockLegalGraph source target) σ active)
      (carrierMatrixKinetic A source target x y) ≤
    activeMatrixHierarchyBudget (q:=q) (scalarClockLegalGraph source target) σ active
      s t K (Fintype.card J) Q diam := by
  let G := activeResidualAllowed (scalarClockLegalGraph source target) σ active
  let c := carrierMatrixKinetic A source target x y
  let B : ℕ → ℝ := fun k ↦ Q*q*(diam k)^2
  have hB (k : ℕ) (hk : k≤K) (i : Fin m) (j : Fin n)
      (hij : (i,j)∈scalarClockLegalGraph source target) (hcell : s k i=t k j) :
      |c i j|≤B k := by
    have hf : source i<target j := (Finset.mem_filter.mp hij).2
    exact abs_carrierMatrixKinetic_le_cell A source target x y hQ i j
      (hquad i j hf) (hd k hk i j hf hcell)
  have hv := activeResidualAllowed_value_le_hierarchy
    (scalarClockLegalGraph source target) σ active s t parent K hs ht label allows
    hallowed c B (fun k ↦ by dsimp [B]; positivity)
    (fun k hk ↦ hB k (Nat.le_of_lt hk)) root hsroot htroot
  have hleaf (b:C K) :
      legalMaximumValue (spatialLegalBlock G (s K) (t K) b) c ≤
      (legalMaximumCard (spatialLegalBlock G (s K) (t K) b):ℝ)*B K := by
    refine (le_abs_self _).trans (abs_legalMaximumValue_le_of_allowed _ c ?_)
    intro i j hij
    obtain ⟨hg,hi,hj⟩ := Finset.mem_filter.mp hij
    have horig := (Finset.mem_filter.mp (Finset.mem_filter.mp hg).1).1
    exact hB K le_rfl i j horig (hi.trans hj.symm)
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun b _ ↦ hleaf b)
  rw [← Finset.sum_mul] at hsum
  exact hv.trans (add_le_add hsum le_rfl)

/-- Optimizing only the kinetic part charges the bounded probe exactly once
per actual added edge, independently of hierarchy depth or class count. -/
theorem cost_tilt_le_cost_add_card_probe
    (δ : OTSelector.PartialMatching m n) (c g : Fin m → Fin n → ℝ)
    {G : ℝ} (hg : ∀ i j,|g i j|≤G) (tilt : ℝ) :
    δ.cost (fun i j ↦ c i j+tilt*g i j) ≤
      δ.cost c+|tilt| *G*δ.card := by
  have hprobe (i j) : tilt*g i j≤|tilt| *G :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hg i j) (abs_nonneg tilt))
  calc
    _ ≤ ∑ e∈δ.edges,(c e.1 e.2+|tilt| *G) :=
      Finset.sum_le_sum (fun e _ ↦ add_le_add le_rfl (hprobe e.1 e.2))
    _ = _ := by
      simp only [OTSelector.PartialMatching.cost,Finset.sum_add_distrib,
        Finset.sum_const,nsmul_eq_mul,OTSelector.PartialMatching.card]
      ring


/-- Compact original clocks and the original matrix produce constants uniform
in the actual point counts, core, spatial depth and window size. The residual
is selected on the literal free carrier rows and unused target columns.
The right side is an explicit sum of their actual spatial legal ranks. -/
theorem exists_uniform_original_matrix_carrier_completion
    {q : ℕ} {I : Set ℝ} {gap : ℝ} (hI : IsCompact I) (hgap : 0<gap)
    {region : Set (ℝ×ℝ)} (hr : IsCompact region)
    (A : (ℝ×ℝ) → Matrix (Fin q) (Fin q) ℝ) (hA : ContinuousOn A region) :
    ∃ bins : ℕ, ∃ Q≥0,
    ∀ {m n : ℕ} (source : Fin m → ℝ) (target : Fin n → ℝ),
    (∀ i,source i∈I) → (∀ i j,gap≤|target j-source i|) →
    (∀ i j,source i<target j → (source i,target j)∈region) →
    ∀ (σ ρ : OTSelector.PartialMatching m n),
    IsLegal (scalarClockLegalGraph source target) σ →
    ∀ (active : Finset (Fin m)),
    IsLegal (residualAllowed (scalarClockLegalGraph source target) σ) ρ →
    ρ.rows=active →
    ∀ (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ)
    {C : ℕ → Type*} [∀ k,Fintype (C k)] [∀ k,DecidableEq (C k)]
    (s : (k:ℕ) → Fin m → C k) (t : (k:ℕ) → Fin n → C k)
    (parent : (k:ℕ) → C (k+1) → C k) (K : ℕ),
    (∀ k,k<K → ∀ i,parent k (s (k+1) i)=s k i) →
    (∀ k,k<K → ∀ j,parent k (t (k+1) j)=t k j) →
    ∀ (diam : ℕ → ℝ),
    (∀ k,k≤K → ∀ i j,source i<target j → s k i=t k j →
      ∀ l,|y j l-x i l|≤diam k) →
    ∀ (root : C 0), (∀ i,s 0 i=root) → (∀ j,t 0 j=root) →
    ∀ (g : Fin m → Fin n → ℝ) (G : ℝ), (∀ i j,|g i j|≤G) → ∀ tilt : ℝ,
    ∃ τ δ : OTSelector.PartialMatching m n,
      IsLegal (scalarClockLegalGraph source target) τ ∧ σ.edges⊆τ.edges ∧
      IsLegal (residualAllowed (scalarClockLegalGraph source target) σ) δ ∧
      δ.rows=active ∧ δ.card=active.card ∧ τ.edges=σ.edges∪δ.edges ∧
      τ.card=σ.card+active.card ∧
      δ.cost (carrierMatrixKinetic A source target x y) ≤
        activeMatrixHierarchyBudget (q:=q) (scalarClockLegalGraph source target) σ active
          s t K bins Q diam ∧
      τ.cost (fun i j ↦ carrierMatrixKinetic A source target x y i j+tilt*g i j) ≤
        σ.cost (fun i j ↦ carrierMatrixKinetic A source target x y i j+tilt*g i j) +
        activeMatrixHierarchyBudget (q:=q) (scalarClockLegalGraph source target) σ active
          s t K bins Q diam + |tilt| * G*active.card := by
  obtain ⟨D⟩ := exists_finiteScalarBins hI hgap
  obtain ⟨Q,hQ,hquad⟩ := exists_compact_matrixQuadratic_sum_bound hr hA
  refine ⟨D.count,Q,hQ,?_⟩
  intro m n source target hsource hsep hpairs σ ρ hσ active hρ hrows x y
    C _ _ s t parent K hs ht diam hd root hsroot htroot g G hg tilt
  obtain ⟨label,allows,hallowed⟩ := D.exists_source_neighborhood_classes hgap source target
    hsource hsep
  let c := carrierMatrixKinetic A source target x y
  obtain ⟨τ,δ,hτ,hsub,hδ,hdrows,hdcard,hedges,htcard,hdcost,_⟩ :=
    exists_minCost_active_completion (scalarClockLegalGraph source target) σ ρ hσ
      active hρ hrows c
  have hbudget : δ.cost c ≤ activeMatrixHierarchyBudget (q:=q)
      (scalarClockLegalGraph source target) σ active s t K D.count Q diam := by
    rw [hdcost]
    simpa only [Fintype.card_fin] using activeResidualAllowed_matrix_value_le_budget
      source target σ active s t parent K hs ht label allows hallowed A x y hQ
      (fun i j hij ↦ hquad (source i,target j) (hpairs i j hij)) diam hd root hsroot htroot
  obtain ⟨hrow,hcol⟩ := residualAllowed_disjoint σ δ hδ
  have heq (z : Fin m → Fin n → ℝ) : τ.cost z=(σ.union δ hrow hcol).cost z := by
    unfold OTSelector.PartialMatching.cost
    rw [hedges]
    rfl
  refine ⟨τ,δ,hτ,hsub,hδ,hdrows,hdcard,hedges,htcard,hbudget,?_⟩
  rw [heq,OTSelector.PartialMatching.cost_union]
  have hprobe := cost_tilt_le_cost_add_card_probe δ c g hg tilt
  rw [hdcard] at hprobe
  dsimp only [c] at hprobe hbudget
  linarith


/-- The canonical cell tag selects only the actual active original sources. -/
def activeSpatialSourceTag {Cell : Type*} (active : Finset (Fin m))
    (s : Fin m → Cell) (i : Fin m) : Option Cell :=
  if i∈active then some (s i) else none

/-- The target tag selects only actual unused original target columns. -/
def freeSpatialTargetTag {Cell : Type*} (σ : OTSelector.PartialMatching m n)
    (t : Fin n → Cell) (j : Fin n) : Option Cell :=
  if j∈σ.freeCols then some (t j) else none

/-- Each hierarchy child is exactly the strict-clock graph on its genuine
active-source and unused-target subclouds, with the original indices retained.
No iid assertion is made for these adaptively selected subclouds. -/
theorem activeResidualAllowed_spatial_rank_eq_actual_clock_subcloud
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n) (active : Finset (Fin m))
    (ha : active⊆σ.freeRows) (s : Fin m → Cell) (t : Fin n → Cell) (b : Cell) :
    legalMaximumCard (spatialLegalBlock
      (activeResidualAllowed (scalarClockLegalGraph source target) σ active) s t b) =
    legalMaximumCard (scalarClockLegalGraph
      (source ∘ spatialSourceEmbedding (activeSpatialSourceTag active s) (some b))
      (target ∘ spatialTargetEmbedding (freeSpatialTargetTag σ t) (some b))) := by
  let S := activeSpatialSourceTag active s
  let T := freeSpatialTargetTag σ t
  have hs (i : Fin m) : S i=some b ↔ i∈active ∧ s i=b := by
    by_cases hi : i∈active <;> simp [S,activeSpatialSourceTag,hi]
  have ht (j : Fin n) : T j=some b ↔ j∈σ.freeCols ∧ t j=b := by
    by_cases hj : j∈σ.freeCols <;> simp [T,freeSpatialTargetTag,hj]
  have heq : spatialLegalBlock
      (activeResidualAllowed (scalarClockLegalGraph source target) σ active) s t b =
      spatialLegalBlock (scalarClockLegalGraph source target) S T (some b) := by
    ext p
    simp only [spatialLegalBlock,activeResidualAllowed,residualAllowed,Finset.mem_filter,
      scalarClockLegalGraph,Finset.mem_univ,true_and,hs,ht,
      OTSelector.PartialMatching.freeCols,Finset.mem_sdiff]
    have hf : p.1∈active → p.1∉σ.rows := fun h ↦ (Finset.mem_sdiff.mp (ha h)).2
    tauto
  rw [heq,legalMaximumCard_spatialLegalBlock_eq,inducedLegalGraph_scalarClockLegalGraph]

/-- Child legal rank never exceeds the number of actual active sources in
that child. Original used rows are absent from this bound. -/
theorem activeResidualAllowed_spatial_rank_le_ports
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (allowed : Finset (Fin m × Fin n)) (σ : OTSelector.PartialMatching m n)
    (active : Finset (Fin m)) (s : Fin m → Cell) (t : Fin n → Cell) (b : Cell) :
    legalMaximumCard (spatialLegalBlock (activeResidualAllowed allowed σ active) s t b) ≤
      (active.filter (fun i ↦ s i=b)).card := by
  obtain ⟨ρ,hρ,hcard⟩ := exists_legalMaximumCard
    (spatialLegalBlock (activeResidualAllowed allowed σ active) s t b)
  rw [← hcard,← ρ.card_rows]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨hg,hcell,_⟩ := Finset.mem_filter.mp (hρ hp)
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).2,hcell⟩

/-- Every hierarchy deficiency is exactly the sum of actual per-child active
source deficiencies. This identity exposes the local stochastic estimate
still required to send the normalized added transport cost to zero. -/
theorem activeResidualAllowed_deficit_eq_sum_local_ports
    {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (allowed : Finset (Fin m × Fin n)) (σ : OTSelector.PartialMatching m n)
    (active : Finset (Fin m)) (s : Fin m → Cell) (t : Fin n → Cell) :
    (active.card:ℝ)-∑ b:Cell,(legalMaximumCard
      (spatialLegalBlock (activeResidualAllowed allowed σ active) s t b):ℝ) =
    ∑ b:Cell,(((active.filter (fun i ↦ s i=b)).card-
      legalMaximumCard (spatialLegalBlock
        (activeResidualAllowed allowed σ active) s t b):ℕ):ℝ) := by
  have hc : active.card=∑ b:Cell,(active.filter (fun i ↦ s i=b)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)
  simp_rw [Nat.cast_sub (activeResidualAllowed_spatial_rank_le_ports allowed σ active s t _)]
  rw [Finset.sum_sub_distrib]
  simp_rw [← Nat.cast_sum]
  rw [← hc]

end PartialMatching
end OTSelector.Reconstruction
