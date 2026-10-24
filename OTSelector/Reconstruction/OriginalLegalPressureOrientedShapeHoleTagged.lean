import OTSelector.Reconstruction.TaggedDyadicEnergyRate
import OTSelector.Reconstruction.FinslerRelativeLawSelectedHierarchyMatching
import OTSelector.Reconstruction.MarkedStationaryValueLegalScalarRepair

/-! Genuine typed hierarchies repair arbitrary spatial laws to the actual scalar legal maximum. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace OTSelector.Reconstruction

/-- A common genuine type-coordinate law need not have any spatial density.
The actual same-type hierarchy core is legal and finite scalar augmentation
repairs it to the original graph's true maximum, paying only iid count defects. -/
theorem originalShapeHole_integral_legalMaximumValue_le_of_tagged_iid
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n : ℕ} (hq : 4 < q)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (law : Measure (T × DyadicUnitCube q)) [IsProbabilityMeasure law]
    (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = law) (hyl : ∀ i, P.map (ys i) = law)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω i ↦ ys i ω) P)
    {I : Set ℝ} {gap : ℝ} (bins : FiniteScalarBins I gap) (hgap : 0 < gap)
    (source target : Fin n → Ω → ℝ)
    (hsource : ∀ i, Measurable (source i)) (htarget : ∀ j, Measurable (target j))
    (hcover : ∀ᵐ ω ∂P, ∀ i, source i ω ∈ I)
    (hsep : ∀ᵐ ω ∂P, ∀ i j, gap ≤ |target j ω-source i ω|)
    (hlegal : ∀ᵐ ω ∂P, ∀ i j, (xs i ω).1 = (ys j ω).1 → source i ω < target j ω)
    (cost : Ω → Fin n → Fin n → ℝ) (hc : ∀ i j, Measurable (fun ω ↦ cost ω i j))
    {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hcn : ∀ᵐ ω ∂P, ∀ i j, 0 ≤ cost ω i j)
    (hbound : ∀ᵐ ω ∂P, ∀ i j, cost ω i j ≤ B)
    (hquadratic : ∀ t, ∀ᵐ ω ∂P, ∀ i j, (xs i ω).1 = t → (ys j ω).1 = t →
      cost ω i j ≤ C*‖dyadicCubePoint (xs i ω).2-dyadicCubePoint (ys j ω).2‖^2) :
    let value := fun ω ↦ PartialMatching.legalMaximumValue
      (scalarClockLegalGraph (fun i ↦ source i ω) (fun j ↦ target j ω)) (cost ω)
    Integrable value P ∧ (∫ ω,value ω ∂P) ≤
      C*dyadicMatchingConstant q*(Fintype.card T : ℝ)^(2/(q : ℝ))*(n : ℝ)^(1-2/(q : ℝ)) +
        (B+2*((bins.count : ℝ)+1)*B)*Real.sqrt (2*(n : ℝ)*Fintype.card T) := by
  classical
  dsimp only
  have hm (t : T) : MeasurableSet {x : T × DyadicUnitCube q | x.1 = t} :=
    measurable_fst (measurableSet_singleton t)
  have hmass : (∑ t : T,law.real {x | x.1 = t}) = 1 := by
    simpa [Set.preimage,Set.mem_singleton_iff] using
      sum_measureReal_preimage_singleton (μ := law) Finset.univ (f := Prod.fst) (fun t _ ↦ hm t)
  obtain ⟨K,hEI,hE⟩ := exists_taggedHierarchy_smallMass_energy hq P law xs ys hx hy hxi hyi hxl hyl hxy
    Finset.univ cost hc hC hB hmass hcn hbound (fun t _ ↦ hquadratic t)
  let energy := fun ω ↦ attributedTypesEnergy Finset.univ (fun i ↦ xs i ω) (fun j ↦ ys j ω)
    (cost ω) (taggedHierarchyAssignment K xs ys ω)
  let defect := fun ω ↦ ∑ t : T, |partitionCount (fun i ↦ (xs i ω).1) t-partitionCount (fun j ↦ (ys j ω).1) t|
  obtain ⟨hDI,hD⟩ := iidTypeCount_total_difference_bound P law law xs ys hx hy hxi hyi hxl hyl hxy
    (fun t : T ↦ {x | x.1 = t}) (fun t ↦ {x | x.1 = t}) hm hm (fun _ ↦ rfl) hmass
  have hdEq : (fun ω ↦ ∑ t : T, |iidTypeCount xs {x | x.1 = t} ω-iidTypeCount ys {x | x.1 = t} ω|) = defect := by
    funext ω
    simp only [defect,partitionCount_tag_eq_iidTypeCount]
  rw [hdEq] at hDI hD
  simp only [mul_one] at hD
  let A := 2*((bins.count : ℝ)+1)*B
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hvalueI : Integrable (fun ω ↦ PartialMatching.legalMaximumValue
      (scalarClockLegalGraph (fun i ↦ source i ω) (fun j ↦ target j ω)) (cost ω)) P := by
    apply Integrable.of_bound (PartialMatching.measurable_legalMaximumValue _
      (measurableSet_scalarClockLegalGraph_eq source target hsource htarget) cost hc).aestronglyMeasurable ((n : ℝ)*B)
    filter_upwards [hcn,hbound] with ω hn hb
    rw [Real.norm_eq_abs]
    simpa only [min_self] using PartialMatching.abs_legalMaximumValue_le_min _ (cost ω) hB
      (fun i j ↦ by rw [abs_of_nonneg (hn i j)]; exact hb i j)
  refine ⟨hvalueI,?_⟩
  have hpoint : ∀ᵐ ω ∂P, PartialMatching.legalMaximumValue
      (scalarClockLegalGraph (fun i ↦ source i ω) (fun j ↦ target j ω)) (cost ω) ≤ energy ω+A*defect ω := by
    filter_upwards [hcover,hsep,hlegal,hcn,hbound] with ω hcover hsep hlegal hn hb
    let x := fun i ↦ xs i ω
    let y := fun j ↦ ys j ω
    let full := taggedHierarchyAssignment K xs ys ω
    let σ := selectedSameTypeMatching Finset.univ (fun i ↦ (x i).1) (fun j ↦ (y j).1) full
    have hσ : PartialMatching.IsLegal (scalarClockLegalGraph (fun i ↦ source i ω) (fun j ↦ target j ω)) σ := by
      intro e he
      have htag := selectedSameTypeMatching_mem Finset.univ (fun i ↦ (x i).1) (fun j ↦ (y j).1) full he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlegal e.1 e.2 htag.2.2⟩
    have hsat := taggedHierarchy_type_no_opposite x y (firstOptimalAssignment_isOptimal (taggedHierarchyCost K x y))
    have hdef := selectedSameTypeMatching_source_defect_le Finset.univ (fun i ↦ (x i).1) (fun j ↦ (y j).1) full hsat
    have hsum : (∑ t : T,partitionCount (fun i ↦ (x i).1) t) = (n : ℝ) := by
      unfold partitionCount
      rw [Finset.sum_comm]
      simp [partitionIndicator]
    simp only [hsum] at hdef
    have hcard := PartialMatching.card_le_legalMaximumCard hσ
    have hmax : PartialMatching.legalMaximumCard (scalarClockLegalGraph (fun i ↦ source i ω) (fun j ↦ target j ω)) ≤ n := by
      simpa only [min_self] using PartialMatching.legalMaximumCard_le_min (scalarClockLegalGraph (fun i ↦ source i ω) (fun j ↦ target j ω))
    have hmissing : ((PartialMatching.legalMaximumCard (scalarClockLegalGraph (fun i ↦ source i ω) (fun j ↦ target j ω))-σ.card : ℕ) : ℝ) ≤ defect ω := by
      rw [Nat.cast_sub hcard]
      have hmR : (PartialMatching.legalMaximumCard (scalarClockLegalGraph (fun i ↦ source i ω) (fun j ↦ target j ω)) : ℝ) ≤ n := Nat.cast_le.mpr hmax
      dsimp only [σ,x,y] at hdef
      linarith only [hmR,hdef]
    have hcE := selectedSameTypeMatching_cost_le_attributed Finset.univ x y full (cost ω) hn
    have hv := bins.legalMaximumValue_le_cost_add_deficit hgap (fun i ↦ source i ω) (fun j ↦ target j ω)
      hcover hsep σ hσ (cost ω) hB (fun i j ↦ by rw [abs_of_nonneg (hn i j)]; exact hb i j)
    have hcoef : (2*(bins.count : ℝ)-1)*B ≤ A := by dsimp only [A]; nlinarith
    have hrepair : (((PartialMatching.legalMaximumCard (scalarClockLegalGraph (fun i ↦ source i ω) (fun j ↦ target j ω))-σ.card : ℕ) : ℝ) *
        ((2*(bins.count : ℝ)-1)*B)) ≤ A*defect ω :=
      (mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg _)).trans
        ((mul_le_mul_of_nonneg_right hmissing hA).trans_eq (mul_comm _ _))
    exact hv.trans (add_le_add hcE hrepair)
  calc
    _ ≤ ∫ ω,energy ω+A*defect ω ∂P := integral_mono_ae hvalueI (hEI.add (hDI.const_mul A)) hpoint
    _ = (∫ ω,energy ω ∂P)+A*(∫ ω,defect ω ∂P) := by rw [integral_add hEI (hDI.const_mul A),integral_const_mul]
    _ ≤ C*dyadicMatchingConstant q*(Fintype.card T : ℝ)^(2/(q : ℝ))*(n : ℝ)^(1-2/(q : ℝ)) +
        B*Real.sqrt (2*(n : ℝ)*Fintype.card T)+A*Real.sqrt (2*(n : ℝ)*Fintype.card T) := by
      apply add_le_add
      · simpa only [Finset.card_univ,mul_one] using hE
      · exact mul_le_mul_of_nonneg_left hD hA
    _ = _ := by dsimp only [A]; ring

end OTSelector.Reconstruction
