import OTSelector.Reconstruction.FinslerConcreteUpperClassActive
import OTSelector.Reconstruction.MarkedStationaryValueLegalActiveGridExpectation

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
/-! Concrete common paired-class specialization of the original active grid
expectation. Every class, activity, support, and edge-cost hypothesis is produced
from the literal original law and allowed coefficient bounds. -/
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
local instance pairedGridExpectationOptionMeasurableSpace (T : Type*) :
    MeasurableSpace (Option T) := ⊤
local instance pairedGridExpectationOptionMeasurableSingleton (T : Type*) :
    MeasurableSingletonClass (Option T) := ⟨fun _ ↦ trivial⟩

variable {X I J : Type*} [MeasurableSpace X] [Fintype I] [Fintype J]
  [MeasurableSpace I] [MeasurableSpace J]
  [MeasurableSingletonClass I] [MeasurableSingletonClass J]

/-- The literal class kinetic and probe edge cost, at the actual retained
count scale and on the unchanged coordinate difference. -/
def pairedClassScaledEdgeCost {q : ℕ} (z : X → Fin q → ℝ)
    (kin : I → J → (Fin q → ℝ) → ℝ) (probe : I → J → ℝ)
    (scale tilt : ℝ) (x y : X × (I × J)) : ℝ :=
  scale * kin x.2.1 y.2.2 (z y.1 - z x.1) + tilt * probe x.2.1 y.2.2

/-- Original coordinate and coefficient measurability make the true signed
class edge cost measurable before any matching is selected. -/
theorem measurable_pairedClassScaledEdgeCost {q : ℕ}
    {z : X → Fin q → ℝ} (hz : Measurable z)
    {kin : I → J → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : I × J ↦ kin p.1 p.2)))
    {probe : I → J → ℝ} (hg : Measurable (Function.uncurry probe)) (scale tilt : ℝ) :
    Measurable (Function.uncurry (pairedClassScaledEdgeCost z kin probe scale tilt)) := by
  have hs : Measurable (fun p : (X × (I × J)) × (X × (I × J)) ↦ p.1.2.1) := by
    fun_prop
  have ht : Measurable (fun p : (X × (I × J)) × (X × (I × J)) ↦ p.2.2.2) := by
    fun_prop
  have hclass := hs.prodMk ht
  have hdisp : Measurable (fun p : (X × (I × J)) × (X × (I × J)) ↦
      z p.2.1 - z p.1.1) :=
    (hz.comp (measurable_fst.comp measurable_snd)).sub
      (hz.comp (measurable_fst.comp measurable_fst))
  exact ((hk.comp (hclass.prodMk hdisp)).const_mul scale).add
    ((hg.comp hclass).const_mul tilt)

/-- Allowed quadratic and probe bounds control the actual unclamped coordinate
edge cost at its own original count scale. -/
theorem abs_pairedClassScaledEdgeCost_le {q : ℕ}
    (z : X → Fin q → ℝ) (allowed : I → J → Prop)
    (kin : I → J → (Fin q → ℝ) → ℝ) (probe : I → J → ℝ)
    {K G scale : ℝ} (hscale : 0 ≤ scale)
    (hkb : ∀ i j, allowed i j → ∀ v, |kin i j v| ≤ K * ∑ l, (v l) ^ 2)
    (hgb : ∀ i j, allowed i j → |probe i j| ≤ G)
    (tilt : ℝ) (x y : X × (I × J)) (hxy : allowed x.2.1 y.2.2) :
    |pairedClassScaledEdgeCost z kin probe scale tilt x y| ≤
      scale * (K * ∑ l, (z x.1 l - z y.1 l) ^ 2) + |tilt| * G := by
  have hsum : (∑ l, ((z y.1 - z x.1) l) ^ 2) =
      ∑ l, (z x.1 l - z y.1 l) ^ 2 := by
    apply Finset.sum_congr rfl
    intro l _
    simp only [Pi.sub_apply]
    ring
  unfold pairedClassScaledEdgeCost
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg hscale]
    exact mul_le_mul_of_nonneg_left ((hkb _ _ hxy _).trans_eq (by rw [hsum])) hscale
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hgb _ _ hxy) (abs_nonneg tilt)

/-- The actual paired-class model obeys the original active legal grid mean
bound. Its type count is precisely the product of the two finite class counts;
its row classes are the active source classes together with inactivity. -/
theorem integral_pairedClass_active_grid_value_div_le
    {Ω : Type*} [MeasurableSpace Ω]
    (q m depth N : ℕ) (hq : 4 < q) (hN : 0 < N)
    (hm : 0 < m) (hdepth : m ≤ 2 ^ depth) (hdepth2 : 2 ^ depth ≤ 2 * m)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (P₀ : I → J → ℝ) (hP₀ : ∀ i j, 0 ≤ P₀ i j)
    (hmassP : 0 < ∑ i, ∑ j, P₀ i j)
    (mask : I → J → Prop) (hzero : ∀ i j, ¬mask i j → P₀ i j = 0)
    (xs ys : Fin N → Ω → X × (I × J))
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ.prod (clockClassJointProbability P₀ hP₀ hmassP : Measure _))
    (hyl : ∀ i, P.map (ys i) = μ.prod (clockClassJointProbability P₀ hP₀ hmassP : Measure _))
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω j ↦ ys j ω) P)
    (θ : X → Option Unit) (hθ : Measurable θ)
    (z : X → Fin q → ℝ) (hz : Measurable z)
    (hunit : ∀ᵐ x ∂μ, (θ x).isSome = true → z x ∈ unitCube q)
    (kin : I → J → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : I × J ↦ kin p.1 p.2)))
    (probe : I → J → ℝ) (hg : Measurable (Function.uncurry probe))
    {density K G tilt : ℝ} (hd : 0 ≤ density)
    (hmass : μ.real {x | (θ x).isSome = true} ≤ density) (hK : 0 ≤ K) (hG : 0 ≤ G)
    (hkb : ∀ i j, mask i j → ∀ v, |kin i j v| ≤ K * ∑ l, (v l) ^ 2)
    (hgb : ∀ i j, mask i j → |probe i j| ≤ G) :
    let graph := fun ω ↦ pairedClassActiveGraph θ mask
      (fun i ↦ xs i ω) (fun j ↦ ys j ω)
    let cost := fun ω i j ↦ pairedClassScaledEdgeCost z kin probe
      (((N : ℝ) * density) ^ (2 / (q : ℝ))) tilt (xs i ω) (ys j ω)
    (∫ ω, PartialMatching.legalMaximumValue (graph ω) (cost ω) ∂P) / N ≤
      (∫ ω, ∑ b : Fin q → Fin (2 ^ depth + 1), PartialMatching.legalMaximumValue
        (PartialMatching.spatialLegalBlock (graph ω)
          (fun i ↦ gridCellLabel q m depth depth hm hdepth (z (xs i ω).1))
          (fun j ↦ gridCellLabel q m depth depth hm hdepth (z (ys j ω).1)) b)
        (cost ω) ∂P) / N +
      activeGridRepairError q
        (legalGridRepairConstant q (Fintype.card I + 1) (Fintype.card I * Fintype.card J))
        K G tilt density ((N : ℝ) / (m : ℝ) ^ q) := by
  classical
  let π := clockClassJointProbability P₀ hP₀ hmassP
  let ρ := μ.prod (π : Measure (I × J))
  let tag := pairedClassTag (I := I) (J := J) θ
  let graph := fun ω ↦ pairedClassActiveGraph θ mask (fun i ↦ xs i ω) (fun j ↦ ys j ω)
  let cost := fun ω i j ↦ pairedClassScaledEdgeCost z kin probe
    (((N : ℝ) * density) ^ (2 / (q : ℝ))) tilt (xs i ω) (ys j ω)
  have hxl' (i : Fin N) : P.map (xs i) = ρ := hxl i
  have hyl' (j : Fin N) : P.map (ys j) = ρ := hyl j
  have hmapS : ρ.map Prod.fst = μ := by simp [ρ]
  have hmapT : ρ.map Prod.snd = (π : Measure (I × J)) := by simp [ρ]
  have hρlegal : ∀ᵐ w ∂ρ, mask w.2.1 w.2.2 := by
    have hπlegal : ∀ᵐ p ∂(π : Measure (I × J)), mask p.1 p.2 :=
      normalizedClockClassPairMeasure_legal P₀ mask hzero
    rw [← hmapT] at hπlegal
    exact ae_of_ae_map measurable_snd.aemeasurable hπlegal
  have hown (i : Fin N) : ∀ᵐ ω ∂P, mask (xs i ω).2.1 (xs i ω).2.2 := by
    have h := hρlegal
    rw [← hxl' i] at h
    exact ae_of_ae_map (hx i).aemeasurable h
  have hρunit : ∀ᵐ w ∂ρ, (θ w.1).isSome = true → z w.1 ∈ unitCube q := by
    have h := hunit
    rw [← hmapS] at h
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have huS (i : Fin N) : ∀ᵐ ω ∂P,
      (θ (xs i ω).1).isSome = true → z (xs i ω).1 ∈ unitCube q := by
    have h := hρunit
    rw [← hxl' i] at h
    exact ae_of_ae_map (hx i).aemeasurable h
  have huT (j : Fin N) : ∀ᵐ ω ∂P,
      (θ (ys j ω).1).isSome = true → z (ys j ω).1 ∈ unitCube q := by
    have h := hρunit
    rw [← hyl' j] at h
    exact ae_of_ae_map (hy j).aemeasurable h
  have hact : ∀ᵐ ω ∂P, ∀ e ∈ graph ω,
      (tag (xs e.1 ω)).isSome = true ∧ (tag (ys e.2 ω)).isSome = true := by
    filter_upwards with ω
    intro e he
    have h := (mem_pairedClassActiveGraph θ mask _ _ e).mp he
    exact ⟨by simpa only [tag, pairedClassTag_isSome] using h.1,
      by simpa only [tag, pairedClassTag_isSome] using h.2.1⟩
  have hleg : ∀ᵐ ω ∂P, ∀ i j a, tag (xs i ω) = some a → tag (ys j ω) = some a →
      (i, j) ∈ graph ω := by
    filter_upwards [pairedClassActiveGraph_same_type_ae P θ mask xs ys hown] with ω hω
    exact fun i j a hi hj ↦ (hω i j a hi hj).1
  have hunit' : ∀ᵐ ω ∂P, ∀ e ∈ graph ω,
      z (xs e.1 ω).1 ∈ unitCube q ∧ z (ys e.2 ω).1 ∈ unitCube q := by
    filter_upwards [ae_all_iff.mpr huS, ae_all_iff.mpr huT] with ω hs ht
    intro e he
    have h := (mem_pairedClassActiveGraph θ mask _ _ e).mp he
    exact ⟨hs e.1 h.1, ht e.2 h.2.1⟩
  have hmass' : ρ.real {x | (tag x).isSome = true} ≤ density := by
    have hset : {x : X × (I × J) | (tag x).isSome = true} =
        {x | (θ x).isSome = true} ×ˢ (univ : Set (I × J)) := by
      ext x
      simp only [tag, pairedClassTag_isSome, mem_ofPred_eq, mem_prod, mem_univ, and_true]
    rw [hset]
    change (μ.prod (π : Measure (I × J))).real _ ≤ density
    rw [measureReal_prod_prod]
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using hmass
  have hcost : ∀ᵐ ω ∂P, ∀ i j, (i, j) ∈ graph ω → |cost ω i j| ≤
      ((N : ℝ) * density) ^ (2 / (q : ℝ)) *
        (K * ∑ l, (z (xs i ω).1 l - z (ys j ω).1 l) ^ 2) + |tilt| * G := by
    filter_upwards with ω
    intro i j hij
    exact abs_pairedClassScaledEdgeCost_le z mask kin probe
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) hd) _)
      hkb hgb tilt (xs i ω) (ys j ω)
      ((mem_pairedClassActiveGraph θ mask _ _ (i, j)).mp hij).2.2
  have h := integral_active_legal_grid_value_div_le_of_common_type
    (T := Unit × (I × J)) (J := Option I)
    q m depth N hq hN hm hdepth hdepth2 P ρ xs ys hx hy hxi hyi hxl hyl hxy
    tag (measurable_pairedClassTag hθ) (fun x ↦ z x.1) (hz.comp measurable_fst)
    graph (measurableSet_mem_pairedClassActiveGraph hθ mask xs ys hx hy)
    hact hleg hunit' (fun ω i ↦ pairedClassActiveSourceClass θ (xs i ω))
    (fun ω ↦ pairedClassActiveSourceAllows θ mask (fun j ↦ ys j ω))
    (fun ω i j ↦ pairedClassActiveGraph_row_factorization θ mask _ _ i j)
    cost (fun i j ↦ (measurable_pairedClassScaledEdgeCost hz hk hg _ _).comp
      ((hx i).prodMk (hy j))) hd hmass' hK hG hcost
  simpa only [Fintype.card_option, Fintype.card_prod, Fintype.card_unit, one_mul] using h

end OTSelector.Reconstruction
