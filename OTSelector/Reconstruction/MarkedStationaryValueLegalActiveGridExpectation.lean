import OTSelector.Reconstruction.MarkedStationaryValueLegalActiveGridGeometry
import OTSelector.Reconstruction.MarkedStationaryValueLegalActiveRefinement

/-! Original iid active legal grid comparison from one original shared type law
and the original coordinate quadratic cost. All level masses and parent budgets
are produced internally. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

local instance activeGridExpectationOptionMeasurableSpace (T : Type*) :
    MeasurableSpace (Option T) := ⊤
local instance activeGridExpectationOptionMeasurableSingleton (T : Type*) :
    MeasurableSingletonClass (Option T) := ⟨fun _ ↦ trivial⟩

/-- The original normalized active legal value is bounded by the actual leaf
values and a vanishing parent-scale repair error. Arbitrary shape laws and zero
mass types are allowed, and only original allowed endpoints need lie in the cube. -/
theorem integral_active_legal_grid_value_div_le_of_common_type
    {Ω X T J : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Fintype T] [DecidableEq T]
    [Fintype J]
    (q m depth N : ℕ) (hq : 4 < q) (hN : 0 < N)
    (hm : 0 < m) (hdepth : m ≤ 2 ^ depth) (hdepth2 : 2 ^ depth ≤ 2 * m)
    (P : Measure Ω) [IsProbabilityMeasure P] (ρ : Measure X) [IsProbabilityMeasure ρ]
    (xs ys : Fin N → Ω → X)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = ρ) (hyl : ∀ i, P.map (ys i) = ρ)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω j ↦ ys j ω) P)
    (tag : X → Option T) (htag : Measurable tag)
    (z : X → Fin q → ℝ) (hz : Measurable z)
    (allowed : Ω → Finset (Fin N × Fin N))
    (ha : ∀ e, MeasurableSet {ω | e ∈ allowed ω})
    (hactive : ∀ᵐ ω ∂P, ∀ e ∈ allowed ω,
      (tag (xs e.1 ω)).isSome = true ∧ (tag (ys e.2 ω)).isSome = true)
    (hlegal : ∀ᵐ ω ∂P, ∀ i j a, tag (xs i ω) = some a → tag (ys j ω) = some a →
      (i, j) ∈ allowed ω)
    (hunit : ∀ᵐ ω ∂P, ∀ e ∈ allowed ω,
      z (xs e.1 ω) ∈ unitCube q ∧ z (ys e.2 ω) ∈ unitCube q)
    (sourceClass : Ω → Fin N → J) (sourceAllows : Ω → J → Fin N → Prop)
    (hallowed : ∀ ω i j, (i, j) ∈ allowed ω ↔ sourceAllows ω (sourceClass ω i) j)
    (c : Ω → Fin N → Fin N → ℝ) (hc : ∀ i j, Measurable (fun ω ↦ c ω i j))
    {density C G t : ℝ} (hd : 0 ≤ density)
    (hmass : ρ.real {x | (tag x).isSome = true} ≤ density) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hcost : ∀ᵐ ω ∂P, ∀ i j, (i, j) ∈ allowed ω → |c ω i j| ≤
      ((N : ℝ) * density) ^ (2 / (q : ℝ)) *
        (C * ∑ l, (z (xs i ω) l - z (ys j ω) l) ^ 2) + |t| * G) :
    (∫ ω, PartialMatching.legalMaximumValue (allowed ω) (c ω) ∂P) / N ≤
      (∫ ω, ∑ b : Fin q → Fin (2 ^ depth + 1), PartialMatching.legalMaximumValue
        (PartialMatching.spatialLegalBlock (allowed ω)
          (fun i ↦ gridCellLabel q m depth depth hm hdepth (z (xs i ω)))
          (fun j ↦ gridCellLabel q m depth depth hm hdepth (z (ys j ω))) b) (c ω) ∂P) / N +
      activeGridRepairError q (legalGridRepairConstant q (Fintype.card J) (Fintype.card T))
        C G t density ((N : ℝ) / (m : ℝ) ^ q) := by
  classical
  let cell := fun k (x : X) ↦ gridCellLabel q m depth k hm hdepth (z x)
  let tag' := fun k ↦ refinedActiveTag (cell (k + 1)) tag
  let base := fun x ↦ (tag x).map (fun _ ↦ ())
  let p := ρ.real {x | (tag x).isSome = true}
  let r := (N : ℝ) * density
  have hr : 0 ≤ r := mul_nonneg (Nat.cast_nonneg _) hd
  have hcell (k : ℕ) : Measurable (cell k) := (measurable_gridCellLabel q m depth k hm hdepth).comp hz
  have htag' (k : ℕ) : Measurable (tag' k) := measurable_refinedActiveTag _ _ (hcell _) htag
  have hp (k : ℕ) : (∑ a, ρ.real (tag' k ⁻¹' {some a})) = p := by
    simpa only [tag', refinedActiveTag_isSome, p] using
      sum_some_measureReal_preimage_eq_active ρ (tag' k) (htag' k)
  have hact : ∀ᵐ ω ∂P, ∀ e ∈ allowed ω,
      (base (xs e.1 ω)).isSome = true ∧ (base (ys e.2 ω)).isSome = true := by
    simpa only [base, Option.isSome_map] using hactive
  have hleg : ∀ᵐ ω ∂P, ∀ k, k < depth → ∀ i j a,
      tag' k (xs i ω) = some a → tag' k (ys j ω) = some a →
        (i, j) ∈ allowed ω ∧ cell (k + 1) (xs i ω) = cell (k + 1) (ys j ω) := by
    filter_upwards [hlegal] with ω hω
    intro k _ i j a hi hj
    have hi' := (refinedActiveTag_eq_some_iff (cell (k + 1)) tag (xs i ω) a).mp hi
    have hj' := (refinedActiveTag_eq_some_iff (cell (k + 1)) tag (ys j ω) a).mp hj
    exact ⟨hω i j a.2 hi'.2 hj'.2, hi'.1.trans hj'.1.symm⟩
  have hbudget : ∀ᵐ ω ∂P, ∀ k, k ≤ depth → ∀ i j, (i, j) ∈ allowed ω →
      cell k (xs i ω) = cell k (ys j ω) → |c ω i j| ≤ legalGridEdgeBound q r C G t k := by
    filter_upwards [hunit, hcost] with ω huω hcω
    intro k hk i j hij hcell
    exact abs_cost_le_grid_parent_of_quadratic q m depth k hm hdepth hdepth2 hk
      hr hC _ _ (huω _ hij).1 (huω _ hij).2 (hcω i j hij) hcell
  have hM : ∀ᵐ ω ∂P, ∀ i j, (i, j) ∈ allowed ω →
      |c ω i j| ≤ legalGridEdgeBound q r C G t 0 := by
    filter_upwards [hbudget] with ω hω
    exact fun i j hij ↦ hω 0 (Nat.zero_le _) i j hij (gridCellLabel_root hm hdepth _ _)
  have h := PartialMatching.integral_legalMaximumValue_le_active_hierarchical_blocks_of_iid_types
    (T := fun k ↦ (Fin q → Fin (2 ^ (k + 1) + 1)) × T)
    P ρ ρ xs ys hx hy hxi hyi hxl hyl hxy base base tag' tag' htag' htag'
    (fun _ _ ↦ rfl) hp allowed ha hact
    (fun k ω i ↦ cell k (xs i ω)) (fun k ω j ↦ cell k (ys j ω))
    (fun k i ↦ (hcell k).comp (hx i)) (fun k j ↦ (hcell k).comp (hy j))
    (fun k ↦ legalGridParent q m depth k hm hdepth) depth
    (fun ω k hk i ↦ legalGridParent_cell q m depth k hm hdepth (Nat.succ_le_of_lt hk) _)
    (fun ω k hk j ↦ legalGridParent_cell q m depth k hm hdepth (Nat.succ_le_of_lt hk) _)
    (by intro k _ x; simp only [tag', base, refinedActiveTag_isSome, Option.isSome_map])
    hleg sourceClass sourceAllows hallowed c hc
    (legalGridEdgeBound_nonneg q 0 hr hC hG) hM (legalGridEdgeBound q r C G t)
    (fun k ↦ legalGridEdgeBound_nonneg q k hr hC hG)
    (by filter_upwards [hbudget] with ω hω; exact fun k hk ↦ hω k hk.le)
    (gridCellLabel q m depth 0 hm hdepth (fun _ ↦ 0))
    (fun _ _ ↦ gridCellLabel_root hm hdepth _ _) (fun _ _ ↦ gridCellLabel_root hm hdepth _ _)
  have hdiv := div_le_div_of_nonneg_right h (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  simp only [add_div, Fintype.card_prod, gridCellLabel_card, Fintype.card_option,
    Nat.cast_add, Nat.cast_one] at hdiv
  refine hdiv.trans (add_le_add le_rfl ?_)
  exact active_legal_grid_repair_sum_div_le q depth (Fintype.card J) (Fintype.card T) N
    hq hN m hm hdepth2 (fun k ↦ (2 ^ (k + 1) + 1) ^ q * Fintype.card T)
    (fun _ _ ↦ le_rfl) hd hmass hC hG

end OTSelector.Reconstruction
