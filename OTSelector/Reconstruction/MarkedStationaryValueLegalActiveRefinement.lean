import OTSelector.Reconstruction.MarkedStationaryValueLegalActiveExpectation

/-! Common original latent types and arbitrary measurable spatial refinements.
Optional-type masses and activity identities are derived from the same law. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Proper optional types partition exactly the original active event. -/
theorem sum_some_measureReal_preimage_eq_active
    {X T : Type*} [MeasurableSpace X] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    (ρ : Measure X) [IsFiniteMeasure ρ] (tag : X → Option T) (htag : Measurable tag) :
    (∑ a : T, ρ.real (tag ⁻¹' {some a})) = ρ.real {x | (tag x).isSome = true} := by
  classical
  let S := (Finset.univ : Finset T).map ⟨some, Option.some_injective T⟩
  have hre : tag ⁻¹' (S : Set (Option T)) = {x | (tag x).isSome = true} := by
    ext x
    cases h : tag x <;> simp [S, h]
  have h := sum_measureReal_preimage_singleton (μ := ρ) S
    (fun a _ ↦ (measurableSet_singleton a).preimage htag)
  rw [hre] at h
  simpa only [S, Finset.sum_map, Function.Embedding.coeFn_mk] using h

/-- Refine a proper original type by its actual spatial cell; inactive points
remain inactive. -/
def refinedActiveTag {X Cell T : Type*} (cell : X → Cell) (tag : X → Option T)
    (x : X) : Option (Cell × T) := (tag x).map (fun a ↦ (cell x, a))

/-- A refined type records exactly the original cell and proper type. -/
@[simp] theorem refinedActiveTag_eq_some_iff {X Cell T : Type*}
    (cell : X → Cell) (tag : X → Option T) (x : X) (a : Cell × T) :
    refinedActiveTag cell tag x = some a ↔ cell x = a.1 ∧ tag x = some a.2 := by
  rcases a with ⟨b, a⟩
  cases h : tag x <;> simp [refinedActiveTag, h, Prod.mk.injEq]

@[simp] theorem refinedActiveTag_isSome {X Cell T : Type*}
    (cell : X → Cell) (tag : X → Option T) (x : X) :
    (refinedActiveTag cell tag x).isSome = (tag x).isSome := by
  simp [refinedActiveTag]

/-- Actual finite spatial/type refinement is measurable. -/
theorem measurable_refinedActiveTag {X Cell T : Type*}
    [MeasurableSpace X] [MeasurableSpace Cell] [MeasurableSpace (Option T)]
    [MeasurableSpace (Option (Cell × T))]
    [Fintype Cell] [Fintype T] [MeasurableSingletonClass Cell]
    [MeasurableSingletonClass (Option T)]
    (cell : X → Cell) (tag : X → Option T) (hc : Measurable cell) (htag : Measurable tag) :
    Measurable (refinedActiveTag cell tag) := by
  have hf : Measurable (fun p : Cell × Option T ↦ p.2.map (fun a ↦ (p.1, a))) :=
    measurable_of_countable _
  exact hf.comp (hc.prodMk htag)

/-- The actual shared latent point law supplies all refined masses and the
unchanged active source count. Spatial child masses may be arbitrary. -/
theorem integral_active_spatial_source_defect_le_of_common_refined_type
    {Ω X Cell T : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Cell] [Fintype Cell] [DecidableEq Cell] [MeasurableSingletonClass Cell]
    [Fintype T] [DecidableEq T] [MeasurableSpace (Option T)]
    [MeasurableSingletonClass (Option T)] [MeasurableSpace (Option (Cell × T))]
    [MeasurableSingletonClass (Option (Cell × T))]
    (P : Measure Ω) [IsProbabilityMeasure P] (ρ : Measure X) [IsProbabilityMeasure ρ]
    {N : ℕ} (xs ys : Fin N → Ω → X)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = ρ) (hyl : ∀ i, P.map (ys i) = ρ)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω j ↦ ys j ω) P)
    (tag : X → Option T) (htag : Measurable tag)
    (cell : X → Cell) (hc : Measurable cell)
    (allowed : Ω → Finset (Fin N × Fin N))
    (ha : ∀ e, MeasurableSet {ω | e ∈ allowed ω})
    (hlegal : ∀ᵐ ω ∂P, ∀ i j a, tag (xs i ω) = some a → tag (ys j ω) = some a →
      (i, j) ∈ allowed ω) :
    let defect := fun ω ↦ (∑ a : T, (blockSizeS (fun i ↦ tag (xs i ω)) (some a) : ℝ)) -
      ∑ b : Cell, (PartialMatching.legalMaximumCard
        (PartialMatching.spatialLegalBlock (allowed ω) (fun i ↦ cell (xs i ω))
          (fun j ↦ cell (ys j ω)) b) : ℝ)
    Integrable defect P ∧ (∫ ω, defect ω ∂P) ≤
      Real.sqrt (2 * (N : ℝ) * (Fintype.card Cell * Fintype.card T) *
        ρ.real {x | (tag x).isSome = true}) := by
  classical
  let tag' := refinedActiveTag cell tag
  have hm := measurable_refinedActiveTag cell tag hc htag
  have hcount (ω : Ω) :
      (∑ a : Cell × T, (blockSizeS (fun i ↦ tag' (xs i ω)) (some a) : ℝ)) =
        ∑ a : T, (blockSizeS (fun i ↦ tag (xs i ω)) (some a) : ℝ) := by
    have hn : (∑ a : Cell × T, blockSizeS (fun i ↦ tag' (xs i ω)) (some a)) =
        ∑ a : T, blockSizeS (fun i ↦ tag (xs i ω)) (some a) := by
      rw [sum_some_blockSizeS_eq_active, sum_some_blockSizeS_eq_active]
      simp only [tag', refinedActiveTag_isSome]
    exact_mod_cast hn
  have hleg : ∀ᵐ ω ∂P, ∀ i j a, tag' (xs i ω) = some a → tag' (ys j ω) = some a →
      (i, j) ∈ allowed ω ∧ cell (xs i ω) = cell (ys j ω) := by
    filter_upwards [hlegal] with ω hω
    intro i j a hi hj
    have hi' := (refinedActiveTag_eq_some_iff cell tag (xs i ω) a).mp hi
    have hj' := (refinedActiveTag_eq_some_iff cell tag (ys j ω) a).mp hj
    exact ⟨hω i j a.2 hi'.2 hj'.2, hi'.1.trans hj'.1.symm⟩
  have h := integral_active_spatial_source_defect_le_of_iid_types P ρ ρ xs ys
    hx hy hxi hyi hxl hyl hxy tag' tag' hm hm (fun _ ↦ rfl)
    (sum_some_measureReal_preimage_eq_active ρ tag' hm) allowed ha
    (fun ω i ↦ cell (xs i ω)) (fun ω j ↦ cell (ys j ω))
    (fun i ↦ hc.comp (hx i)) (fun j ↦ hc.comp (hy j)) hleg
  simpa only [hcount, Fintype.card_prod, Nat.cast_mul, tag', refinedActiveTag_isSome] using h

end OTSelector.Reconstruction
