import OTSelector.Reconstruction.MarkedStationaryValueLegalActiveHierarchy

/-! Original iid expectations for active hierarchical legal repair.
The square-root error is derived from the original optional point types at each
parent scale; no iid law is assigned to adaptively unmatched endpoints. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

namespace PartialMatching

/-- A bounded actual allowed cost makes the original signed legal value
integrable. Illegal entries need only be measurable, not bounded. -/
theorem integrable_legalMaximumValue_of_allowed
    {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
    (P : Measure Ω) [IsFiniteMeasure P]
    (allowed : Ω → Finset (Fin m × Fin n))
    (ha : ∀ e, MeasurableSet {ω | e ∈ allowed ω})
    (c : Ω → Fin m → Fin n → ℝ) (hc : ∀ i j, Measurable (fun ω ↦ c ω i j))
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᵐ ω ∂P, ∀ i j, (i, j) ∈ allowed ω → |c ω i j| ≤ M) :
    Integrable (fun ω ↦ legalMaximumValue (allowed ω) (c ω)) P := by
  apply Integrable.of_bound
    (measurable_legalMaximumValue allowed (measurableSet_graph_eq_of_mem allowed ha)
      c hc).aestronglyMeasurable ((m : ℝ) * M)
  filter_upwards [hM] with ω hω
  rw [Real.norm_eq_abs]
  exact (abs_legalMaximumValue_le_of_allowed (allowed ω) (c ω) hω).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
      ((legalMaximumCard_le_min _).trans (min_le_left _ _))) hM0)

/-- At every parent scale the original iid type histogram bounds the actual
active legal deficiency. Integrating the finite hierarchy therefore pays its
square-root error at that parent's own cost bound. -/
theorem integral_legalMaximumValue_le_active_hierarchical_blocks_of_iid_types
    {Ω X Y J : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype J]
    {C T : ℕ → Type*} [∀ k, Fintype (C k)] [∀ k, DecidableEq (C k)]
    [∀ k, MeasurableSpace (C k)] [∀ k, MeasurableSingletonClass (C k)]
    [∀ k, Fintype (T k)] [∀ k, DecidableEq (T k)]
    [∀ k, MeasurableSpace (Option (T k))]
    [∀ k, MeasurableSingletonClass (Option (T k))]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {N : ℕ} (xs : Fin N → Ω → X) (ys : Fin N → Ω → Y)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = ν)
    (hxy : IndepFun (fun ω i ↦ xs i ω) (fun ω j ↦ ys j ω) P)
    (baseA : X → Option Unit) (baseB : Y → Option Unit)
    (tagA : (k : ℕ) → X → Option (T k)) (tagB : (k : ℕ) → Y → Option (T k))
    (hA : ∀ k, Measurable (tagA k)) (hB : ∀ k, Measurable (tagB k))
    (hmass : ∀ k a, μ.real (tagA k ⁻¹' {some a}) = ν.real (tagB k ⁻¹' {some a}))
    {p : ℝ} (hp : ∀ k, ∑ a : T k, μ.real (tagA k ⁻¹' {some a}) = p)
    (allowed : Ω → Finset (Fin N × Fin N))
    (ha : ∀ e, MeasurableSet {ω | e ∈ allowed ω})
    (hactive : ∀ᵐ ω ∂P, ∀ e ∈ allowed ω,
      (baseA (xs e.1 ω)).isSome = true ∧ (baseB (ys e.2 ω)).isSome = true)
    (s t : (k : ℕ) → Ω → Fin N → C k)
    (hsm : ∀ k i, Measurable (fun ω ↦ s k ω i))
    (htm : ∀ k j, Measurable (fun ω ↦ t k ω j))
    (parent : (k : ℕ) → C (k + 1) → C k) (K : ℕ)
    (hs : ∀ ω k, k < K → ∀ i, parent k (s (k + 1) ω i) = s k ω i)
    (ht : ∀ ω k, k < K → ∀ j, parent k (t (k + 1) ω j) = t k ω j)
    (hsame : ∀ k, k < K → ∀ x, (tagA k x).isSome = (baseA x).isSome)
    (hlegal : ∀ᵐ ω ∂P, ∀ k, k < K → ∀ i j a,
      tagA k (xs i ω) = some a → tagB k (ys j ω) = some a →
        (i, j) ∈ allowed ω ∧ s (k + 1) ω i = t (k + 1) ω j)
    (sourceClass : Ω → Fin N → J) (sourceAllows : Ω → J → Fin N → Prop)
    (hallowed : ∀ ω i j, (i, j) ∈ allowed ω ↔ sourceAllows ω (sourceClass ω i) j)
    (c : Ω → Fin N → Fin N → ℝ) (hc : ∀ i j, Measurable (fun ω ↦ c ω i j))
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ᵐ ω ∂P, ∀ i j, (i, j) ∈ allowed ω → |c ω i j| ≤ M)
    (B : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ B k)
    (hcost : ∀ᵐ ω ∂P, ∀ k, k < K → ∀ i j, (i, j) ∈ allowed ω →
      s k ω i = t k ω j → |c ω i j| ≤ B k)
    (root : C 0) (hsroot : ∀ ω i, s 0 ω i = root) (htroot : ∀ ω j, t 0 ω j = root) :
    (∫ ω, legalMaximumValue (allowed ω) (c ω) ∂P) ≤
      (∫ ω, ∑ b : C K, legalMaximumValue
        (spatialLegalBlock (allowed ω) (s K ω) (t K ω) b) (c ω) ∂P) +
      ∑ k ∈ Finset.range K,
        Real.sqrt (2 * (N : ℝ) * Fintype.card (T k) * p) *
          (2 * (Fintype.card (Option J) : ℝ) * B k) := by
  classical
  let D : ℕ → Ω → ℝ := fun k ω ↦
    (∑ a : Unit, (blockSizeS (fun i ↦ baseA (xs i ω)) (some a) : ℝ)) -
      ∑ b : C (k + 1), (legalMaximumCard
        (spatialLegalBlock (allowed ω) (s (k + 1) ω) (t (k + 1) ω) b) : ℝ)
  let A : ℕ → ℝ := fun k ↦ 2 * (Fintype.card (Option J) : ℝ) * B k
  have hA0 (k : ℕ) : 0 ≤ A k := mul_nonneg
    (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (hB0 k)
  have hcount (k : ℕ) (hk : k < K) (ω : Ω) :
      (∑ a : T k, (blockSizeS (fun i ↦ tagA k (xs i ω)) (some a) : ℝ)) =
        ∑ a : Unit, (blockSizeS (fun i ↦ baseA (xs i ω)) (some a) : ℝ) := by
    have hn : (∑ a : T k, blockSizeS (fun i ↦ tagA k (xs i ω)) (some a)) =
        ∑ a : Unit, blockSizeS (fun i ↦ baseA (xs i ω)) (some a) := by
      rw [sum_some_blockSizeS_eq_active, sum_some_blockSizeS_eq_active]
      congr 1
      funext i
      exact hsame k hk (xs i ω)
    exact_mod_cast hn
  have hD (k : ℕ) (hk : k ∈ Finset.range K) :
      Integrable (D k) P ∧ (∫ ω, D k ω ∂P) ≤
        Real.sqrt (2 * (N : ℝ) * Fintype.card (T k) * p) := by
    have hleg : ∀ᵐ ω ∂P, ∀ i j a, tagA k (xs i ω) = some a →
        tagB k (ys j ω) = some a → (i, j) ∈ allowed ω ∧
          s (k + 1) ω i = t (k + 1) ω j := by
      filter_upwards [hlegal] with ω hω
      exact hω k (Finset.mem_range.mp hk)
    have h := integral_active_spatial_source_defect_le_of_iid_types P μ ν xs ys
      hx hy hxi hyi hxl hyl hxy (tagA k) (tagB k) (hA k) (hB k)
      (hmass k) (hp k) allowed ha (s (k + 1)) (t (k + 1))
      (hsm (k + 1)) (htm (k + 1)) hleg
    simpa only [hcount k (Finset.mem_range.mp hk), D] using h
  have hVI := integrable_legalMaximumValue_of_allowed P allowed ha c hc hM0 hM
  have hleafI (b : C K) : Integrable (fun ω ↦ legalMaximumValue
      (spatialLegalBlock (allowed ω) (s K ω) (t K ω) b) (c ω)) P := by
    refine integrable_legalMaximumValue_of_allowed P
      (fun ω ↦ spatialLegalBlock (allowed ω) (s K ω) (t K ω) b) ?_ c hc hM0 ?_
    · intro e
      have hS := measurableSet_eq_fun (hsm K e.1) measurable_const (g := fun _ ↦ b)
      have hT := measurableSet_eq_fun (htm K e.2) measurable_const (g := fun _ ↦ b)
      simpa only [spatialLegalBlock, Finset.mem_filter, Set.ofPred_and] using
        (ha e).inter (hS.inter hT)
    · filter_upwards [hM] with ω hω
      intro i j hij
      exact hω i j (Finset.mem_filter.mp hij).1
  have hLI := integrable_finsetSum (Finset.univ : Finset (C K)) (fun b _ ↦ hleafI b)
  have hRI := integrable_finsetSum (Finset.range K)
    (fun k hk ↦ (hD k hk).1.mul_const (A k))
  have hpoint : ∀ᵐ ω ∂P, legalMaximumValue (allowed ω) (c ω) ≤
      (∑ b : C K, legalMaximumValue
        (spatialLegalBlock (allowed ω) (s K ω) (t K ω) b) (c ω)) +
      ∑ k ∈ Finset.range K, D k ω * A k := by
    filter_upwards [hactive, hcost] with ω haω hcω
    exact legalMaximumValue_le_active_hierarchical_blocks_upto (allowed ω)
      (fun i ↦ baseA (xs i ω)) (fun j ↦ baseB (ys j ω)) haω
      (fun k ↦ s k ω) (fun k ↦ t k ω) parent K (hs ω) (ht ω)
      (sourceClass ω) (sourceAllows ω) (hallowed ω) (c ω) B hB0 hcω
      root (hsroot ω) (htroot ω)
  have h := integral_mono_ae hVI (hLI.fun_add hRI) hpoint
  rw [integral_add hLI hRI, integral_finsetSum _
    (fun k hk ↦ (hD k hk).1.mul_const (A k))] at h
  simp only [integral_mul_const] at h
  refine h.trans (add_le_add le_rfl (Finset.sum_le_sum ?_))
  intro k hk
  exact mul_le_mul_of_nonneg_right (hD k hk).2 (hA0 k)

end PartialMatching
end OTSelector.Reconstruction
