import OTSelector.Reconstruction.TaggedDyadicIID

/-!
# Typed matching rates and fixed-subplan energy

One full permutation controls all deterministic type subcollections simultaneously.
Its normalized attributed energy has the high-dimensional small-mass power,
with the actual original count completion correction.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false in
/-- A single measurable full competitor simultaneously has the correct rate for
all selected deterministic types. No realized type counts are balanced. -/
theorem exists_taggedHierarchy_attributed_energy_rate
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n : ℕ} (hq : 4 < q)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (T × DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    (S : Finset T) (cost : Ω → Fin n → Fin n → ℝ)
    (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j)) {C B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ cost ξ i j)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, cost ξ i j ≤ B)
    (hquadratic : ∀ t ∈ S, ∀ᵐ ξ ∂P, ∀ i j, (xs i ξ).1 = t → (ys j ξ).1 = t →
      cost ξ i j ≤ C * ‖dyadicCubePoint (xs i ξ).2 - dyadicCubePoint (ys j ξ).2‖ ^ 2) :
    ∃ K : ℕ, ∀ t ∈ S,
      Integrable (fun ξ ↦ attributedTypeEnergy t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
        (cost ξ) (taggedHierarchyAssignment K xs ys ξ)) P ∧
      (∫ ξ, attributedTypeEnergy t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
        (cost ξ) (taggedHierarchyAssignment K xs ys ξ) ∂P) ≤
        C * dyadicMatchingConstant q * ((n : ℝ) * μ.real {x | x.1 = t}) ^ (1 - 2 / (q : ℝ)) +
        B * Real.sqrt (2 * (n : ℝ) * μ.real {x | x.1 = t}) := by
  classical
  have hex (t : T) := exists_dyadicCube_rate_cutoff_nonneg hq
    (mul_nonneg (Nat.cast_nonneg n) (measureReal_nonneg : 0 ≤ μ.real {x | x.1 = t}))
  choose cutoff hcut using hex
  let K : ℕ := Finset.univ.sup cutoff
  refine ⟨K, ?_⟩
  intro t ht
  have htK : cutoff t ≤ K := Finset.le_sup (f := cutoff) (Finset.mem_univ t)
  have h := expected_taggedHierarchy_attributed_energy_multiscale htK P μ xs ys hx hy
    hxi hyi hxl hyl hxy t cost hc hC hB hcn hbound (hquadratic t ht)
  refine ⟨h.1, h.2.trans ?_⟩
  have hcutt := hcut t
  simp only [← mul_assoc] at hcutt
  apply add_le_add _ le_rfl
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcutt hC

/-- Finite mass attribution for an arbitrary selected collection of types. -/
theorem sum_rpow_typeMass_finset_le {T : Type*} (S : Finset T) (p : T → ℝ)
    (hp : ∀ t ∈ S, 0 ≤ p t) {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    (∑ t ∈ S, (p t) ^ γ) ≤ (S.card : ℝ) ^ (1 - γ) * (∑ t ∈ S, p t) ^ γ := by
  have h := sum_rpow_typeMass_le (fun t : S ↦ p t) (fun t ↦ hp t t.property) hγ0 hγ1
  simpa only [Fintype.card_coe, Finset.sum_coe_sort S (fun t ↦ (p t) ^ γ),
    Finset.sum_coe_sort S p] using h

theorem sum_sqrt_typeMass_finset_le {T : Type*} (S : Finset T) (p : T → ℝ)
    (hp : ∀ t ∈ S, 0 ≤ p t) :
    (∑ t ∈ S, Real.sqrt (p t)) ≤ Real.sqrt ((S.card : ℝ) * ∑ t ∈ S, p t) := by
  have h := sum_sqrt_typeMass_le (fun t : S ↦ p t) (fun t ↦ hp t t.property)
  simpa only [Fintype.card_coe, Finset.sum_coe_sort S (fun t ↦ Real.sqrt (p t)),
    Finset.sum_coe_sort S p] using h

/-- Selected incident energy is evaluated on the one full global permutation. -/
def attributedTypesEnergy {T : Type*} {q n : ℕ} (S : Finset T)
    (x y : Fin n → T × DyadicUnitCube q) (cost : Fin n → Fin n → ℝ)
    (σ : Assignment n) : ℝ := ∑ t ∈ S, attributedTypeEnergy t x y cost σ

/-- Summation of actual typewise expected energies uses only the original
finite type masses and the common full competitor. -/
theorem integral_sum_type_energy_le
    {Ω T : Type*} [MeasurableSpace Ω] {q n : ℕ} (hq : 4 < q)
    (P : Measure Ω) (S : Finset T) (p : T → ℝ) (E : T → Ω → ℝ)
    {C B ε : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hp0 : ∀ t ∈ S, 0 ≤ p t) (hmass : (∑ t ∈ S, p t) = ε)
    (hE : ∀ t ∈ S, Integrable (E t) P ∧
      (∫ ξ, E t ξ ∂P) ≤ C * dyadicMatchingConstant q * ((n : ℝ) * p t) ^ (1 - 2 / (q : ℝ)) +
        B * Real.sqrt (2 * (n : ℝ) * p t)) :
    Integrable (fun ξ ↦ ∑ t ∈ S, E t ξ) P ∧
      (∫ ξ, ∑ t ∈ S, E t ξ ∂P) ≤
        C * dyadicMatchingConstant q * (S.card : ℝ) ^ (2 / (q : ℝ)) *
          ((n : ℝ) * ε) ^ (1 - 2 / (q : ℝ)) + B * Real.sqrt (2 * (n : ℝ) * S.card * ε) := by
  refine ⟨integrable_finsetSum _ (fun t ht ↦ (hE t ht).1), ?_⟩
  rw [integral_finsetSum _ (fun t ht ↦ (hE t ht).1)]
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  have hg0 : 0 < 1 - 2 / (q : ℝ) := by
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hg1 : 1 - 2 / (q : ℝ) ≤ 1 := by
    have : 0 ≤ 2 / (q : ℝ) := by positivity
    linarith
  have hp := sum_rpow_typeMass_finset_le S (fun t ↦ (n : ℝ) * p t)
    (fun t ht ↦ mul_nonneg (Nat.cast_nonneg n) (hp0 t ht)) hg0 hg1
  have hs := sum_sqrt_typeMass_finset_le S (fun t ↦ 2 * (n : ℝ) * p t)
    (fun t ht ↦ mul_nonneg (by positivity) (hp0 t ht))
  rw [← Finset.mul_sum, hmass] at hp hs
  have he : 1 - (1 - 2 / (q : ℝ)) = 2 / (q : ℝ) := by ring
  rw [he] at hp
  calc
    _ ≤ ∑ t ∈ S, (C * dyadicMatchingConstant q *
        ((n : ℝ) * p t) ^ (1 - 2 / (q : ℝ)) +
        B * Real.sqrt (2 * (n : ℝ) * p t)) :=
      Finset.sum_le_sum (fun t ht ↦ (hE t ht).2)
    _ = C * dyadicMatchingConstant q *
        (∑ t ∈ S, ((n : ℝ) * p t) ^ (1 - 2 / (q : ℝ))) +
        B * (∑ t ∈ S, Real.sqrt (2 * (n : ℝ) * p t)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ _ := by
      apply add_le_add
      · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp
          (mul_nonneg hC (dyadicMatchingConstant_pos hq).le)
      · have heq : (S.card : ℝ) * (2 * (n : ℝ) * ε) = 2 * (n : ℝ) * S.card * ε := by ring
        rw [heq] at hs
        exact mul_le_mul_of_nonneg_left hs hB


set_option backward.isDefEq.respectTransparency false in
/-- Actual small-mass expected recovery before normalization. The same full
permutation supplies the main mass power and the finite count correction. -/
theorem exists_taggedHierarchy_smallMass_energy
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n : ℕ} (hq : 4 < q)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (T × DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    (S : Finset T) (cost : Ω → Fin n → Fin n → ℝ)
    (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j)) {C B ε : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hmass : (∑ t ∈ S, μ.real {x | x.1 = t}) = ε)
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ cost ξ i j)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, cost ξ i j ≤ B)
    (hquadratic : ∀ t ∈ S, ∀ᵐ ξ ∂P, ∀ i j, (xs i ξ).1 = t → (ys j ξ).1 = t →
      cost ξ i j ≤ C * ‖dyadicCubePoint (xs i ξ).2 - dyadicCubePoint (ys j ξ).2‖ ^ 2) :
    ∃ K : ℕ,
      Integrable (fun ξ ↦ attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
        (cost ξ) (taggedHierarchyAssignment K xs ys ξ)) P ∧
      (∫ ξ, attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
        (cost ξ) (taggedHierarchyAssignment K xs ys ξ) ∂P) ≤
        C * dyadicMatchingConstant q * (S.card : ℝ) ^ (2 / (q : ℝ)) *
          ((n : ℝ) * ε) ^ (1 - 2 / (q : ℝ)) + B * Real.sqrt (2 * (n : ℝ) * S.card * ε) := by
  classical
  obtain ⟨K, hK⟩ := exists_taggedHierarchy_attributed_energy_rate hq P μ xs ys hx hy
    hxi hyi hxl hyl hxy S cost hc hC hB hcn hbound hquadratic
  exact ⟨K, integral_sum_type_energy_le hq P S (fun t ↦ μ.real {x | x.1 = t})
    (fun t ξ ↦ attributedTypeEnergy t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
      (cost ξ) (taggedHierarchyAssignment K xs ys ξ)) hC hB
    (fun _ _ ↦ measureReal_nonneg) hmass hK⟩


/-- The main type energy loses exactly the sample scale after normalization. -/
theorem normalized_type_mass_power_eq {n : ℕ} (hn : 0 < n) (q : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ((n : ℝ) ^ (2 / q) / n) * ((n : ℝ) * ε) ^ (1 - 2 / q) = ε ^ (1 - 2 / q) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.mul_rpow hnR.le hε]
  have he : (n : ℝ) ^ (2 / q) * (n : ℝ) ^ (1 - 2 / q) = n := by
    rw [← Real.rpow_add hnR]
    norm_num
  calc
    _ = ((n : ℝ) ^ (2 / q) * (n : ℝ) ^ (1 - 2 / q) / n) * ε ^ (1 - 2 / q) := by ring
    _ = _ := by rw [he, div_self hnR.ne', one_mul]

/-- Normalized attributed energy has the paper's small-mass power and vanishing
count correction. The constants come from the same actual finite type family. -/
theorem normalized_type_energy_bound {n : ℕ} (hn : 0 < n) (q A B T : ℝ)
    {ε E : ℝ} (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hE : E ≤ A * ((n : ℝ) * ε) ^ (1 - 2 / q) + B * Real.sqrt (2 * n * T * ε)) :
    ((n : ℝ) ^ (2 / q) / n) * E ≤
      A * ε ^ (1 - 2 / q) +
        B * Real.sqrt (2 * T) * (n : ℝ) ^ (2 / q - 1 / 2) * Real.sqrt ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 ≤ (n : ℝ) ^ (2 / q) / n := by positivity
  apply (mul_le_mul_of_nonneg_left hE hs).trans_eq
  rw [mul_add]
  have hm := normalized_type_mass_power_eq hn q hε
  have hc := normalized_count_sqrt_eq hn q (2 * T * ε)
  have he : (n : ℝ) * (2 * T * ε) = 2 * n * T * ε := by ring
  have hsq : Real.sqrt (2 * T * ε) = Real.sqrt (2 * T) * Real.sqrt ε :=
    Real.sqrt_mul (mul_nonneg (by norm_num) hT) ε
  rw [he, hsq] at hc
  calc
    _ = A * (((n : ℝ) ^ (2 / q) / n) * ((n : ℝ) * ε) ^ (1 - 2 / q)) +
      B * (((n : ℝ) ^ (2 / q) / n) * Real.sqrt (2 * n * T * ε)) := by ring
    _ = _ := by rw [hm, hc]; ring

set_option backward.isDefEq.respectTransparency false in
/-- One original full permutation controls every selected subcollection at once.
The finite class refinement is fixed before the samples are drawn. -/
theorem exists_taggedHierarchy_all_smallMass_energies
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (T × DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    (cost : Ω → Fin n → Fin n → ℝ)
    (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j)) {C B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ cost ξ i j)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, cost ξ i j ≤ B)
    (hquadratic : ∀ t, ∀ᵐ ξ ∂P, ∀ i j, (xs i ξ).1 = t → (ys j ξ).1 = t →
      cost ξ i j ≤ C * ‖dyadicCubePoint (xs i ξ).2 - dyadicCubePoint (ys j ξ).2‖ ^ 2) :
    ∃ K : ℕ, ∀ S : Finset T,
      Integrable (fun ξ ↦ attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
        (cost ξ) (taggedHierarchyAssignment K xs ys ξ)) P ∧
      ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
        (∫ ξ, attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
          (cost ξ) (taggedHierarchyAssignment K xs ys ξ) ∂P) ≤
        C * dyadicMatchingConstant q * (S.card : ℝ) ^ (2 / (q : ℝ)) *
          (∑ t ∈ S, μ.real {x | x.1 = t}) ^ (1 - 2 / (q : ℝ)) +
        B * Real.sqrt (2 * S.card) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) *
          Real.sqrt (∑ t ∈ S, μ.real {x | x.1 = t}) := by
  classical
  obtain ⟨K, hK⟩ := exists_taggedHierarchy_attributed_energy_rate hq P μ xs ys hx hy
    hxi hyi hxl hyl hxy Finset.univ cost hc hC hB hcn hbound (fun t _ ↦ hquadratic t)
  refine ⟨K, ?_⟩
  intro S
  have h := integral_sum_type_energy_le hq P S (fun t ↦ μ.real {x | x.1 = t})
    (fun t ξ ↦ attributedTypeEnergy t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
      (cost ξ) (taggedHierarchyAssignment K xs ys ξ)) hC hB
    (fun _ _ ↦ measureReal_nonneg) rfl (fun t _ ↦ hK t (Finset.mem_univ t))
  exact ⟨h.1, normalized_type_energy_bound hn q
    (C * dyadicMatchingConstant q * (S.card : ℝ) ^ (2 / (q : ℝ))) B S.card
    (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ ↦ measureReal_nonneg)) h.2⟩


/-- Every full matching cost is bounded by its total type attribution. -/
theorem assignmentCost_le_attributedTypesEnergy_univ
    {T : Type*} [Fintype T] {q n : ℕ} (x y : Fin n → T × DyadicUnitCube q)
    (cost : Fin n → Fin n → ℝ) (σ : Assignment n) (hc : ∀ i j, 0 ≤ cost i j) :
    assignmentCost cost σ ≤ attributedTypesEnergy Finset.univ x y cost σ := by
  classical
  unfold assignmentCost attributedTypesEnergy attributedTypeEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  have h := Finset.single_le_sum (s := (Finset.univ : Finset T))
    (f := fun t ↦ typeTouchIndicator t (x i).1 (y (σ i)).1 * cost i (σ i))
    (fun t _ ↦ mul_nonneg (typeTouchIndicator_bounds _ _ _).1 (hc i _))
    (Finset.mem_univ (x i).1)
  simpa [typeTouchIndicator] using h

/-- Incident energy counts each edge once even when both endpoints are selected. -/
def incidentTypesEnergy {T : Type*} {q n : ℕ} (S : Finset T)
    (x y : Fin n → T × DyadicUnitCube q) (cost : Fin n → Fin n → ℝ)
    (σ : Assignment n) : ℝ := by
  classical
  exact ∑ i, if (x i).1 ∈ S ∨ (y (σ i)).1 ∈ S then cost i (σ i) else 0

/-- The attributed bound controls the actual energy of all edges touching the
selected deterministic population pieces, including crossing completion edges. -/
theorem incidentTypesEnergy_le_attributedTypesEnergy
    {T : Type*} {q n : ℕ} (S : Finset T) (x y : Fin n → T × DyadicUnitCube q)
    (cost : Fin n → Fin n → ℝ) (σ : Assignment n) (hc : ∀ i j, 0 ≤ cost i j) :
    incidentTypesEnergy S x y cost σ ≤ attributedTypesEnergy S x y cost σ := by
  classical
  unfold incidentTypesEnergy attributedTypesEnergy attributedTypeEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  by_cases hmem : (x i).1 ∈ S ∨ (y (σ i)).1 ∈ S
  · simp only [hmem, ↓reduceIte]
    rcases hmem with hm | hm
    · have h := Finset.single_le_sum (s := S)
        (f := fun t ↦ typeTouchIndicator t (x i).1 (y (σ i)).1 * cost i (σ i))
        (fun t _ ↦ mul_nonneg (typeTouchIndicator_bounds _ _ _).1 (hc i _)) hm
      simpa [typeTouchIndicator] using h
    · have h := Finset.single_le_sum (s := S)
        (f := fun t ↦ typeTouchIndicator t (x i).1 (y (σ i)).1 * cost i (σ i))
        (fun t _ ↦ mul_nonneg (typeTouchIndicator_bounds _ _ _).1 (hc i _)) hm
      simpa [typeTouchIndicator] using h
  · simp only [hmem, ↓reduceIte]
    exact Finset.sum_nonneg (fun t _ ↦ mul_nonneg (typeTouchIndicator_bounds _ _ _).1 (hc i _))

set_option backward.isDefEq.respectTransparency false in
/-- The whole original finite assignment value inherits the global rate. The
competitor uses original marked samples, including all count completion edges. -/
theorem expected_assignmentValue_le_taggedHierarchy_rate
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (T × DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    (cost : Ω → Fin n → Fin n → ℝ)
    (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j)) {C B : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ cost ξ i j)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, cost ξ i j ≤ B)
    (hquadratic : ∀ t, ∀ᵐ ξ ∂P, ∀ i j, (xs i ξ).1 = t → (ys j ξ).1 = t →
      cost ξ i j ≤ C * ‖dyadicCubePoint (xs i ξ).2 - dyadicCubePoint (ys j ξ).2‖ ^ 2) :
    Integrable (fun ξ ↦ perturbedAssignmentValue (cost ξ) 0 0) P ∧
    ((n : ℝ) ^ (2 / (q : ℝ)) / n) * (∫ ξ, perturbedAssignmentValue (cost ξ) 0 0 ∂P) ≤
      C * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) +
      B * Real.sqrt (2 * Fintype.card T) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) := by
  classical
  obtain ⟨K, hK⟩ := exists_taggedHierarchy_all_smallMass_energies hq hn P μ xs ys hx hy
    hxi hyi hxl hyl hxy cost hc hC hB hcn hbound hquadratic
  have hmass : (∑ t : T, μ.real {x | x.1 = t}) = 1 := by
    simpa [Set.preimage, Set.mem_singleton_iff] using
      sum_measureReal_preimage_singleton (μ := μ) Finset.univ (f := Prod.fst)
        (fun t _ ↦ measurable_fst (measurableSet_singleton t))
  have h := hK Finset.univ
  simp only [Finset.card_univ, hmass, Real.one_rpow, Real.sqrt_one, mul_one] at h
  have hci (i j : Fin n) : Integrable (fun ξ ↦ cost ξ i j) P := by
    apply (integrable_const B).mono' (hc i j).aestronglyMeasurable
    filter_upwards [hcn, hbound] with ξ hnξ hbξ
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnξ i j)] using hbξ i j
  have hi := Probability.integrable_assignmentValue P cost hc hci
  refine ⟨hi, ?_⟩
  have hle := integral_mono_ae hi h.1 (by
    filter_upwards [hcn] with ξ hnξ
    have hv := perturbedAssignmentValue_le (cost ξ) 0 0 (taggedHierarchyAssignment K xs ys ξ)
    simp only [perturbedEdgeCost_zero] at hv
    exact hv.trans (assignmentCost_le_attributedTypesEnergy_univ
      (fun i ↦ xs i ξ) (fun i ↦ ys i ξ) (cost ξ) _ hnξ))
  exact (mul_le_mul_of_nonneg_left hle (by positivity)).trans h.2




/-- The count completion correction is uniformly bounded for every nonempty
sample in the high-dimensional range. -/
theorem highDimensional_count_power_le_one {q n : ℕ} (hq : 4 < q) (hn : 0 < n) :
    (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (4 : ℝ) < q := by exact_mod_cast hq
  apply Real.rpow_le_one_of_one_le_of_nonpos hnR
  rw [sub_nonpos, div_le_iff₀ (by linarith : (0 : ℝ) < q)]
  linarith

end OTSelector.Reconstruction
