import OTSelector.Reconstruction.TaggedDyadicEnergyRate

/-! The original global hierarchy energy rate can be attained above any
prescribed dyadic depth. Its one full permutation still controls all selected
type subcollections, with the original constants and count correction. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The original typewise energy estimate with an independently prescribed
minimum depth, chosen before any selected subcollection. -/
theorem exists_taggedHierarchy_attributed_energy_rate_above
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n : ℕ} (hq : 4 < q) (depth : ℕ)
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
    ∃ K : ℕ, depth ≤ K ∧ ∀ t ∈ S,
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
  let K : ℕ := max depth (Finset.univ.sup cutoff)
  refine ⟨K, le_max_left _ _, ?_⟩
  intro t ht
  have htK : cutoff t ≤ K :=
    (Finset.le_sup (f := cutoff) (Finset.mem_univ t)).trans (le_max_right _ _)
  have h := expected_taggedHierarchy_attributed_energy_multiscale htK P μ xs ys hx hy
    hxi hyi hxl hyl hxy t cost hc hC hB hcn hbound (hquadratic t ht)
  refine ⟨h.1, h.2.trans ?_⟩
  have hcutt := hcut t
  simp only [← mul_assoc] at hcutt
  apply add_le_add _ le_rfl
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcutt hC

/-- One sufficiently deep original permutation controls every small-mass
subcollection simultaneously, before normalization. -/
theorem exists_taggedHierarchy_all_smallMass_energies_above
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n : ℕ} (hq : 4 < q) (depth : ℕ)
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
    ∃ K : ℕ, depth ≤ K ∧ ∀ S : Finset T,
      Integrable (fun ξ ↦ attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
        (cost ξ) (taggedHierarchyAssignment K xs ys ξ)) P ∧
      (∫ ξ, attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
          (cost ξ) (taggedHierarchyAssignment K xs ys ξ) ∂P) ≤
        C * dyadicMatchingConstant q * (S.card : ℝ) ^ (2 / (q : ℝ)) *
          ((n : ℝ) * ∑ t ∈ S, μ.real {x | x.1 = t}) ^ (1 - 2 / (q : ℝ)) +
        B * Real.sqrt (2 * (n : ℝ) * S.card * ∑ t ∈ S, μ.real {x | x.1 = t}) := by
  classical
  obtain ⟨K, hdepth, hK⟩ := exists_taggedHierarchy_attributed_energy_rate_above hq depth P μ xs ys hx hy
    hxi hyi hxl hyl hxy Finset.univ cost hc hC hB hcn hbound (fun t _ ↦ hquadratic t)
  refine ⟨K, hdepth, ?_⟩
  intro S
  have h := integral_sum_type_energy_le hq P S (fun t ↦ μ.real {x | x.1 = t})
    (fun t ξ ↦ attributedTypeEnergy t (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
      (cost ξ) (taggedHierarchyAssignment K xs ys ξ)) hC hB
    (fun _ _ ↦ measureReal_nonneg) rfl (fun t _ ↦ hK t (Finset.mem_univ t))
  exact h

end OTSelector.Reconstruction
