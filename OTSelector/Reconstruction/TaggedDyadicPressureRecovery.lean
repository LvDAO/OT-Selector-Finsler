import OTSelector.Reconstruction.TaggedDyadicProbeRecovery

/-!
# Small-mass pressure recovery on one original competitor

The distance energy and bounded probe are charged to the same full measurable
permutation. The selected types are fixed deterministic population pieces;
all sample-count completion edges remain included.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- Linear cost operations preserve the exact incident-type attribution. -/
theorem attributedTypesEnergy_linear
    {T : Type*} {q n : ℕ} (S : Finset T) (x y : Fin n → T × DyadicUnitCube q)
    (cost probe : Fin n → Fin n → ℝ) (σ : Assignment n) (a b : ℝ) :
    attributedTypesEnergy S x y (fun i j ↦ a * cost i j + b * probe i j) σ =
      a * attributedTypesEnergy S x y cost σ + b * attributedTypesEnergy S x y probe σ := by
  unfold attributedTypesEnergy attributedTypeEnergy
  have he (t : T) (i : Fin n) : typeTouchIndicator t (x i).1 (y (σ i)).1 *
      (a * cost i (σ i) + b * probe i (σ i)) =
      a * (typeTouchIndicator t (x i).1 (y (σ i)).1 * cost i (σ i)) +
      b * (typeTouchIndicator t (x i).1 (y (σ i)).1 * probe i (σ i)) := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

set_option backward.isDefEq.respectTransparency false in
/-- The paper's normalized small-mass recovery estimate, including the probe,
for one actual measurable full assignment and every deterministic type subset. -/
theorem exists_taggedHierarchy_smallMass_pressure_recovery
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] {q n : ℕ} (hq : 4 < q) (hn : 0 < n)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (T × DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun ξ i ↦ xs i ξ) (fun ξ i ↦ ys i ξ) P)
    (cost probe : Ω → Fin n → Fin n → ℝ)
    (hc : ∀ i j, Measurable (fun ξ ↦ cost ξ i j))
    (hg : ∀ i j, Measurable (fun ξ ↦ probe ξ i j)) {C B G : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hcn : ∀ᵐ ξ ∂P, ∀ i j, 0 ≤ cost ξ i j)
    (hbound : ∀ᵐ ξ ∂P, ∀ i j, cost ξ i j ≤ B)
    (hgBound : ∀ᵐ ξ ∂P, ∀ i j, |probe ξ i j| ≤ G)
    (hquadratic : ∀ t, ∀ᵐ ξ ∂P, ∀ i j, (xs i ξ).1 = t → (ys j ξ).1 = t →
      cost ξ i j ≤ C * ‖dyadicCubePoint (xs i ξ).2 - dyadicCubePoint (ys j ξ).2‖ ^ 2) :
    ∃ K : ℕ, ∀ (S : Finset T) (τ : ℝ),
      Integrable (fun ξ ↦ attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
        (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost ξ i j + |τ| * |probe ξ i j|)
          (taggedHierarchyAssignment K xs ys ξ)) P ∧
      (1 / (n : ℝ)) * (∫ ξ, attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
        (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost ξ i j + |τ| * |probe ξ i j|)
          (taggedHierarchyAssignment K xs ys ξ) ∂P) ≤
        C * dyadicMatchingConstant q * (S.card : ℝ) ^ (2 / (q : ℝ)) *
          (∑ t ∈ S, μ.real {x | x.1 = t}) ^ (1 - 2 / (q : ℝ)) +
        B * Real.sqrt (2 * S.card) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) *
          Real.sqrt (∑ t ∈ S, μ.real {x | x.1 = t}) +
        2 * |τ| * G * ∑ t ∈ S, μ.real {x | x.1 = t} := by
  obtain ⟨K, hK⟩ := exists_taggedHierarchy_all_smallMass_energies hq hn P μ xs ys hx hy
    hxi hyi hxl hyl hxy cost hc hC hB hcn hbound hquadratic
  refine ⟨K, ?_⟩
  intro S τ
  have hp := expected_taggedHierarchy_bounded_probe P μ xs ys hx hy hxi hyi hxl hyl
    K S probe hg hG rfl hgBound
  let ec (ξ : Ω) := attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
    (cost ξ) (taggedHierarchyAssignment K xs ys ξ)
  let eg (ξ : Ω) := attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
    (fun i j ↦ |probe ξ i j|) (taggedHierarchyAssignment K xs ys ξ)
  have heq : (fun ξ ↦ attributedTypesEnergy S (fun i ↦ xs i ξ) (fun i ↦ ys i ξ)
      (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost ξ i j + |τ| * |probe ξ i j|)
        (taggedHierarchyAssignment K xs ys ξ)) =
      (fun ξ ↦ (n : ℝ) ^ (2 / (q : ℝ)) * ec ξ + |τ| * eg ξ) := by
    funext ξ
    exact attributedTypesEnergy_linear _ _ _ _ _ _ _ _
  rw [heq]
  have hci : Integrable (fun ξ ↦ (n : ℝ) ^ (2 / (q : ℝ)) * ec ξ) P :=
    (hK S).1.const_mul _
  have hgi : Integrable (fun ξ ↦ |τ| * eg ξ) P := hp.1.const_mul _
  refine ⟨hci.add hgi, ?_⟩
  rw [integral_add hci hgi, integral_const_mul, integral_const_mul]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgp := mul_le_mul_of_nonneg_left hp.2 (div_nonneg (abs_nonneg τ) hnR.le)
  have hge : |τ| / (n : ℝ) * (2 * G * n * ∑ t ∈ S, μ.real {x | x.1 = t}) =
      2 * |τ| * G * ∑ t ∈ S, μ.real {x | x.1 = t} := by
    field_simp
  rw [hge] at hgp
  have h := add_le_add (hK S).2 hgp
  calc
    _ = ((n : ℝ) ^ (2 / (q : ℝ)) / n) * (∫ ξ, ec ξ ∂P) +
        (|τ| / n) * (∫ ξ, eg ξ ∂P) := by ring
    _ ≤ _ := h

end OTSelector.Reconstruction
