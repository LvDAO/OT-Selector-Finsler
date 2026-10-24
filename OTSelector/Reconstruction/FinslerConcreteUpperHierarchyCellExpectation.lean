import OTSelector.Reconstruction.FinslerConcreteUpperHierarchyCellCore
import OTSelector.Reconstruction.TaggedDyadicMinimumDepth

/-! One global original-type energy budget controls all compact-color cores.
The fine fixed-depth count correction is separate from the leading energy and
uses only the actual iid histograms of the unchanged original experiment. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- A sufficiently deep single hierarchy gives all same-cell cores, with one
normalized type energy estimate and one explicit fixed-level count budget. -/
theorem exists_same_cell_core_with_one_expected_energy
    {Ω T C : Type*} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSingletonClass T]
    [Fintype T] [Fintype C] {q n k : ℕ} (hq : 4 < q) (hn : 0 < n) (hk : 0 < k)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure (T × DyadicUnitCube q)) [IsProbabilityMeasure μ]
    (xs ys : Fin n → Ω → T × DyadicUnitCube q)
    (hx : ∀ i, Measurable (xs i)) (hy : ∀ i, Measurable (ys i))
    (hxi : iIndepFun xs P) (hyi : iIndepFun ys P)
    (hxl : ∀ i, P.map (xs i) = μ) (hyl : ∀ i, P.map (ys i) = μ)
    (hxy : IndepFun (fun sample i ↦ xs i sample) (fun sample i ↦ ys i sample) P)
    (S : Finset T) (cost : Ω → Fin n → Fin n → ℝ)
    (hc : ∀ i j, Measurable (fun sample ↦ cost sample i j)) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcn : ∀ᵐ sample ∂P, ∀ i j, 0 ≤ cost sample i j)
    (hbound : ∀ᵐ sample ∂P, ∀ i j, cost sample i j ≤ B)
    (hquadratic : ∀ t ∈ S, ∀ᵐ sample ∂P, ∀ i j,
      (xs i sample).1 = t → (ys j sample).1 = t → cost sample i j ≤
        A * ‖dyadicCubePoint (xs i sample).2 - dyadicCubePoint (ys j sample).2‖ ^ 2)
    (sourceCell targetCell : Ω → Fin n → Option C)
    (hcolors : ∀ᵐ sample ∂P,
      (∀ i, (xs i sample).1 ∈ S → ∃ c, sourceCell sample i = some c) ∧
      (∀ j, (ys j sample).1 ∈ S → ∃ c, targetCell sample j = some c) ∧
      ∀ i j c c', sourceCell sample i = some c → targetCell sample j = some c' →
        (xs i sample).1 = (ys j sample).1 →
        dyadicCubeCell k (xs i sample).2 = dyadicCubeCell k (ys j sample).2 → c = c') :
    ∃ K : ℕ, k ≤ K ∧
      (Integrable (fun sample ↦ attributedTypesEnergy S (fun i ↦ xs i sample)
        (fun j ↦ ys j sample) (cost sample) (taggedHierarchyAssignment K xs ys sample)) P ∧
      ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
        (∫ sample, attributedTypesEnergy S (fun i ↦ xs i sample) (fun j ↦ ys j sample)
          (cost sample) (taggedHierarchyAssignment K xs ys sample) ∂P) ≤
        A * dyadicMatchingConstant q * (S.card : ℝ) ^ (2 / (q : ℝ)) *
          (∑ t ∈ S, μ.real {x | x.1 = t}) ^ (1 - 2 / (q : ℝ)) +
        B * Real.sqrt (2 * S.card) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) *
          Real.sqrt (∑ t ∈ S, μ.real {x | x.1 = t})) ∧
      (Integrable (fun sample ↦ ∑ t ∈ S,
        taggedDyadicDiscrepancy t k (fun i ↦ xs i sample) (fun j ↦ ys j sample)) P ∧
      (∫ sample, ∑ t ∈ S, taggedDyadicDiscrepancy t k
        (fun i ↦ xs i sample) (fun j ↦ ys j sample) ∂P) ≤
        ∑ t ∈ S, Real.sqrt (2 * (n : ℝ) * μ.real {x | x.1 = t} * ((2 : ℝ) ^ k + 1) ^ q)) ∧
      ∀ᵐ sample ∂P, ∃ core : OTSelector.PartialMatching n n,
        (∀ e ∈ core.edges,
          (xs e.1 sample).1 ∈ S ∧ (xs e.1 sample).1 = (ys e.2 sample).1 ∧
          ∃ c, sourceCell sample e.1 = some c ∧ targetCell sample e.2 = some c) ∧
        core.cost (cost sample) ≤ attributedTypesEnergy S (fun i ↦ xs i sample)
          (fun j ↦ ys j sample) (cost sample) (taggedHierarchyAssignment K xs ys sample) ∧
        (∑ t ∈ S, partitionCount (fun i ↦ (xs i sample).1) t) - (core.card : ℝ) ≤
          ∑ t ∈ S, taggedDyadicDiscrepancy t k
            (fun i ↦ xs i sample) (fun j ↦ ys j sample) := by
  classical
  obtain ⟨K, hkK, hK⟩ := exists_taggedHierarchy_attributed_energy_rate_above hq k P μ xs ys
    hx hy hxi hyi hxl hyl hxy S cost hc hA hB hcn hbound hquadratic
  have he := integral_sum_type_energy_le hq P S (fun t ↦ μ.real {x | x.1 = t})
    (fun t sample ↦ attributedTypeEnergy t (fun i ↦ xs i sample) (fun j ↦ ys j sample)
      (cost sample) (taggedHierarchyAssignment K xs ys sample)) hA hB
    (fun _ _ ↦ measureReal_nonneg) rfl hK
  have hen := normalized_type_energy_bound hn q
    (A * dyadicMatchingConstant q * (S.card : ℝ) ^ (2 / (q : ℝ))) B S.card
    (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ ↦ measureReal_nonneg)) he.2
  refine ⟨K, hkK, ⟨he.1, hen⟩, ?_, ?_⟩
  · have hd (t : T) := iid_taggedDyadicDiscrepancy_bound P μ xs ys hx hy hxi hyi hxl hyl hxy t k
    refine ⟨integrable_finsetSum S (fun t _ ↦ (hd t).1), ?_⟩
    rw [integral_finsetSum S (fun t _ ↦ (hd t).1)]
    exact Finset.sum_le_sum (fun t _ ↦ (hd t).2)
  · filter_upwards [hcolors, hcn] with sample hcol hcost
    exact exists_hierarchy_same_cell_core hk hkK S (fun i ↦ xs i sample) (fun j ↦ ys j sample)
      (taggedHierarchyAssignment K xs ys sample) (firstOptimalAssignment_isOptimal _)
      (sourceCell sample) (targetCell sample) hcol.1 hcol.2.1 hcol.2.2 (cost sample) hcost

end OTSelector.Reconstruction
