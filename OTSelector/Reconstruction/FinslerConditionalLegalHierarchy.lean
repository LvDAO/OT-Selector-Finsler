import OTSelector.Reconstruction.FinslerConditionalLegalBlock
import OTSelector.Reconstruction.MarkedStationaryValueLegalMultiscale

/-!
# Original conditional populations supply legal multiscale repair

The compact disjoint original carriers produce one positive clock gap and one
finite scalar partition. The actual conditional samples then satisfy the legal
hierarchy estimate for arbitrary spatial cell refinements. No sample balancing
or additional geometric condition is imposed.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

variable {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z] [MeasurableEq Z]

/-- The original calibration, rather than an assumed finite-class graph,
produces the fixed class constant in every conditional multiscale bound. -/
theorem exists_population_conditional_legal_hierarchy
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : M → Z} (ha : Measurable a) (hbalance : μ.map a = ν.map a)
    {u : M → ℝ} (hu : Continuous u) {A B N : Set M}
    (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) (hN : MeasurableSet N)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ x ∂ν, x ∈ B)
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ x ∂ν, x ∈ N)
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {C : ℕ → Type*} [∀ k, Fintype (C k)] [∀ k, DecidableEq (C k)] :
    ∃ gap : ℝ, 0 < gap ∧ ∃ bins : FiniteScalarBins (u '' A ∪ u '' B) gap,
      ∀ᵐ z ∂μ.map a, ∀ (m n : ℕ) (source : Fin m → ℝ) (target : Fin n → ℝ),
        (∀ i, source i ∈ (condDistrib u a μ z).support) →
        (∀ j, target j ∈ (condDistrib u a ν z).support) →
        ∀ (s : (k : ℕ) → Fin m → C k) (t : (k : ℕ) → Fin n → C k)
          (parent : (k : ℕ) → C (k + 1) → C k),
          (∀ k i, parent k (s (k + 1) i) = s k i) →
          (∀ k j, parent k (t (k + 1) j) = t k j) →
          ∀ (c : Fin m → Fin n → ℝ) (Bnd : ℕ → ℝ),
            (∀ k, 0 ≤ Bnd k) →
            (∀ k i j, (i, j) ∈ scalarClockLegalGraph source target →
              s k i = t k j → |c i j| ≤ Bnd k) →
            ∀ root : C 0, (∀ i, s 0 i = root) → (∀ j, t 0 j = root) → ∀ K : ℕ,
              PartialMatching.legalMaximumValue (scalarClockLegalGraph source target) c ≤
                (∑ b : C K, PartialMatching.legalMaximumValue
                  (PartialMatching.spatialLegalBlock
                    (scalarClockLegalGraph source target) (s K) (t K) b) c) +
                ∑ k ∈ Finset.range K,
                  (∑ b : C (k + 1), (((OTSelector.blockFinset (s (k + 1)) b).card -
                    PartialMatching.legalMaximumCard (PartialMatching.spatialLegalBlock
                      (scalarClockLegalGraph source target) (s (k + 1)) (t (k + 1)) b) : ℕ) : ℝ)) *
                        (2 * ((bins.count : ℝ) + 1) * Bnd k) := by
  obtain ⟨gap, hgap, bins, hbins⟩ := exists_population_conditional_scalar_bins μ ν ha hbalance hu
    hA hB hAB hN hμA hνB hμN hνN horder
  refine ⟨gap, hgap, bins, ?_⟩
  filter_upwards [hbins] with z hz
  intro m n source target hsource htarget s t parent hs ht c Bnd hB0 hBc root hsr htr K
  exact bins.legalMaximumValue_le_hierarchical_spatial_blocks hgap source target
    (fun i ↦ hz.1 (hsource i)) (fun i j ↦ hz.2 _ (hsource i) _ (htarget j))
    s t parent hs ht c Bnd hB0 hBc root hsr htr K

end OTSelector.Reconstruction
