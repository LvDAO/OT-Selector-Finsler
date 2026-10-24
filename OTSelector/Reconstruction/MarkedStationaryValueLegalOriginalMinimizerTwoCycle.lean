import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalMinimizerNoLocalCycle
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalCycleCenteredExhaustion

/-! # Actual weighted stationary minimality produces original legal two-cycles -/
open Set Function MeasureTheory ProbabilityTheory Filter
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {probe : ℝ → ℝ → ℝ} {t : ℝ}

/-- Every actual original weighted stationary minimizer satisfies the legal
two-cycle inequality at every pair of its occupied edges, almost surely. The
same-input stationary competitor, finite energy and strict mean saving are
all produced internally; cyclic monotonicity is a conclusion. -/
theorem LegalWeightedStationaryPoissonMatching.minimizer_legal_twoCycle
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hg : Measurable (Function.uncurry probe))
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |probe a b| ≤ G)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q α β kin probe, M.value t ≤ P.value t) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
        ∀ f ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
          e.1.2 < f.2.2 → f.1.2 < e.2.2 →
            originalWeightedEdgeCost kin probe t e + originalWeightedEdgeCost kin probe t f ≤
              originalWeightedEdgeCost kin probe t (e.1, f.2) +
                originalWeightedEdgeCost kin probe t (f.1, e.2) := by
  apply M.ae_originalTwoCycle_of_origin_inactive hk hg t
  intro ell hell ε hε S
  let : Fact (0 < ell) := ⟨hell⟩
  exact M.minimizer_originCycle_inactive hk hkn hg hC hkb hgb hmin hε S

/-- The original bounded probe gives exactly the kinetic defect used by the
complete-path traffic argument, retaining every original color and clock. -/
theorem LegalWeightedStationaryPoissonMatching.minimizer_legal_kineticTwoCycle
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hg : Measurable (Function.uncurry probe))
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |probe a b| ≤ G)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q α β kin probe, M.value t ≤ P.value t) :
    ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
        ∀ f ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
          e.1.2 < f.2.2 → f.1.2 < e.2.2 →
            kin e.1.2 e.2.2 (e.2.1 - e.1.1) + kin f.1.2 f.2.2 (f.2.1 - f.1.1) ≤
              kin e.1.2 f.2.2 (f.2.1 - e.1.1) + kin f.1.2 e.2.2 (e.2.1 - f.1.1) +
                4 * |t| * G := by
  filter_upwards [M.minimizer_legal_twoCycle hk hkn hg hC hkb hgb hmin] with s hs
  intro e he f hf hcross1 hcross2
  exact originalWeightedTwoCycle_le_imp_kinetic_defect kin probe hgb t e f
    (hs e he f hf hcross1 hcross2)

end OTSelector.Reconstruction
