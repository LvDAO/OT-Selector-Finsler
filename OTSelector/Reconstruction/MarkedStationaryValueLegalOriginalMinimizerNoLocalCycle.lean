import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalGridExchangeKineticIntegrability

/-! # Actual stationary minimality excludes every improving original local cycle -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false
variable {q : ℕ} {ell ε : ℝ} [hell : Fact (0 < ell)]
  {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {probe : ℝ → ℝ → ℝ} {t : ℝ}

/-- The literal original-input grid exchange belongs to the very same weighted
stationary Poisson matching class used in the actual minimization. -/
def LegalWeightedStationaryPoissonMatching.gridExchange
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hg : Measurable (Function.uncurry probe))
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |probe a b| ≤ G)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε) :
    LegalWeightedStationaryPoissonMatching q α β kin probe := by
  have hnorm := M.gridExchangeLaw_palm_normalization S
  let : IsProbabilityMeasure (legalMarkedJointPalm q (originalGridExchangeLaw S M.law)) := hnorm.1
  exact {
    law := originalGridExchangeLaw S M.law
    stationary := measurePreserving_originalGridExchangeLaw S M.law M.stationary
    full_matching := M.gridExchangeLaw_full_matching S
    forward := M.gridExchangeLaw_forward S
    input_laplace := by
      intro R hR F hF hzero
      rw [integral_legalMarkedInputSceneLaplace_eq_of_inputLaw_eq
        (originalGridExchangeLaw S M.law) M.law (map_originalGridExchangeLaw_input S M.law) F hF]
      exact M.input_laplace R hR F hF hzero
    palm_probability := hnorm.1
    source_clock := hnorm.2.1
    target_clock := hnorm.2.2
    kinetic_integrable := M.gridExchangeLaw_kinetic_integrable hk hkn hg hC hkb hgb S
    probe_integrable := by
      apply (integrable_const G).mono' ((hg.comp measurable_fst).aestronglyMeasurable)
      exact Eventually.of_forall (fun m ↦ by
        change ‖probe m.1.1 m.1.2‖ ≤ G
        rw [Real.norm_eq_abs]
        exact hgb m.1.1 m.1.2) }

/-- The exact unit source-window mean is the actual competitor's original
true-Palm weighted value, with no substituted objective or input law. -/
theorem LegalWeightedStationaryPoissonMatching.gridExchange_value_eq_unitSourceMean
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hg : Measurable (Function.uncurry probe))
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |probe a b| ≤ G)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε) :
    (M.gridExchange hk hkn hg hC hkb hgb S).value t =
      ∫ p : (Fin q → ℝ) × LegalMarkedOptimalInputScene q,
        originalWeightedSourceReadout kin probe t (legalMarkedUnitWindowWeight q)
          (originalGridExchangeScene S (p.2, p.1))
        ∂(cavityGridPhaseLaw (Fin q) ell).prod
          (M.law : Measure (LegalMarkedOptimalInputScene q)) := by
  let N := M.gridExchange hk hkn hg hC hkb hgb S
  have hwm : Measurable (legalMarkedUnitWindowWeight q) :=
    measurable_const.indicator (measurableSet_palmUnitCube (Fin q))
  have hread := N.weightedSourceReadout_integrable_and_integral hk hg t hwm
    (integrable_legalMarkedUnitWindowWeight q)
  have heq : (∫ s, originalWeightedSourceReadout kin probe t (legalMarkedUnitWindowWeight q) s
      ∂(N.law : Measure (LegalMarkedOptimalInputScene q))) = N.value t := by
    simpa only [integral_legalMarkedUnitWindowWeight, one_mul] using hread.2
  rw [← heq]
  change (∫ s, originalWeightedSourceReadout kin probe t (legalMarkedUnitWindowWeight q) s
    ∂((M.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (cavityGridPhaseLaw (Fin q) ell)).map (originalGridExchangeScene S)) = _
  rw [integral_map (measurable_originalGridExchangeScene S).aemeasurable
    hread.1.aestronglyMeasurable]
  exact (integral_prod_swap _).symm

/-- Actual global minimality forbids positive probability of the internally
selected original legal improving cycle in any fixed reference cell. -/
theorem LegalWeightedStationaryPoissonMatching.minimizer_originCycle_inactive
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hg : Measurable (Function.uncurry probe))
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |probe a b| ≤ G)
    (hmin : ∀ P : LegalWeightedStationaryPoissonMatching q α β kin probe, M.value t ≤ P.value t)
    (hε : 0 < ε)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε) :
    (M.law : Measure (LegalMarkedOptimalInputScene q)) S.active = 0 := by
  by_contra hpos
  have hstrict := (M.gridExchange_unitSourceReadout_strict_decrease
    hk hg hC hkb hgb hε S (lt_of_le_of_ne bot_le (Ne.symm hpos))).2
  rw [← M.gridExchange_value_eq_unitSourceMean hk hkn hg hC hkb hgb S] at hstrict
  exact (not_lt_of_ge (hmin (M.gridExchange hk hkn hg hC hkb hgb S))) hstrict

end OTSelector.Reconstruction
