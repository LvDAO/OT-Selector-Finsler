import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalActualGridExchangeStationarity
import OTSelector.Reconstruction.MarkedStationaryValueLegalCanonicalFirstInputScene
import OTSelector.Reconstruction.MarkedStationaryValueLegalConditionedMatching

/-! # Actual full original-input and Palm laws of the stationary competitor -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
local instance originalGridExchangeLawPlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace
local instance originalGridExchangeLawInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
variable {q : ℕ} {ell ε : ℝ} [hell : Fact (0 < ell)]
  {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
  {probe : ℝ → ℝ → ℝ} {t : ℝ}

/-- The entire original colored input law, including all its correlations,
is exactly unchanged by the concrete stationary exchange. -/
theorem map_originalGridExchangeLaw_input
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    (originalGridExchangeLaw S Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd =
      (Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd := by
  change (((Q : Measure (LegalMarkedOptimalInputScene q)).prod
    (cavityGridPhaseLaw (Fin q) ell)).map (originalGridExchangeScene S)).map Prod.snd = _
  rw [Measure.map_map measurable_snd (measurable_originalGridExchangeScene S)]
  have hcomp : Prod.snd ∘ originalGridExchangeScene S =
      (Prod.snd : LegalMarkedOptimalInputScene q → LocalFiniteMeasure (LegalColoredInputPoint q)) ∘
        Prod.fst := rfl
  rw [hcomp, ← Measure.map_map measurable_snd measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- The actual competitor remains a full matching of every unchanged input. -/
theorem LegalWeightedStationaryPoissonMatching.gridExchangeLaw_full_matching
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε) :
    ∀ᵐ s ∂(originalGridExchangeLaw S M.law : Measure (LegalMarkedOptimalInputScene q)),
      IsFullOriginalInputMatching q s := by
  change ∀ᵐ s ∂((M.law : Measure (LegalMarkedOptimalInputScene q)).prod
    (cavityGridPhaseLaw (Fin q) ell)).map (originalGridExchangeScene S), _
  apply (ae_map_iff (measurable_originalGridExchangeScene S).aemeasurable
    (measurableSet_isFullOriginalInputMatching q)).mpr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae M.full_matching] with p hp
  exact hp.gridExchange hell.out S p.2

/-- Every occupied edge under the actual exchanged law has both original
clocks strictly ordered. -/
theorem LegalWeightedStationaryPoissonMatching.gridExchangeLaw_forward
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε) :
    ∀ᵐ s ∂(originalGridExchangeLaw S M.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2 := by
  let B : Set (LegalMarkedPhysicalEdge q) := {e | ¬ e.1.2 < e.2.2}
  have hB : MeasurableSet B := (measurableSet_lt measurable_fst.snd measurable_snd.snd).compl
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) B) :=
    (Measure.measurable_coe hB).comp (measurable_localFiniteMeasure_coe.comp measurable_fst.fst)
  have hz : ∀ᵐ s ∂(originalGridExchangeLaw S M.law : Measure (LegalMarkedOptimalInputScene q)),
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) B = 0 := by
    change ∀ᵐ s ∂((M.law : Measure (LegalMarkedOptimalInputScene q)).prod
      (cavityGridPhaseLaw (Fin q) ell)).map (originalGridExchangeScene S), _
    apply (ae_map_iff (measurable_originalGridExchangeScene S).aemeasurable
      (measurableSet_eq_fun hm measurable_const)).mpr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae M.full_matching,
      Measure.quasiMeasurePreserving_fst.ae M.forward] with p hp hf
    have hnew := hp.forward_gridExchange hf hell.out S p.2
    exact measure_mono_null (fun e he hmem ↦ he (hnew e hmem))
      ((originalGridExchangeScene S p).1.1 : Measure (LegalMarkedPhysicalEdge q)).measure_compl_support
  filter_upwards [M.gridExchangeLaw_full_matching S, hz] with s hs hz
  apply forall_support_of_ae_of_legalCounting (0 : LegalMarkedPhysicalEdge q) s.1.1
    ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
    (P := fun e ↦ e.1.2 < e.2.2)
  exact ae_iff.mpr hz

/-- Exact original intensity and whole-marginal conservation internally
normalize the true competitor Palm and recover both original scalar marginals. -/
theorem LegalWeightedStationaryPoissonMatching.gridExchangeLaw_palm_normalization
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε) :
    IsProbabilityMeasure (legalMarkedJointPalm q (originalGridExchangeLaw S M.law)) ∧
      (legalMarkedJointPalm q (originalGridExchangeLaw S M.law)).map (fun m ↦ m.1.1) = α ∧
      (legalMarkedJointPalm q (originalGridExchangeLaw S M.law)).map (fun m ↦ m.1.2) = β := by
  let Q := originalGridExchangeLaw S M.law
  have hfull := M.gridExchangeLaw_full_matching S
  have hmeans := physicalScene_intensities_eq_inputColors q Q
    (hfull.mono (fun _ hs ↦ ⟨hs.source_marginal, hs.target_marginal⟩))
  have hi0 := (legalMarkedInputColorIntensity_eq_of_inputLaw_eq Q M.law
    (map_originalGridExchangeLaw_input S M.law) 0).trans
      M.inputColorIntensities_eq_volume_prod.1
  have hi1 := (legalMarkedInputColorIntensity_eq_of_inputLaw_eq Q M.law
    (map_originalGridExchangeLaw_input S M.law) 1).trans
      M.inputColorIntensities_eq_volume_prod.2
  exact probability_cubePalm_physicalScenePairCampbell_clock_marginals _
    (measurePreserving_legalMarkedInputPairLaw q Q
      (measurePreserving_originalGridExchangeLaw S M.law M.stationary)) α β
    (hmeans.1.trans hi0) (hmeans.2.trans hi1)

end OTSelector.Reconstruction
