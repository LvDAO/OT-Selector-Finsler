import OTSelector.Reconstruction.FinslerOriginalReserveLiftingMeasurable
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputPalmNormalization
import OTSelector.Reconstruction.MarkedStationaryValuePalmMarginals
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalMeanMarginalFullness

/-!
# Palm computation for input-preserving scene repairs and the reserve limit

This module closes most of the Palm computation of the concrete reserve-repair
lifting and exposes the reserve limit arithmetic.

1. **Palm normalization and original marginals (proved).**  For any measurable
   scene map T which preserves the original colored input and commutes with every
   original reroot, and which produces full original matchings almost surely,
   the Palm of the pushed law is a probability measure with exactly the original
   source and target clock marginals (palm_normalization_of_sceneMap).  The proof
   uses the exact input-law preservation, the stationarity of the pushed law and
   the finite matching fullness only; it is the Palm computation of the reserve
   repair, with the concrete repair map as the only remaining choice.

2. **Palm integrability from domination (proved).**  If the pushed Palm is
   dominated by a finite multiple of the original Palm, the kinetic and probe
   integrability transfer (palm_integrable_of_dominated).  This is the exact
   remaining estimate needed to make the lifted law a weighted stationary
   matching.

3. **The completed lifting (proved modulo full matching, forwardness and the
   domination constant).**  Combining 1 and 2 gives a genuine weighted
   stationary matching with the repaired law and its Palm value
   (exists_stationary_lifting_of_sceneMap_palm).

4. **Reserve limit arithmetic (proved).**  The dilated weighted value tends to
   I_w(t) under continuity, and the explicit reserve cost tends to zero
   (tendsto_dilated_weightedInf, tendsto_reserveCost_zero), so the paper's
   finite-value comparison reduces to its a.e. finite-sample form
   (legalPressureLimit_le_weightedInf_of_reserveComparison, already assembled in
   FinslerOriginalReserveLiftingMeasurable).

## Remaining gap

The concrete measurable selection of the reserve repair map from the finite
completion, its Palm domination constant, and the a.e. finite-sample reserve cost
bound entering the expectation/box limit remain.  The Palm normalization, its
original marginals, the integrability transfer and the reserve limit arithmetic
are proved.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators Topology ENNReal NNReal ContDiff Matrix.Norms.Operator
  CompactlySupported

noncomputable section
namespace OTSelector.Reconstruction

open Module Manifold OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

local instance reserveRepairPlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) :=
  LocalFiniteMeasure.instPolishSpace

local instance reserveRepairInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) :=
  LocalFiniteMeasure.instPolishSpace

/-! ## 1. Palm normalization and original marginals -/

section PalmNormalization

variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- **Palm computation of an input-preserving reroot-equivariant scene repair.**
The pushed Palm is a probability measure with exactly the original source and
target clock marginals.  Only input-law preservation, the induced stationarity
and almost sure full matching are used; no property of the concrete repair rule
is required beyond the scene map axioms. -/
theorem palm_normalization_of_sceneMap
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (T : LegalMarkedOptimalInputScene q → LegalMarkedOptimalInputScene q)
    (hT : Measurable T) (hinput : ∀ s, (T s).2 = s.2)
    (hcomm : ∀ v : Fin q → ℝ,
      T ∘ legalMarkedInputSceneReroot q v = legalMarkedInputSceneReroot q v ∘ T)
    (hfull : ∀ᵐ s ∂((M.law.map hT.aemeasurable :
        ProbabilityMeasure (LegalMarkedOptimalInputScene q)).toMeasure),
      IsFullOriginalInputMatching q s) :
    IsProbabilityMeasure (legalMarkedJointPalm q (M.law.map hT.aemeasurable)) ∧
      (legalMarkedJointPalm q (M.law.map hT.aemeasurable)).map
        (fun m => m.1.1) = α ∧
      (legalMarkedJointPalm q (M.law.map hT.aemeasurable)).map
        (fun m => m.1.2) = β := by
  let Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q) :=
    M.law.map hT.aemeasurable
  have hstat : ∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q))
      (Q : Measure (LegalMarkedOptimalInputScene q)) :=
    map_law_stationary M T hT hcomm
  have hinput_law : (Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd =
      (M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd :=
    map_law_input_eq M T hT hinput
  have hfull' : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      IsFullOriginalInputMatching q s := hfull
  have hmeans := physicalScene_intensities_eq_inputColors q Q
    (hfull'.mono (fun s hs => ⟨hs.source_marginal, hs.target_marginal⟩))
  have hi0 : physicalSceneSourceIntensity (legalMarkedInputPairLaw q Q :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (volume : Measure (Fin q → ℝ)).prod α :=
    (hmeans.1).trans
      ((legalMarkedInputColorIntensity_eq_of_inputLaw_eq Q M.law hinput_law 0).trans
        M.inputColorIntensities_eq_volume_prod.1)
  have hi1 : physicalSceneTargetIntensity (legalMarkedInputPairLaw q Q :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) =
      (volume : Measure (Fin q → ℝ)).prod β :=
    (hmeans.2).trans
      ((legalMarkedInputColorIntensity_eq_of_inputLaw_eq Q M.law hinput_law 1).trans
        M.inputColorIntensities_eq_volume_prod.2)
  exact probability_cubePalm_physicalScenePairCampbell_clock_marginals
    (legalMarkedInputPairLaw q Q :
      Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
    (measurePreserving_legalMarkedInputPairLaw q Q hstat) α β hi0 hi1

end PalmNormalization

/-! ## 2. Palm integrability from domination -/

section PalmDomination

variable {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
  {g : ℝ → ℝ → ℝ}

/-- A finite domination of the pushed Palm by the original Palm transfers the
kinetic and probe integrability of the weighted stationary matching. -/
theorem palm_integrable_of_dominated
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (T : LegalMarkedOptimalInputScene q → LegalMarkedOptimalInputScene q)
    (hT : Measurable T) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hdom : legalMarkedJointPalm q (M.law.map hT.aemeasurable) ≤
      c • legalMarkedJointPalm q M.law) :
    Integrable (fun m => kin m.1.1 m.1.2 m.2)
        (legalMarkedJointPalm q (M.law.map hT.aemeasurable)) ∧
      Integrable (fun m => g m.1.1 m.1.2)
        (legalMarkedJointPalm q (M.law.map hT.aemeasurable)) :=
  ⟨(M.kinetic_integrable.smul_measure hc).mono_measure hdom,
    (M.probe_integrable.smul_measure hc).mono_measure hdom⟩

end PalmDomination

/-! ## 3. The completed lifting with computed Palm -/

section CompletedLifting

variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

/-- **Measurable stationary lifting with computed Palm.**  For a measurable
input-preserving reroot-equivariant scene map whose outputs are full legal
forward matchings almost surely and whose pushed Palm is finitely dominated by
the original Palm, the pushed law is a genuine weighted stationary matching of
the same original input laws.  All Palm fields are produced; only full matching,
forwardness and the domination constant are extra hypotheses. -/
theorem exists_stationary_lifting_of_sceneMap_palm
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (T : LegalMarkedOptimalInputScene q → LegalMarkedOptimalInputScene q)
    (hT : Measurable T) (hinput : ∀ s, (T s).2 = s.2)
    (hcomm : ∀ v : Fin q → ℝ,
      T ∘ legalMarkedInputSceneReroot q v = legalMarkedInputSceneReroot q v ∘ T)
    (hfull : ∀ᵐ s ∂((M.law.map hT.aemeasurable :
        ProbabilityMeasure (LegalMarkedOptimalInputScene q)).toMeasure),
      IsFullOriginalInputMatching q s)
    (hforward : ∀ᵐ s ∂((M.law.map hT.aemeasurable :
        ProbabilityMeasure (LegalMarkedOptimalInputScene q)).toMeasure),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support, e.1.2 < e.2.2)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hdom : legalMarkedJointPalm q (M.law.map hT.aemeasurable) ≤
      c • legalMarkedJointPalm q M.law)
    (t : ℝ) :
    ∃ M' : LegalWeightedStationaryPoissonMatching q α β kin g,
      M'.law = M.law.map hT.aemeasurable ∧
      M'.value t = (∫ m, kin m.1.1 m.1.2 m.2
          ∂legalMarkedJointPalm q (M.law.map hT.aemeasurable)) +
        t * ∫ m, g m.1.1 m.1.2 ∂legalMarkedJointPalm q (M.law.map hT.aemeasurable) := by
  obtain ⟨hpalm, hsource, htarget⟩ :=
    palm_normalization_of_sceneMap M T hT hinput hcomm hfull
  obtain ⟨hkin, hprobe⟩ := palm_integrable_of_dominated M T hT hc hdom
  have hfull_orig : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      IsFullOriginalInputMatching q (T s) :=
    (ae_map_iff hT.aemeasurable (measurableSet_isFullOriginalInputMatching q)).mp hfull
  exact exists_stationary_lifting_of_sceneMap M T hT hinput hcomm hfull_orig hforward
    hpalm hsource htarget hkin hprobe

end CompletedLifting

/-! ## 4. Reserve limit arithmetic -/

section ReserveLimit

/-- The normalization factors of the finite-value comparison tend to one. -/
theorem tendsto_dilated_factor (e : ℝ) :
    Tendsto (fun rho : ℝ => (1 - rho) ^ e) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  tendsto_one_sub_rpow e

/-- The explicit reserve cost C rho^(1-2/q) + C|t|G rho tends to zero. -/
theorem tendsto_reserveCost_zero {q : ℕ} (hq : 2 < q) (C G t : ℝ) :
    Tendsto (fun rho : ℝ => C * rho ^ (1 - 2 / (q : ℝ)) + C * |t| * G * rho)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hqR : (2 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hexp : (0 : ℝ) < 1 - 2 / (q : ℝ) := by
    rw [sub_pos, div_lt_one hq0]
    linarith
  have hrho : Tendsto (fun rho : ℝ => rho) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun rho : ℝ => rho ^ (1 - 2 / (q : ℝ))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (tendsto_rpow_neg_nhdsGT_zero (y := -(1 - 2 / (q : ℝ)))
      (by linarith)).inv_tendsto_atTop
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with rho hrho'
    change (rho ^ (-(1 - 2 / (q : ℝ))))⁻¹ = rho ^ (1 - 2 / (q : ℝ))
    rw [Real.rpow_neg hrho'.le]
    simp
  have h2 : Tendsto (fun rho : ℝ => C * rho ^ (1 - 2 / (q : ℝ)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (h1.const_mul C)
  have h3 : Tendsto (fun rho : ℝ => C * |t| * G * rho) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (hrho.const_mul (C * |t| * G))
  simpa using h2.add h3

/-- The dilated weighted value tends to the weighted value at the fixed tilt,
under continuity in the tilt. -/
theorem tendsto_dilated_weightedInf {q : ℕ} (I : ℝ → ℝ) {t : ℝ}
    (hI : ContinuousAt I t) :
    Tendsto (fun rho : ℝ => (1 - rho) ^ (1 - 2 / (q : ℝ)) * I (t * (1 - rho) ^ (2 / (q : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 (I t)) := by
  have ha : Tendsto (fun rho : ℝ => (1 - rho) ^ (1 - 2 / (q : ℝ)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_one_sub_rpow _
  have hc : Tendsto (fun rho : ℝ => (1 - rho) ^ (2 / (q : ℝ)))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_one_sub_rpow _
  have harg : Tendsto (fun rho : ℝ => t * (1 - rho) ^ (2 / (q : ℝ)))
      (𝓝[>] (0 : ℝ)) (𝓝 t) := by
    have h := (tendsto_const_nhds (x := t)).mul hc
    simpa only [mul_one] using h
  have hIarg : Tendsto (fun rho : ℝ => I (t * (1 - rho) ^ (2 / (q : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 (I t)) := hI.tendsto.comp harg
  have hprod := ha.mul hIarg
  simpa only [one_mul] using hprod

end ReserveLimit

end OTSelector.Reconstruction
