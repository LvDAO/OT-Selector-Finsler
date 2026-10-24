import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalUnitSourcePalmIntegrability
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalGridExchangeLawMatching

/-! The actual exchanged original law retains true Palm kinetic integrability. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {probe : ℝ → ℝ → ℝ} {t : ℝ}
  {ell ε : ℝ} [hell : Fact (0 < ell)]

/-- The actual normalized true Palm of the concrete same-input stationary
grid exchange has finite kinetic energy. All local/global integrability is
produced from the original law and its already proved quadratic coefficient bound. -/
theorem LegalWeightedStationaryPoissonMatching.gridExchangeLaw_kinetic_integrable
    (M : LegalWeightedStationaryPoissonMatching q α β kin probe)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hg : Measurable (Function.uncurry probe))
    {C G : ℝ} (hC : 0 ≤ C)
    (hkb : ∀ a b v, |kin a b v| ≤ C * ∑ i, v i ^ 2)
    (hgb : ∀ a b, |probe a b| ≤ G)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε) :
    Integrable (fun m : PhysicalPairPalmMark (Fin q) ↦ kin m.1.1 m.1.2 m.2)
      (legalMarkedJointPalm q (originalGridExchangeLaw S M.law)) := by
  let Q := originalGridExchangeLaw S M.law
  let P := (M.law : Measure (LegalMarkedOptimalInputScene q)).prod
    (cavityGridPhaseLaw (Fin q) ell)
  let k : PhysicalPairPalmMark (Fin q) → ℝ := fun m ↦ kin m.1.1 m.1.2 m.2
  let p : PhysicalPairPalmMark (Fin q) → ℝ := fun m ↦ probe m.1.1 m.1.2
  let c : PhysicalPairPalmMark (Fin q) → ℝ := fun m ↦ k m + t * p m
  have hkm : Measurable k := hk
  have hpm : Measurable p := hg.comp measurable_fst
  have hcm : Measurable c := hkm.add (hpm.const_mul t)
  have hprob := (M.gridExchangeLaw_palm_normalization S).1
  let : IsProbabilityMeasure (legalMarkedJointPalm q Q) := hprob
  have hpi : Integrable p (legalMarkedJointPalm q Q) := by
    apply (integrable_const G).mono' hpm.aestronglyMeasurable
    exact Eventually.of_forall (fun m ↦ by simpa only [Real.norm_eq_abs] using hgb m.1.1 m.1.2)
  have hpf : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      Integrable p (legalMarkedSceneUnitPalmKernel q s) := by
    rw [legalMarkedJointPalm_eq_unitPalmKernel_comp] at hpi
    exact Measure.ae_integrable_of_integrable_comp hpi
  have hpr : Integrable (legalMarkedScenePalmReadout q p)
      (Q : Measure (LegalMarkedOptimalInputScene q)) := integrable_legalMarkedScenePalmReadout Q hpi
  have hrepr (s : LegalMarkedOptimalInputScene q) :
      legalMarkedScenePalmReadout q c s =
        originalWeightedSourceReadout kin probe t (legalMarkedUnitWindowWeight q) s := by
    exact legalMarkedScenePalmReadout_eq_originalUnitSourceMarkReadout c hcm s
  have hcf : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      Integrable c (legalMarkedSceneUnitPalmKernel q s) := by
    change ∀ᵐ s ∂P.map (originalGridExchangeScene S), _
    have hset : MeasurableSet {s | Integrable c (legalMarkedSceneUnitPalmKernel q s)} :=
      ProbabilityTheory.measurableSet_integrable hcm.stronglyMeasurable
    apply (ae_map_iff (measurable_originalGridExchangeScene S).aemeasurable hset).mpr
    have hwm : Measurable (legalMarkedUnitWindowWeight q) :=
      measurable_const.indicator (measurableSet_palmUnitCube (Fin q))
    have hfiber := M.ae_integrable_sourceWindow_cost (t := t) hk hg hwm
      (integrable_legalMarkedUnitWindowWeight q)
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae M.full_matching,
      Measure.quasiMeasurePreserving_fst.ae hfiber] with z hz hi
    have hwK : ∀ x ∉ palmUnitCube (Fin q), legalMarkedUnitWindowWeight q x = 0 :=
      fun _ hx ↦ Set.indicator_of_notMem hx _
    have hnew := hz.gridExchange_sourceWindow_integrable_and_gain hell.out S z.2
      (legalMarkedUnitWindowWeight q) (show IsCompact (palmUnitCube (Fin q)) from isCompact_Icc)
      hwK hi
    exact (integrable_originalUnitSourceMark_iff c hcm _).mpr hnew.1
  have hcr : Integrable (legalMarkedScenePalmReadout q c)
      (Q : Measure (LegalMarkedOptimalInputScene q)) := by
    have hwm : Measurable (legalMarkedUnitWindowWeight q) :=
      measurable_const.indicator (measurableSet_palmUnitCube (Fin q))
    have hwK : ∀ x ∉ palmUnitCube (Fin q), legalMarkedUnitWindowWeight q x = 0 :=
      fun _ hx ↦ Set.indicator_of_notMem hx _
    have hread := M.gridExchange_sourceReadout_integrable_and_integral hk hg hC hkb hgb S hwm
      (integrable_legalMarkedUnitWindowWeight q)
      (show IsCompact (palmUnitCube (Fin q)) from isCompact_Icc) hwK
    have hm : Measurable (legalMarkedScenePalmReadout q c) :=
      hcm.stronglyMeasurable.integral_kernel.measurable
    change Integrable (legalMarkedScenePalmReadout q c) (P.map (originalGridExchangeScene S))
    apply (integrable_map_measure hm.aestronglyMeasurable
      (measurable_originalGridExchangeScene S).aemeasurable).mpr
    convert hread.1.swap using 1
    funext z
    exact hrepr (originalGridExchangeScene S z)
  have hkf : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      Integrable k (legalMarkedSceneUnitPalmKernel q s) := by
    filter_upwards [hcf, hpf] with s hc hp
    convert hc.sub (hp.const_mul t) using 1
    funext m
    change k m = (k m + t * p m) - t * p m
    ring
  have heq : legalMarkedScenePalmReadout q k =ᵐ[(Q : Measure (LegalMarkedOptimalInputScene q))]
      (fun s ↦ legalMarkedScenePalmReadout q c s - t * legalMarkedScenePalmReadout q p s) := by
    filter_upwards [hkf, hpf] with s hk hp
    dsimp only [legalMarkedScenePalmReadout]
    rw [show c = (fun m ↦ k m + t * p m) from rfl,
      integral_add hk (hp.const_mul t), integral_const_mul]
    ring
  have hkr : Integrable (legalMarkedScenePalmReadout q k)
      (Q : Measure (LegalMarkedOptimalInputScene q)) :=
    (hcr.sub (hpr.const_mul t)).congr heq.symm
  exact integrable_nonneg_jointPalm_of_scene_readout Q k hkm
    (fun m ↦ hkn m.1.1 m.1.2 m.2) hkf hkr

end OTSelector.Reconstruction
