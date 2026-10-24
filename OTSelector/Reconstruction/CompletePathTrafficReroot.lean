import OTSelector.Reconstruction.OriginalCompletePathEdgeTraffic

/-! # The literal original complete-path traffic is spatially stationary -/
open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- A physical reroot preserves both original clocks and full displacement. -/
theorem physicalPairAnchor_physicalSceneEdgeReroot {q : ℕ}
    (v : Fin q → ℝ) (e : LegalMarkedPhysicalEdge q) :
    physicalPairAnchor (physicalSceneEdgeReroot v e) =
      ((physicalPairAnchor e).1 - v, (physicalPairAnchor e).2) := by
  change (e.1.1 - v, ((e.1.2, e.2.2), (e.2.1 - v) - (e.1.1 - v))) =
    (e.1.1 - v, ((e.1.2, e.2.2), e.2.1 - e.1.1))
  congr 2
  abel

/-- Exact actual pair-kernel change of variables under the original joint reroot. -/
theorem lintegral_physicalScenePairKernel_reroot {q : ℕ}
    (v : Fin q → ℝ) (scene : LegalMarkedOptimalInputScene q)
    {G : ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q)) → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ a, G a ∂physicalScenePairKernel (legalMarkedInputSceneReroot q v scene).1) =
      ∫⁻ a, G (a.1 - v, a.2) ∂physicalScenePairKernel scene.1 := by
  let π : Measure (LegalMarkedPhysicalEdge q) := scene.1.1
  have hleft : (∫⁻ a, G a ∂physicalScenePairKernel
      (legalMarkedInputSceneReroot q v scene).1) =
      ∫⁻ e, G (physicalPairAnchor (physicalSceneEdgeReroot v e)) ∂π := by
    rw [physicalScenePairKernel_apply]
    change (∫⁻ a, G a ∂(π.map (physicalSceneEdgeReroot v)).map physicalPairAnchor) = _
    rw [Measure.map_map measurable_physicalPairAnchor
      (physicalSceneEdgeReroot v).continuous.measurable]
    exact lintegral_map hG
      (measurable_physicalPairAnchor.comp (physicalSceneEdgeReroot v).continuous.measurable)
  have hright : (∫⁻ a, G (a.1 - v, a.2) ∂physicalScenePairKernel scene.1) =
      ∫⁻ e, G ((physicalPairAnchor e).1 - v, (physicalPairAnchor e).2) ∂π := by
    rw [physicalScenePairKernel_apply]
    change (∫⁻ a, G (a.1 - v, a.2) ∂π.map physicalPairAnchor) = _
    exact lintegral_map (hG.comp ((measurable_fst.sub_const v).prodMk measurable_snd))
      measurable_physicalPairAnchor
  rw [hleft, hright]
  apply lintegral_congr_ae
  exact Eventually.of_forall fun e ↦ congrArg G (physicalPairAnchor_physicalSceneEdgeReroot v e)

/-- Rerooting an actual complete path translates only its physical smoothing
kernel; neither original clock endpoint nor full paired mark is changed. -/
theorem legalMarkedCompletePathTraffic_reroot {q : ℕ}
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    (v : Fin q → ℝ) (scene : LegalMarkedOptimalInputScene q) :
    legalMarkedCompletePathTraffic q d h f (legalMarkedInputSceneReroot q v scene) =
      legalMarkedCompletePathTraffic q d (fun x ↦ h (x - v)) f scene := by
  have hG : Measurable (fun a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
      ∫⁻ c : ℝ, h (a.1 + d (a.2, c)) * f (a.2, c) ∂volume) := by
    have hm := (hh.comp (measurable_fst.fst.add
      (hd.comp (measurable_fst.snd.prodMk measurable_snd)))).mul
      (hf.comp (measurable_fst.snd.prodMk measurable_snd))
    exact hm.lintegral_prod_right'
  unfold legalMarkedCompletePathTraffic
  rw [lintegral_physicalScenePairKernel_reroot v scene hG]
  apply lintegral_congr_ae
  filter_upwards [] with a
  apply lintegral_congr_ae
  filter_upwards [] with c
  have hx : a.1 - v + d (a.2, c) = a.1 + d (a.2, c) - v := by abel
  rw [hx]

/-- Every measurable nonnegative readout of the literal traffic has the same
expectation at each physical observation point on the original stationary law. -/
theorem LegalWeightedStationaryPoissonMatching.lintegral_completePathTraffic_shift
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ) (hd : Measurable d)
    {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f)
    {Φ : ℝ≥0∞ → ℝ≥0∞} (hΦ : Measurable Φ) (v : Fin q → ℝ) :
    (∫⁻ scene, Φ (legalMarkedCompletePathTraffic q d (fun x ↦ h (x - v)) f scene)
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q))) =
    ∫⁻ scene, Φ (legalMarkedCompletePathTraffic q d h f scene)
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  simp_rw [← legalMarkedCompletePathTraffic_reroot d hd hh hf v]
  have hm := hΦ.comp (measurable_legalMarkedCompletePathTraffic d hd hh hf)
  have he := lintegral_map hm (Q.stationary v).measurable
    (μ := (Q.law : Measure (LegalMarkedOptimalInputScene q)))
  rw [(Q.stationary v).map_eq] at he
  exact he.symm

end OTSelector.Reconstruction
