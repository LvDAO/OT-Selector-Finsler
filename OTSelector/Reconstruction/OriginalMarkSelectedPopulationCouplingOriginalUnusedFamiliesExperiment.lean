import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockOrientedFamilyScalar

/-! Both original global reserve families in one original unit-Q/raw-reserve experiment. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
namespace LegalWeightedStationaryPoissonMatching
variable {q : ℕ} {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g)

/-- The actual original unit matching and two raw reserve clouds construct
both global RN families on one AE event. Any nonnegative reserve intensity is
allowed; the whole-scene/FULL witnesses never enter the iid auxiliary. -/
theorem originalGlobalReserveAtomLaws
    (G : OriginalStageClockGrid) (h₀ : G.clockSlabSurplus μ ν 0 = 0)
    (hN : G.clockSlabSurplus μ ν G.count = 0)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 ≤ ρ) (hq : 4 < q) :
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    let M := originalMainReserveExperimentLaw Q (Real.toNNReal ρ*(volume K).toNNReal)
    let Hs := G.sourceReserveFineBlockPartition h₀ hN
    let Ht := G.targetReserveFineBlockPartition h₀ hN
    let Es := Hs.atomEnergy b R 0 1 ∘ originalSourceReserveExperimentSplice
    let Et := Ht.atomEnergy b R 1 0 ∘ originalTargetReserveExperimentSplice
    (∀ᵐ p ∂M, Hs.AtomSpec b R 0 1 (originalSourceReserveExperimentSplice p) ∧
      Ht.AtomSpec b R 1 0 (originalTargetReserveExperimentSplice p)) ∧
      Integrable Es M ∧ Integrable Et M ∧
      (∫ p, Es p + Et p ∂M) / volume.real K ≤
        2*(G.count : ℝ)*((q : ℝ)*dyadicMatchingConstant q*ρ^(1-2/(q : ℝ))) := by
  let K := originalCenteredPhysicalCubeRegion b (2*R)
  let rate := Real.toNNReal ρ*(volume K).toNNReal
  let M := originalMainReserveExperimentLaw Q rate
  let Ps := (Q.law : Measure (LegalMarkedOptimalInputScene q)).prod (markedPoissonLaw q ℝ ν rate)
  let Pt := (Q.law : Measure (LegalMarkedOptimalInputScene q)).prod (markedPoissonLaw q ℝ μ rate)
  have hs := G.sourceReserveGlobalAtomLaws h₀ hN Ps b hR hρ hq
  have ht := G.targetReserveGlobalAtomLaws h₀ hN Pt b hR hρ hq
  have hms : Measurable (originalSourceReserveExperimentSplice (q := q)) := by
    unfold originalSourceReserveExperimentSplice
    fun_prop
  have hmt : Measurable (originalTargetReserveExperimentSplice (q := q)) := by
    unfold originalTargetReserveExperimentSplice
    fun_prop
  have hps : MeasurePreserving originalSourceReserveExperimentSplice M (Ps.prod (markedPoissonLaw q ℝ μ rate)) :=
    ⟨hms, map_originalSourceReserveExperimentSplice Q rate⟩
  have hpt : MeasurePreserving originalTargetReserveExperimentSplice M (Pt.prod (markedPoissonLaw q ℝ ν rate)) :=
    ⟨hmt, map_originalTargetReserveExperimentSplice Q rate⟩
  have his := hps.integrable_comp_of_integrable hs.2.1
  have hit := hpt.integrable_comp_of_integrable ht.2.1
  refine ⟨?_, his, hit, ?_⟩
  · filter_upwards [hps.quasiMeasurePreserving.ae hs.1, hpt.quasiMeasurePreserving.ae ht.1] with p hp hq
    exact ⟨hp,hq⟩
  · have hbs := (congrArg (fun t : ℝ ↦ t / volume.real K)
      (hps.hasLaw.integral_comp hs.2.1.aestronglyMeasurable)).trans_le hs.2.2
    have hbt := (congrArg (fun t : ℝ ↦ t / volume.real K)
      (hpt.hasLaw.integral_comp ht.2.1.aestronglyMeasurable)).trans_le ht.2.2
    rw [integral_add his hit, add_div]
    exact (add_le_add hbs hbt).trans_eq (by ring)

end LegalWeightedStationaryPoissonMatching
end OTSelector.Reconstruction
