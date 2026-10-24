import OTSelector.Reconstruction.FinslerRelativeLawOriginalMicrocellBinomialMean
import OTSelector.Reconstruction.FinslerRelativeLawOriginalGridBoxProbability

/-! Original Haar/class physical means agree with the exact homogeneous-grid binomial parameters. -/
open Set Function MeasureTheory ProbabilityTheory Filter BoxIntegral
open scoped Topology ENNReal NNReal BigOperators unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {q : ℕ}

/-- The positive original subcell mean eventually has precisely the probability
used by the homogeneous microscopic model. The same Haar factor is chosen
before all class masses, cells and scales; no full-box probability premise
remains at the caller. -/
theorem exists_original_grid_haar_class_binomial_mean_laws
    (μ : Measure E) [μ.IsAddHaarMeasure] (e : E ≃L[ℝ] (Fin q → ℝ)) (hq : 0 < q) :
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ (classMass : ℝ≥0) (L : ℝ), 0 < L →
      ∀ (s : Set E) (hs : MeasurableSet s)
        (A B : Type*) [MeasurableSpace A] [MeasurableSpace B]
        (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
        (source : A → ℝ) (target : B → ℝ), Measurable source → Measurable target →
      ∀ (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ),
      Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)) →
      Measurable (Function.uncurry probe) → ∀ tilt : ℝ,
      ∀ᶠ N : ℕ in atTop, ∀ (ν : Fin q → ℤ)
        (hmass : μ (s ∩ e ⁻¹' (unitPartition.box (positiveMicroscopicGridOrder q L N) ν :
          Set (Fin q → ℝ))) ≠ 0),
      let n := positiveMicroscopicGridOrder q L N
      let K := s ∩ e ⁻¹' (unitPartition.box n ν : Set (Fin q → ℝ))
      let _inst := normalized_original_unitPartitionCell_probability μ e n ν
        (hs.inter ((unitPartition.box n ν).measurableSet_coe.preimage e.continuous.measurable))
        inter_subset_right hmass
      let originalLaw := (blockDataLaw ((normalizedFiniteLaw (μ.restrict K)).prod α)
        (binomWeight N (μ K * (classMass : ℝ≥0∞)).toNNReal)).prod
          (blockDataLaw ((normalizedFiniteLaw (μ.restrict K)).prod β)
            (binomWeight N (μ K * (classMass : ℝ≥0∞)).toNNReal))
      (∫ d, unclampedBlockLegalTilted q source target N kin probe tilt
        (mapBlockData (Prod.map e id) d.1) (mapBlockData (Prod.map e id) d.2) ∂originalLaw) =
        affineClassBinomialShapeExpectation source target α β N
          (positiveMicroscopicCubeProbability q (c * classMass) L N) ((n : ℝ≥0)⁻¹)
          (fun l ↦ (ν l : ℝ) / n) (originalMicrocellShape e n ν s) kin probe tilt := by
  obtain ⟨c, hc, hmean⟩ := exists_original_microcell_binomial_mean_laws μ e
  refine ⟨c, hc, ?_⟩
  intro classMass L hL s hs A B _ _ α _ β _ source target hsource htarget kin probe hk hp tilt
  filter_upwards [eventually_positiveMicroscopicCubeProbability_eq_original_box hq (c * classMass) hL]
    with N hN
  intro ν hmass
  have h := (hmean classMass s hs (positiveMicroscopicGridOrder q L N) ν N hmass hN.1
    A B α β source target hsource htarget kin probe hk hp tilt).2
  let p : unitInterval := ⟨((c * classMass) *
      (((positiveMicroscopicGridOrder q L N : ℝ≥0)⁻¹) ^ q) : ℝ≥0),
    NNReal.coe_nonneg _, (by exact_mod_cast hN.1)⟩
  have hprob : p = positiveMicroscopicCubeProbability q (c * classMass) L N :=
    Subtype.ext hN.2.symm
  dsimp only at h ⊢
  change _ = affineClassBinomialShapeExpectation source target α β N p
    ((positiveMicroscopicGridOrder q L N : ℝ≥0)⁻¹)
    (fun l ↦ (ν l : ℝ) / positiveMicroscopicGridOrder q L N)
    (originalMicrocellShape e (positiveMicroscopicGridOrder q L N) ν s) kin probe tilt at h
  rw [hprob] at h
  exact h

end OTSelector.Reconstruction
