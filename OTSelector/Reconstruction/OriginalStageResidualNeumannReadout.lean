import OTSelector.Reconstruction.OriginalStageResidualNeumannReadoutPositiveSmoothing
import OTSelector.Reconstruction.OriginalStageResidualNeumannReadoutMeanZero
import OTSelector.Reconstruction.OriginalStageResidualNeumannReadoutIntegrability
import OTSelector.Reconstruction.OriginalStageResidualNeumannReadoutEndpoints

/-! Literal original stage densities, omitted-path derivatives and signed full-input reflection. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- The literal complete original source and target inputs keep their distinct slab classes. -/
def originalStageSignedReflectedInputError {q : ℕ}
    (η : (Fin q → ℝ) → ℝ) (R s t : ℝ)
    (scene : LegalMarkedOptimalInputScene q) (z : Fin q → ℝ) : ℝ :=
  originalClassReflectedInputScalarField η R (Ico s t) (legalInputColorMeasure q scene.2 0) z -
  originalClassReflectedInputScalarField η R (Ioc s t) (legalInputColorMeasure q scene.2 1) z

private theorem stage_pairing_of_pointwise_balance {q : ℕ} (σ : Measure (Fin q → ℝ))
    {core derivative sourceError targetError : (Fin q → ℝ) → ℝ}
    (hc : Integrable core σ) (hs : Integrable sourceError σ) (ht : Integrable targetError σ)
    (he : ∀ᵐ z ∂σ, core z = derivative z + sourceError z - targetError z)
    : Integrable derivative σ ∧
    ∀ (K : Compacts (Fin q → ℝ)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ)),
    (∫ z, core z * φ z ∂σ) = (∫ z, derivative z * φ z ∂σ) +
      (∫ z, sourceError z * φ z ∂σ) - ∫ z, targetError z * φ z ∂σ := by
  have hd : Integrable derivative σ := ((hc.sub hs).add ht).congr (by
    filter_upwards [he] with z hz
    change core z - sourceError z + targetError z = derivative z
    linarith)
  refine ⟨hd, ?_⟩
  intro K φ
  have hp {f : (Fin q → ℝ) → ℝ} (hf : Integrable f σ) :
      Integrable (fun z ↦ f z * φ z) σ := by
    simpa only [mul_comm] using smoothTest_mul_density_integrable K σ φ hf
  calc
    _ = ∫ z, derivative z * φ z + sourceError z * φ z - targetError z * φ z ∂σ := by
      apply integral_congr_ae
      filter_upwards [he] with z hz
      rw [hz]
      ring
    _ = _ := by
      rw [integral_sub (f := fun z ↦ derivative z * φ z + sourceError z * φ z)
        (g := fun z ↦ targetError z * φ z) ((hp hd).add (hp hs)) (hp ht),
        integral_add (hp hd) (hp hs)]


variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Actual stage densities have the literal omitted-slab derivative and complete original
signed reflected-input test identity on the same axisaligned cube. All port projection,
retained reflection cancellation, positive cut FTC, constants and integrability are produced. -/
theorem ae_all_originalStageResidualDensity_Neumann_readout
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η) (hηI : Integrable η volume)
    (hηone : ∫ x, η x = 1) (hηsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0)
    (hηeven : ∀ v w, (∀ i, |v i| = |w i|) → η v = η w)
    {M : ℝ} (hM : 0 ≤ M) (hηM : ∀ x, |η x| ≤ M) {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      Integrable (fun z ↦ originalOmittedSmoothedSlabDerivative S w R ell s t η z scene)
        (volume.restrict (haarRootCube _ R)) ∧
      ∀ A : OriginalStageResidualDensityData S w R ell η, A.scene = scene →
      ∀ (K : Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
        (φ : 𝓓_{K}(Fin (finrank ℝ S.covector.ker) → ℝ, ℝ)),
        (∫ z in haarRootCube _ R, φ z) = 0 →
      (∫ z in haarRootCube _ R, (A.sourceDensity s t z - A.targetDensity s t z) * φ z) =
        (∫ z in haarRootCube _ R,
          originalOmittedSmoothedSlabDerivative S w R ell s t η z scene * φ z) +
        (∫ z in haarRootCube _ R, originalClassReflectedInputScalarField η R (Ico s t)
          (legalInputColorMeasure _ scene.2 0) z * φ z) -
        (∫ z in haarRootCube _ R, originalClassReflectedInputScalarField η R (Ioc s t)
          (legalInputColorMeasure _ scene.2 1) z * φ z) := by
  have hRone : 1 ≤ R := by linarith
  have hηneg : ∀ v, η (-v) = η v := fun v ↦ hηeven (-v) v (by intro i; simp)
  filter_upwards [D.ae_all_originalOmittedSmoothedSlabDerivative_eq_positive_balance
      hF hw Q R ell hst,
    D.ae_all_originalStagePortDensities_eq_omittedRaw_add_reflectedInput hF hw Q hell hR s t,
    D.ae_all_originalStageResidualDensity_meanZero_test_pairing hF hw Q (by linarith)
      hR hRone hη.continuous.measurable hηI hηone hηsupport hηeven hηM (s := s) (t := t),
    D.ae_all_originalStageCore_reflectedInputErrors_integrable hF hw Q (by linarith)
      hR hRone hη.continuous.measurable hηI hηone hηsupport hηeven hM hηM s t]
    with scene hb hp hm hi
  let σ := volume.restrict (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)
  have he : ∀ᵐ z ∂σ, originalStageResidualCoreDensity S w R ell s t η scene z =
      originalOmittedSmoothedSlabDerivative S w R ell s t η z scene +
      originalClassReflectedInputScalarField η R (Ico s t) (legalInputColorMeasure _ scene.2 0) z -
      originalClassReflectedInputScalarField η R (Ioc s t) (legalInputColorMeasure _ scene.2 1) z := by
    filter_upwards [ae_restrict_mem (show MeasurableSet (haarRootCube _ R) from measurableSet_Icc)]
      with z hz
    have hpz := hp η hη.continuous.measurable M hM hηM hηsupport hηneg z hz
    have hbz := hb η hη hcη z
    dsimp only [originalStageResidualCoreDensity]
    rw [hpz.1, hpz.2]
    linarith
  obtain ⟨hd, hpair⟩ := stage_pairing_of_pointwise_balance σ hi.1 hi.2.1 hi.2.2 he
  refine ⟨hd, ?_⟩
  intro A hA K φ hφ
  rw [hm A hA K φ hφ]
  exact hpair K φ

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
