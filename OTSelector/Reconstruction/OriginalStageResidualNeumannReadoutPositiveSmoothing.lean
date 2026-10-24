import OTSelector.Reconstruction.OriginalRetainedSlabResidualReadouts
import OTSelector.Reconstruction.OriginalEuclideanMollifierChoice

/-! Actual omitted-path smoothing is the literal positive-cut clock-slab derivative. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual omitted source endpoint smoothing uses exactly the original source half slab. -/
def originalOmittedRawSlabSourceDensity (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R ell s t : ℝ)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (z : Fin (finrank ℝ S.covector.ker) → ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  ∫ x, η (x-z) ∂originalRestrictedSceneSlabSourceMeasure
    (originalPathLengthRetained S w R ell)ᶜ s t scene

/-- The actual omitted target endpoint smoothing keeps the original target half slab. -/
def originalOmittedRawSlabTargetDensity (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R ell s t : ℝ)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (z : Fin (finrank ℝ S.covector.ker) → ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  ∫ x, η (x-z) ∂originalRestrictedSceneSlabTargetMeasure
    (originalPathLengthRetained S w R ell)ᶜ s t scene

/-- The literal negative clock-occupation derivative of every original omitted path.
The physical source and target clocks, velocities and positions are left unchanged. -/
def originalOmittedSmoothedSlabDerivative (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker) (R ell s t : ℝ)
    (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ)
    (z : Fin (finrank ℝ S.covector.ker) → ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) : ℝ :=
  -(∫ a in (originalPathLengthRetained S w R ell)ᶜ,
    (∫ c in Ioc s t,
      fderiv ℝ (fun x ↦ η (x-z)) (a.1 + originalSeedPathOffset S w c a.2)
        (originalSeedClockOccupation S w c a.2) ∂volume)
      ∂physicalScenePairKernel scene.1)

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Actual positive-cut FTC applied to every translated smooth kernel gives the literal
omitted slab balance, including every exterior endpoint's true incoming and outgoing cut. -/
theorem ae_all_originalOmittedSmoothedSlabDerivative_eq_positive_balance
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (R ell : ℝ) {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ,
        ContDiff ℝ 1 η → HasCompactSupport η → ∀ z,
      originalOmittedSmoothedSlabDerivative S w R ell s t η z scene =
        originalOmittedRawSlabSourceDensity S w R ell s t η z scene -
        originalOmittedRawSlabTargetDensity S w R ell s t η z scene +
        originalOmittedCutDensity S w R ell s η z scene -
        originalOmittedCutDensity S w R ell t η z scene := by
  filter_upwards [D.ae_all_originalRestrictedWeakSlab_integrable_balance hF hw Q
    (originalPathLengthRetained S w R ell)ᶜ hst,
    D.ae_all_originalRestrictedClockSlab_testDerivative_eq_weakSlab Q] with scene hb hd
  intro η hη hcη z
  let ψ := fun x ↦ η (x-z)
  have hψ : ContDiff ℝ 1 ψ := hη.comp (contDiff_id.sub contDiff_const)
  have hcψ : HasCompactSupport ψ := by
    simpa only [ψ, Function.comp_def, Homeomorph.coe_addRight, sub_eq_add_neg] using
      hcη.comp_homeomorph (Homeomorph.addRight (-z))
  have h := (hb ψ hψ hcψ).2
  rw [← hd (originalPathLengthRetained S w R ell)ᶜ ψ s t hst] at h
  exact h

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
