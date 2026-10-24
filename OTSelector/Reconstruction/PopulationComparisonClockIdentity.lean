import OTSelector.Reconstruction.FinslerPopulationJacobiDensity

/-!
# The original physical clock equals the actual comparison clock

The whole-seed density keeps the original readout and speed, whereas the endpoint
system is read from the smooth comparison. The identical central curve and actual
joint phase jet identify these two scalar clocks and velocities exactly.
-/

open Set Manifold
open scoped Topology ContDiff

namespace OTSelector.Reconstruction
open OTSelector.Geometry

variable {E M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The original potential-window readout gives exactly the comparison graph time. -/
theorem populationWindowGraphClock_eq_comparison
    (P : F.CalibratedSeedWindow u) (A : E ≃L[ℝ] (ℝ × V))
    {Γ : P.seed.covector.ker → ℝ → M} {w : P.seed.covector.ker}
    (hcurve : P.seed.curve w = Γ w) (t : ℝ) :
    populationWindowGraphClock P A w t = (A (P.comparisonReadout Γ (w, t))).1 := by
  change (A (extChartAt 𝓘(ℝ, E) (P.toManifold P.center) (P.seed.curve w t))).1 = _
  rw [hcurve]
  rfl

/-- The actual joint phase jet fixes the physical clock speed appearing in the
original conditional density, with the comparison's own positive graph speed. -/
theorem populationWindowGraphSpeed_eq_comparison
    (P : F.CalibratedSeedWindow u) (A : E ≃L[ℝ] (ℝ × V))
    {Γ : P.seed.covector.ker → ℝ → M} {w : P.seed.covector.ker} {t : ℝ}
    {D : (P.seed.covector.ker × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h₁ : HasFDerivAt (F.chartMomentumFamily (P.toManifold P.center) P.seed.curve) D (w, t))
    (h₂ : HasFDerivAt (F.chartMomentumFamily (P.toManifold P.center) Γ) D (w, t)) :
    populationWindowGraphSpeed P A w t =
      (fderiv ℝ (A ∘ P.comparisonReadout Γ) (w, t) (0, 1)).1 := by
  obtain ⟨hγ, hΓ⟩ := F.chartPosition_same_firstJet_of_chartMomentum
    (P.toManifold P.center) h₁ h₂
  have hd := (A.hasFDerivAt.comp (w, t) hγ).fderiv.trans
    (A.hasFDerivAt.comp (w, t) hΓ).fderiv.symm
  change fderiv ℝ (A ∘ P.comparisonReadout P.seed.curve) (w, t) =
    fderiv ℝ (A ∘ P.comparisonReadout Γ) (w, t) at hd
  exact congrArg (fun f : (P.seed.covector.ker × ℝ) →L[ℝ] ℝ × V ↦ (f (0, 1)).1) hd

end OTSelector.Reconstruction
