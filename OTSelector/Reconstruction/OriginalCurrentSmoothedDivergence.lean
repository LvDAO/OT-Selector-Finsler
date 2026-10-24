import OTSelector.Reconstruction.OriginalCubeTraceCompactnessSceneSmoothness

/-! Actual divergence of compact-kernel smoothing of the same original path occupation. -/

open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal BigOperators Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

private theorem sum_coordinate_dual_contraction {q : ℕ}
    (L : (Fin q → ℝ) →L[ℝ] ℝ) (v : Fin q → ℝ) :
    (∑ i : Fin q, (-(L (Pi.single i 1))) * v i) = -(L v) := by
  classical
  have hv : (∑ i : Fin q, v i • Pi.single i (1 : ℝ)) = v := by
    ext i
    simp [Pi.smul_apply, Pi.single_apply]
  calc
    (∑ i : Fin q, (-(L (Pi.single i 1))) * v i) =
        -(∑ i : Fin q, v i * L (Pi.single i 1)) := by
      simp only [neg_mul, Finset.sum_neg_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun i _ ↦ mul_comm _ _)
    _ = -(L (∑ i : Fin q, v i • Pi.single i 1)) := by
      simp only [map_sum, _root_.map_smul, smul_eq_mul]
    _ = -(L v) := by rw [hv]

private theorem integrable_smoothed_coordinate_contraction
    {P : Type*} [MeasurableSpace P] {q : ℕ} {σ : Measure P}
    {X V : P → (Fin q → ℝ)} {η : (Fin q → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hX : Measurable X) (hV : AEStronglyMeasurable V σ)
    (htraffic : ∀ B : Set (Fin q → ℝ), IsCompact B →
      Integrable (fun p ↦ B.indicator (fun _ ↦ ‖V p‖) (X p)) σ)
    (z : Fin q → ℝ) (i : Fin q) :
    Integrable (fun p ↦ (-(fderiv ℝ η (X p - z) (Pi.single i 1))) * V p i) σ := by
  have hd := integrable_compact_kernel_current_derivative hη hcη hX hV htraffic z
  have hv := hd.apply_continuousLinearMap (Pi.single i 1)
  simpa only [ContinuousLinearMap.smulRight_apply, neg_apply, ContinuousLinearMap.proj_apply,
    Pi.smul_apply, smul_eq_mul]
    using (ContinuousLinearMap.proj i : (Fin q → ℝ) →L[ℝ] ℝ).integrable_comp hv

/-- The literal pairing of the differentiated compact kernel with the original vector traffic
is integrable; this is produced from local traffic, not assumed for the divergence identity. -/
theorem integrable_compact_kernel_gradientPairing
    {P : Type*} [MeasurableSpace P] {q : ℕ} {σ : Measure P}
    {X V : P → (Fin q → ℝ)} {η : (Fin q → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hX : Measurable X) (hV : AEStronglyMeasurable V σ)
    (htraffic : ∀ B : Set (Fin q → ℝ), IsCompact B →
      Integrable (fun p ↦ B.indicator (fun _ ↦ ‖V p‖) (X p)) σ)
    (z : Fin q → ℝ) : Integrable (fun p ↦ fderiv ℝ η (X p - z) (V p)) σ := by
  classical
  have hs := integrable_finsetSum Finset.univ
    (fun i _ ↦ integrable_smoothed_coordinate_contraction hη hcη hX hV htraffic z i)
  have heq : (fun p ↦ ∑ i : Fin q,
      (-(fderiv ℝ η (X p - z) (Pi.single i 1))) * V p i) =
      fun p ↦ -(fderiv ℝ η (X p - z) (V p)) :=
    funext (fun p ↦ sum_coordinate_dual_contraction _ _)
  rw [heq] at hs
  simpa only [neg_neg] using hs.fun_neg

/-- The actual divergence of the smoothed traffic is the negative integral of the kernel's
actual Fréchet derivative applied to the same vector occupation. -/
theorem divergence_compact_kernel_current
    {P : Type*} [MeasurableSpace P] {q : ℕ} {σ : Measure P}
    {X V : P → (Fin q → ℝ)} {η : (Fin q → ℝ) → ℝ}
    (hη : ContDiff ℝ 1 η) (hcη : HasCompactSupport η)
    (hX : Measurable X) (hV : AEStronglyMeasurable V σ)
    (htraffic : ∀ B : Set (Fin q → ℝ), IsCompact B →
      Integrable (fun p ↦ B.indicator (fun _ ↦ ‖V p‖) (X p)) σ)
    (z : Fin q → ℝ) :
    (∑ i : Fin q, fderiv ℝ (fun z ↦ ∫ p, η (X p - z) • V p ∂σ) z
        (Pi.single i 1) i) = -(∫ p, fderiv ℝ η (X p - z) (V p) ∂σ) := by
  classical
  have hd := integrable_compact_kernel_current_derivative hη hcη hX hV htraffic z
  have heval (i : Fin q) :
      fderiv ℝ (fun z ↦ ∫ p, η (X p - z) • V p ∂σ) z (Pi.single i 1) i =
        ∫ p, (-(fderiv ℝ η (X p - z) (Pi.single i 1))) * V p i ∂σ := by
    rw [fderiv_compact_kernel_current_apply hη hcη hX hV htraffic z]
    simpa only [ContinuousLinearMap.smulRight_apply, neg_apply, ContinuousLinearMap.proj_apply,
      Pi.smul_apply, smul_eq_mul]
      using ((ContinuousLinearMap.proj i : (Fin q → ℝ) →L[ℝ] ℝ).integral_comp_comm
        (hd.apply_continuousLinearMap (Pi.single i 1))).symm
  simp_rw [heval]
  rw [← integral_finsetSum Finset.univ
    (fun i _ ↦ integrable_smoothed_coordinate_contraction hη hcη hX hV htraffic z i)]
  simp_rw [sum_coordinate_dual_contraction]
  exact integral_neg _

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- On a single full-measure set of actual original scenes, every compact C¹ kernel and every
original clock restriction obey the literal divergence identity. Both the actual current's
derivative and the local occupation's integrability come from the original first-traffic law. -/
theorem OriginalSeedConditionalMoments.ae_all_divergence_originalClockSetCurrent_spatial
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    ∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (A : Set ℝ) (η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ),
        ContDiff ℝ 1 η → HasCompactSupport η → ∀ z,
        (∑ i : Fin (finrank ℝ S.covector.ker),
          fderiv ℝ (fun z ↦ originalSeedPathClockSetCurrent S w
            (fun x ↦ η (x - z)) A s) z (Pi.single i 1) i) =
          -(∫ p : OriginalClockOccupationPoint S,
            fderiv ℝ η (originalClockOccupationPosition S w p - z)
              (originalClockOccupationVelocity S w p) ∂originalClockOccupationMeasure S A s) := by
  filter_upwards [D.ae_integrable_originalClockOccupation_compact_weight hF hw hbounds Q,
    D.ae_all_hasFDerivAt_originalClockSetCurrent_spatial hF hw hbounds Q] with s hs hd
  intro A η hη hcη z
  have hX := measurable_originalClockOccupationPosition S hF hw
  have hV : AEStronglyMeasurable (originalClockOccupationVelocity S w)
      (originalClockOccupationMeasure S A s) :=
    (measurable_originalClockOccupationVelocity S hF hw).aestronglyMeasurable
  have heq := (hd A η hη hcη z).fderiv.trans
    (hasFDerivAt_compact_kernel_current hη hcη hX
      (σ := originalClockOccupationMeasure S A s) hV (hs A) z).fderiv.symm
  rw [heq]
  exact divergence_compact_kernel_current hη hcη hX hV (hs A) z

end OTSelector.Reconstruction
