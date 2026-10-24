import OTSelector.Reconstruction.OriginalIIDActualLocalLaplace
import OTSelector.Probability.OriginalIIDConfigurationLaplace

/-!
# Actual-core Laplace convergence for original masked configurations

The actual original iid compact-test limit is transferred through the proved
configuration encoding, retaining the same full original laws and deterministic
core mask at one common full-measure set of coordinate roots.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Metric Module Manifold OTSelector.Geometry
open scoped Topology ENNReal NNReal ContDiff BigOperators CompactlySupported

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

private theorem original_compactTest_spatial_support {V : Type*}
    [NormedAddCommGroup V] (H : C_c(V × ℝ, ℝ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ p, p.1 ∉ closedBall 0 B → H p = 0 := by
  obtain ⟨B, hB⟩ := (H.hasCompactSupport.image continuous_fst).isBounded.subset_ball (0 : V)
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro p hp
  by_contra hH
  apply hp
  have hpB : p.1 ∈ ball (0 : V) B := hB ⟨p, subset_tsupport H hH, rfl⟩
  exact (closedBall_subset_closedBall (le_max_left B 1)) (ball_subset_closedBall hpB)

section ActualCore

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- At one common full-measure set of actual coordinate roots, every pair of
nonnegative compact configuration tests has the original two-color Laplace
limit. The exact configuration pushforward law keeps both original iid laws,
all retained endpoint multiplicities and the deterministic original core mask.
No scaled-defect or target-limit callback is assumed. -/
theorem PopulationLocalPressureCore.original_ae_twoColor_configuration_laplace_tendsto
    [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hlarge : Tendsto s atTop atTop)
    (hnormalization : ∀ n,
      s n ^ finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker =
        ((n + 1 : ℕ) : ℝ)) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let K := e '' (R '' C.roots)
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let mask := a ⁻¹' C.roots
    ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      ∀ (H G : C_c((Fin q → ℝ) × ℝ, ℝ)),
        (∀ p, 0 ≤ H p) → (∀ p, 0 ≤ G p) →
        let obs := fun n x ↦ (s n • (e (R (a x)) - c), u x)
        let θ := originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c)
        Tendsto (fun n ↦
          ∫ cfg, Real.exp (-(OTSelector.PointProcess.LocalConfiguration.testIntegral cfg.1 H +
              OTSelector.PointProcess.LocalConfiguration.testIntegral cfg.2 G))
            ∂OTSelector.Probability.originalIidMaskedConfigurationPairLaw η₀ η₁
              (n + 1) (n + 1) (0 : (Fin q → ℝ) × ℝ) (0 : (Fin q → ℝ) × ℝ)
              mask mask (obs n) (obs n)) atTop
          (𝓝 (Real.exp (-(θ *
            ((∫ p, 1 - Real.exp (-H p)
                ∂((volume : Measure (Fin q → ℝ)).prod (condDistrib u a η₀ (ref c)))) +
              (∫ p, 1 - Real.exp (-G p)
                ∂((volume : Measure (Fin q → ℝ)).prod (condDistrib u a η₁ (ref c))))))))) := by
  dsimp only
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let mask := a ⁻¹' C.roots
  have hmask : MeasurableSet mask := C.roots_compact.measurableSet.preimage ha
  have hR : Measurable R := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  filter_upwards [D.original_ae_twoColor_iid_laplace_tendsto hF hcomplete hu ha hinj i
    s hs hlarge hnormalization] with c hc
  intro H G hH hG
  let obs := fun n x ↦ (s n • (e (R (a x)) - c), u x)
  have hobs n : Measurable (obs n) := by
    change Measurable (fun x ↦ (s n • (e (R (a x)) - c), u x))
    exact (((e.continuous.measurable.comp (hR.comp ha)).sub_const c).const_smul (s n)).prodMk
      hu.continuous.measurable
  have hraw := hc H G H.continuous.measurable G.continuous.measurable hH hG
    (original_compactTest_spatial_support H) (original_compactTest_spatial_support G)
  apply hraw.congr'
  filter_upwards [] with n
  exact (OTSelector.Probability.integral_originalIidMaskedConfigurationPairLaw_laplace_eq_sum
    η₀ η₁ (n + 1) (n + 1) (0 : (Fin _ → ℝ) × ℝ) (0 : (Fin _ → ℝ) × ℝ)
      hmask hmask (hobs n) (hobs n) H G).symm

end ActualCore
end OTSelector.Reconstruction

