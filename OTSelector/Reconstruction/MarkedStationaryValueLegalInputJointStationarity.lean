import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointPoisson

/-!
# Actual stationary joint limits with immutable original input colors

The same spatial reroot moves the true legal plan and every unchanged original
input point while preserving both its physical clock and finite color tag.
The exact original-root cocycle and the actual vanishing Haar boundary give
joint stationarity of every actual weak limit.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
local instance markedStationaryValueLegalInputJointStationarityLocalInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputJointStationarityLocalPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Original clocks and immutable input colors are fixed by physical rerooting. -/
def legalColoredInputPointReroot (q : ℕ) (v : Fin q → ℝ) :
    LegalColoredInputPoint q ≃ₜ LegalColoredInputPoint q :=
  (physicalScenePointReroot v).prodCongr (Homeomorph.refl (Fin 2))

/-- One joint reroot retains the original matching/input correlations. -/
def legalMarkedInputSceneReroot (q : ℕ) (v : Fin q → ℝ)
    (s : LegalMarkedOptimalInputScene q) : LegalMarkedOptimalInputScene q :=
  (physicalSceneReroot v s.1, localFiniteMapHomeomorph (legalColoredInputPointReroot q v) s.2)

theorem continuous_legalMarkedInputSceneReroot (q : ℕ) (v : Fin q → ℝ) :
    Continuous (legalMarkedInputSceneReroot q v) :=
  ((continuous_physicalSceneReroot v).comp continuous_fst).prodMk
    ((continuous_localFiniteMapHomeomorph (legalColoredInputPointReroot q v)).comp continuous_snd)

theorem physicalScenePointReroot_legalMarkedRootedSourcePoint
    (q : ℕ) (L : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ) (z v : Fin q → ℝ) (i : ℕ) :
    physicalScenePointReroot v (legalMarkedRootedSourcePoint q L ω z i) =
      legalMarkedRootedSourcePoint q L ω (z + v) i := by
  change ((legalMarkedCenteredCoordinate q L (legalMarkedPhysicalEdge q L ω i 0).1 - z) - v,
    mSourceMark ω i) = _
  simp only [sub_sub]
  rfl

theorem physicalScenePointReroot_legalMarkedRootedTargetPoint
    (q : ℕ) (L : ℝ) (ω : TwoMarkedCloudSpace q ℝ ℝ) (z v : Fin q → ℝ) (i : ℕ) :
    physicalScenePointReroot v (legalMarkedRootedTargetPoint q L ω z i) =
      legalMarkedRootedTargetPoint q L ω (z + v) i := by
  change ((legalMarkedCenteredCoordinate q L (legalMarkedPhysicalEdge q L ω 0 i).2 - z) - v,
    mTargetMark ω i) = _
  simp only [sub_sub]
  rfl

/-- Rerooting the same full original colored input measure is exactly root
translation; neither color is resampled or reassigned. -/
theorem legalColoredInputReroot_local
    (q : ℕ) {L : ℝ} (hL : 0 < L) (ω : TwoMarkedCloudSpace q ℝ ℝ) (z v : Fin q → ℝ) :
    localFiniteMapHomeomorph (legalColoredInputPointReroot q v)
      (legalMarkedRootedColoredInputLocal q L (ω, z)) =
        legalMarkedRootedColoredInputLocal q L (ω, z + v) := by
  apply LocalFiniteMeasure.testIntegral_injective
  funext F
  change (∫ x, F x ∂(legalMarkedRootedColoredInputMeasure q L (ω, z)).map
    (legalColoredInputPointReroot q v)) =
    ∫ x, F x ∂legalMarkedRootedColoredInputMeasure q L (ω, z + v)
  rw [integral_map (f := fun x ↦ F x)
    (legalColoredInputPointReroot q v).continuous.measurable.aemeasurable
    (show AEStronglyMeasurable (fun x ↦ F x) _ from F.continuous.aestronglyMeasurable),
    integral_legalMarkedRootedColoredInputMeasure q hL _ (ω, z),
    integral_legalMarkedRootedColoredInputMeasure q hL _ (ω, z + v)]
  apply congrArg₂ (fun a b : ℝ ↦ a + b)
  · apply Finset.sum_congr rfl
    intro i hi
    change F (physicalScenePointReroot v (legalMarkedRootedSourcePoint q L ω z i), 0) = _
    rw [physicalScenePointReroot_legalMarkedRootedSourcePoint]
  · apply Finset.sum_congr rfl
    intro i hi
    change F (physicalScenePointReroot v (legalMarkedRootedTargetPoint q L ω z i), 1) = _
    rw [physicalScenePointReroot_legalMarkedRootedTargetPoint]

/-- The true finite legal optimum and both original input colors satisfy one
exact root-change cocycle on their actual joint observation. -/
theorem legalMarkedInputSceneReroot_observation
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (ω : TwoMarkedCloudSpace q ℝ ℝ) (z v : Fin q → ℝ) :
    legalMarkedInputSceneReroot q v (legalMarkedOptimalInputObservation q hL kin g t (ω, z)) =
      legalMarkedOptimalInputObservation q hL kin g t (ω, z + v) := by
  have : ∀ w : TwoMarkedCloudSpace q ℝ ℝ,
      IsFiniteMeasure (legalMarkedNormalizedOptimalPlan q L kin g t w) :=
    fun w ↦ isFiniteMeasure_legalMarkedNormalizedOptimalPlan q hL kin g t w
  apply Prod.ext
  · exact physicalSceneReroot_localScene v (legalMarkedNormalizedOptimalPlan q L kin g t)
      (legalMarkedNormalizedOptimalPlan q L kin g t)
      (legalMarkedCenteredCoordinate q L) (measurable_legalMarkedCenteredCoordinate q L)
      Prod.snd measurable_snd (L ^ q) ω z
  · exact legalColoredInputReroot_local q hL ω z v

/-- Actual Haar-root joint weak limits are stationary, including their original
colored inputs. No stationarity of the finite clouds or optimizer is assumed. -/
theorem measurePreserving_legalMarkedInputSceneReroot_of_tendsto
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q)) (v : Fin q → ℝ) :
    MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q)) (Q : Measure (LegalMarkedOptimalInputScene q)) := by
  have hlaw k : (legalMarkedOptimalInputSceneLaw q α β kin hk g hg t (L k) (hL k) :
      Measure (LegalMarkedOptimalInputScene q)) =
      haarCubeAverageLaw (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L k ^ q)))
        (legalMarkedOptimalInputObservation q (hL k) kin g t) (L k / 2) := by
    simp only [legalMarkedOptimalInputSceneLaw, haarCubeAverageLaw, legalMarkedHaarRootLaw,
      haarCubeRootLaw, Fintype.card_fin, show 2 * (L k / 2) = L k by ring]
    rfl
  exact measurePreserving_of_haarCubeAverageLaw_tendsto
    (fun k ↦ twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L k ^ q)))
    (fun k ↦ legalMarkedOptimalInputObservation q (hL k) kin g t)
    (fun k ↦ measurable_legalMarkedOptimalInputObservation q (hL k) hk hg t)
    (fun k ↦ L k / 2) (fun k ↦ by linarith [hL k])
    (hlarge.atTop_div_const (by norm_num)) _ hlaw hweak
    (continuous_legalMarkedInputSceneReroot q v) v
    (fun k ω z ↦ legalMarkedInputSceneReroot_observation q (hL k) kin g t ω z v)

/-- The actual joint weak input limit has its prescribed Poisson readout in
every specified physical cube containing the test, not merely in a chosen cube. -/
theorem integral_legalMarkedInputSceneLaplace_eq_originalPoisson_window_of_tendsto
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q))
    {S : ℝ} (hS : 0 < S) (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x)
    (hwindow : ∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
      x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
      ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
        ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β := by
  have hh : Measurable (fun x : LegalMarkedPhysicalPoint q ↦ F (x, 0)) :=
    F.continuous.measurable.comp (measurable_id.prodMk measurable_const)
  have ht : Measurable (fun x : LegalMarkedPhysicalPoint q ↦ F (x, 1)) :=
    F.continuous.measurable.comp (measurable_id.prodMk measurable_const)
  have hvol : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  have hinput := (tendsto_integral_legalMarkedRootedInputLaplace q hS.le measurableSet_Icc
    (Subset.refl _) hvol α β hh ht (fun x ↦ hF (x, 0)) (fun x ↦ hF (x, 1))
    (fun x ↦ hwindow x 0) (fun x ↦ hwindow x 1)).comp hlarge
  have hactual := hinput.congr' (.of_forall (fun k ↦
    (integral_legalMarkedOptimalInputSceneLaw_laplace q α β kin hk g hg t (hL k) F hF).symm))
  exact tendsto_nhds_unique
    ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak)
      (legalMarkedInputSceneLaplace q F hF)) hactual

/-- The same original legal finite optima produce an actual jointly stationary
weak scene with its unchanged colored Poisson inputs. The prescribed input
readout is valid in every specified cube containing its compact test. Matching
marginal fullness is a subsequent nonproper-projection assertion. -/
theorem exists_stationary_originalPoisson_legalMarkedOptimalInputSceneLaw
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop) :
    ∃ Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
        (L (φ k)) (hL (φ k))) atTop (𝓝 Q) ∧
      (∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
        (Q : Measure (LegalMarkedOptimalInputScene q)) (Q : Measure (LegalMarkedOptimalInputScene q))) ∧
      (∀ (S : ℝ), 0 < S → ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
        (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
          x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) →
        (∫ s, legalMarkedInputSceneLaplace q F hF s ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
          ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
            ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β) := by
  obtain ⟨Q, φ, hφ, hw⟩ := exists_tendsto_subseq_legalMarkedOptimalInputSceneLaw q L hL α β kin hk g hg t
  have hlargeφ : Tendsto (fun k ↦ L (φ k)) atTop atTop := hlarge.comp hφ.tendsto_atTop
  refine ⟨Q, φ, hφ, hw, ?_, ?_⟩
  · exact fun v ↦ measurePreserving_legalMarkedInputSceneReroot_of_tendsto q α β kin hk g hg t
      (fun k ↦ L (φ k)) (fun k ↦ hL (φ k)) hlargeφ hw v
  · intro S hS F hF hwindow
    exact integral_legalMarkedInputSceneLaplace_eq_originalPoisson_window_of_tendsto
      q α β kin hk g hg t (fun k ↦ L (φ k)) (fun k ↦ hL (φ k)) hlargeφ hw hS F hF hwindow

end OTSelector.Reconstruction
