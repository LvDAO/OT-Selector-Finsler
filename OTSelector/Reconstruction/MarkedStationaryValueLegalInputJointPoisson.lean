import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointTightness

/-!
# Prescribed original Poisson input readouts of actual joint weak limits

The immutable-color input factor has proper compact tests. Their bounded
Laplace functions are continuous on the joint vague carrier, so the actual
original rooted Poisson window laws identify every joint weak limit directly.
Neither selected-point independence nor clock support separation is assumed.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
local instance markedStationaryValueLegalInputJointPoissonLocalInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputJointPoissonLocalPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- A continuous bounded Laplace readout of the same original colored inputs. -/
def legalMarkedInputSceneLaplace (q : ℕ) (F : C_c(LegalColoredInputPoint q, ℝ))
    (hF : ∀ x, 0 ≤ F x) : LegalMarkedOptimalInputScene q →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun s : LegalMarkedOptimalInputScene q ↦ Real.exp (-LocalFiniteMeasure.testIntegral s.2 F),
      Real.continuous_exp.comp
        ((LocalFiniteMeasure.continuous_testIntegral F).comp continuous_snd).neg⟩ 2 (by
      intro x y
      have hb (s : LegalMarkedOptimalInputScene q) :
          |Real.exp (-LocalFiniteMeasure.testIntegral s.2 F)| ≤ 1 := by
        rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        exact neg_nonpos.mpr (integral_nonneg hF)
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans ((add_le_add (hb x) (hb y)).trans_eq (by norm_num)))

/-- The input factor is the original complete empirical input test in the same
physical coordinates and the same original root, with both colors explicit. -/
theorem integral_legalMarkedOptimalInputSceneLaw_laplace
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    {L : ℝ} (hL : 0 < L) (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s
      ∂(legalMarkedOptimalInputSceneLaw q α β kin hk g hg t L hL :
        Measure (LegalMarkedOptimalInputScene q))) =
      ∫ p, legalMarkedRootedInputLaplace q L (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) p
        ∂(twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
          (legalMarkedHaarRootLaw q L) := by
  change (∫ s, legalMarkedInputSceneLaplace q F hF s
    ∂(((twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
      (legalMarkedHaarRootLaw q L)).map (legalMarkedOptimalInputObservation q hL kin g t))) = _
  rw [integral_map (measurable_legalMarkedOptimalInputObservation q hL hk hg t).aemeasurable
    (legalMarkedInputSceneLaplace q F hF).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall (fun p ↦ by
    change Real.exp (-(∫ x, F x ∂legalMarkedRootedColoredInputMeasure q L p)) = _
    rw [integral_legalMarkedRootedColoredInputMeasure q hL F p]
    rfl)

/-- Every actual joint weak limit has the original independent two-color
physical Poisson Laplace functional on all nonnegative compact input tests.
The containing physical window is produced from the test itself. -/
theorem integral_legalMarkedInputSceneLaplace_eq_originalPoisson_of_tendsto
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k) (hlarge : Tendsto L atTop atTop)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q))
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    ∃ S > 0, (∫ s, legalMarkedInputSceneLaplace q F hF s ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
      ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
        ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β := by
  obtain ⟨S, hS, hbound⟩ := (F.hasCompactSupport.image
    (continuous_fst.comp continuous_fst)).isBounded.exists_pos_norm_lt
  have hzero (c : Fin 2) (p : LegalMarkedPhysicalPoint q)
      (hp : p.1 ∉ haarRootCube (Fin q) S) : F (p, c) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hsupp
    apply hp
    have hn : ‖p.1‖ < S := hbound _ ⟨(p, c), hsupp, rfl⟩
    have hi (i : Fin q) : |p.1 i| ≤ S := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm p.1 i).trans hn.le
    exact ⟨fun i ↦ (abs_le.mp (hi i)).1, fun i ↦ (abs_le.mp (hi i)).2⟩
  have hh : Measurable (fun x : LegalMarkedPhysicalPoint q ↦ F (x, 0)) :=
    F.continuous.measurable.comp (measurable_id.prodMk measurable_const)
  have ht : Measurable (fun x : LegalMarkedPhysicalPoint q ↦ F (x, 1)) :=
    F.continuous.measurable.comp (measurable_id.prodMk measurable_const)
  have hvol : volume (haarRootCube (Fin q) S) ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hS.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity : 0 < 2 * S) q)).ne'
  have hinput := (tendsto_integral_legalMarkedRootedInputLaplace q hS.le measurableSet_Icc
    (Subset.refl _) hvol α β hh ht (fun x ↦ hF (x, 0)) (fun x ↦ hF (x, 1))
    (hzero 0) (hzero 1)).comp hlarge
  have hactual : Tendsto (fun k ↦ ∫ s, legalMarkedInputSceneLaplace q F hF s
      ∂(legalMarkedOptimalInputSceneLaw q α β kin hk g hg t (L k) (hL k) :
        Measure (LegalMarkedOptimalInputScene q))) atTop
      (𝓝 (∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
        ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β)) := by
    apply hinput.congr'
    exact .of_forall (fun k ↦ (integral_legalMarkedOptimalInputSceneLaw_laplace q α β kin hk
      g hg t (hL k) F hF).symm)
  have hw := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak)
    (legalMarkedInputSceneLaplace q F hF)
  exact ⟨S, hS, tendsto_nhds_unique hw hactual⟩

end OTSelector.Reconstruction
