import OTSelector.Reconstruction.OriginalIIDTiltedEnergyBound

/-!
# One actual iid energy budget on a bounded tilt interval

The zero-tilt original supported upper and the exact finite optimizer comparison
provide one eventual budget and one sample-size threshold for all bounded tilts.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped ENNReal BigOperators Topology NNReal BoundedContinuousFunction Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

section Generic
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ} [NeZero n]

/-- The nonnegative base energy of an actual tilted optimizer is paid by the
exact zero-tilt optimum plus two bounded-probe corrections. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_tilt_base_le_zero
    (base probe : X → Y → ℝ)
    (hb : Measurable (Function.uncurry base))
    (hp : Measurable (Function.uncurry probe))
    (hb0 : ∀ x y, 0 ≤ base x y)
    (G t : ℝ) (hG : ∀ x y, |probe x y| ≤ G)
    (ξ : (Fin n → X) × (Fin n → Y)) :
    (∫⁻ p, ENNReal.ofReal (base p.1 p.2)
      ∂originalIIDOptimalPhysicalPlan (fun x y ↦ base x y + t * probe x y) 1 ξ) ≤
      ENNReal.ofReal (perturbedAssignmentValue
        (fun i j ↦ base (ξ.1 i) (ξ.2 j)) 0 0 / n + 2 * |t| * G) := by
  calc
    _ = ENNReal.ofReal (∫ p, base p.1 p.2
        ∂originalIIDOptimalPhysicalPlan (fun x y ↦ base x y + t * probe x y) 1 ξ) :=
      (ofReal_integral_eq_lintegral_ofReal
        (integrable_originalIIDOptimalPhysicalPlan
          (fun x y ↦ base x y + t * probe x y) 1 ξ hb.stronglyMeasurable)
        (Eventually.of_forall (fun p ↦ hb0 p.1 p.2))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (integral_originalIIDOptimalPhysicalPlan_tilt_base_le_zero base probe hb hp G t hG ξ)
end Generic

section Finsler
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

omit [MeasurableSpace E] [BorelSpace E] in
/-- At every sample size one zero-tilt pressure mean bounds the true expected
scaled-slack energies of all actual tilted optimizers on a bounded interval. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_finsler_supported_uniform_slack_le_zero
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (u : M → ℝ) (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (f : (K × K) →ᵇ ℝ) (T : ℝ) (hT : 0 ≤ T) (n : ℕ) (t : ℝ) (ht : |t| ≤ T) :
    (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (finslerMeanScale E n *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
      ∂originalIIDOptimalPhysicalPlan
        (fun x y ↦ finslerMeanScale E n *
          ((F.lengthEDist x y).toReal - u y + u x) +
          t * finslerCarrierProbe μ ν K hK.measurableSet hμ hν f x y) 1 ξ
      ∂canonicalLaw μ ν n) ≤
      ENNReal.ofReal ((∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        ξ.1 ξ.2 u (finslerMeanScale E n) f 0 ∂canonicalLaw μ ν n) + 2 * T * ‖f‖) := by
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace inferInstance
  let k := finslerMeanScale E n
  have hk : 0 ≤ k := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let base := fun x y : M ↦ k * (dist x y - u y + u x)
  let probe := finslerCarrierProbe μ ν K hK.measurableSet hμ hν f
  have hb : Measurable (Function.uncurry base) :=
    (((measurable_fst.dist measurable_snd).sub
      (hu.continuous.measurable.comp measurable_snd)).add
      (hu.continuous.measurable.comp measurable_fst)).const_mul k
  have hp : Measurable (Function.uncurry probe) := f.continuous.measurable.comp
    (((measurable_supportProjection μ K hK.measurableSet hμ).comp measurable_fst).prodMk
      ((measurable_supportProjection ν K hK.measurableSet hν).comp measurable_snd))
  have hb0 (x y : M) : 0 ≤ base x y := by
    have h := hu.le_add_mul y x
    simp only [NNReal.coe_one, one_mul, dist_comm y x] at h
    exact mul_nonneg hk (by linarith)
  have hbound (x y : M) : |probe x y| ≤ ‖f‖ := by
    exact (Real.norm_eq_abs _).symm ▸ f.norm_coe_le_norm _
  have hcorr : 2 * |t| * ‖f‖ ≤ 2 * T * ‖f‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num)) (norm_nonneg _)
  have hpoint (ξ : canonicalOmega M n) :
      (∫⁻ p, ENNReal.ofReal (base p.1 p.2)
        ∂originalIIDOptimalPhysicalPlan (fun x y ↦ base x y + t * probe x y) 1 ξ) ≤
        ENNReal.ofReal (Pressure.supportedDistancePressure μ ν K hK.measurableSet hμ hν
          ξ.1 ξ.2 u k f 0 + 2 * T * ‖f‖) := by
    have hcmp : perturbedAssignmentValue (fun i j ↦ base (ξ.1 i) (ξ.2 j)) 0 0 /
        (n + 1 : ℕ) + 2 * |t| * ‖f‖ ≤
        perturbedAssignmentValue (fun i j ↦ base (ξ.1 i) (ξ.2 j)) 0 0 /
          (n + 1 : ℕ) + 2 * T * ‖f‖ := by linarith
    have h := (lintegral_originalIIDOptimalPhysicalPlan_tilt_base_le_zero
      base probe hb hp hb0 ‖f‖ t hbound ξ).trans (ENNReal.ofReal_le_ofReal hcmp)
    convert h using 1
    · rfl
    · simp only [Pressure.supportedDistancePressure, perturbedAssignmentValue,
        perturbedEdgeCost_zero]
      congr 3
  have hx : ∀ᵐ ξ ∂canonicalLaw μ ν n, ∀ i, canonicalX n i ξ ∈ K := by
    apply ae_all_iff.mpr
    intro i
    apply ae_of_ae_map (measurable_canonicalX n i).aemeasurable
    simpa only [canonicalLaw_map_canonicalX] using hμ
  have hy : ∀ᵐ ξ ∂canonicalLaw μ ν n, ∀ j, canonicalY n j ξ ∈ K := by
    apply ae_all_iff.mpr
    intro j
    apply ae_of_ae_map (measurable_canonicalY n j).aemeasurable
    simpa only [canonicalLaw_map_canonicalY] using hν
  have hint := Pressure.integrable_supportedDistancePressure
    (canonicalLaw μ ν n) μ ν K hK.measurableSet hμ hν
    (canonicalX n) (canonicalY n) (measurable_canonicalX n) (measurable_canonicalY n)
    u hu hu.continuous k f 0 (Nat.succ_pos n) hk hK hx hy
  have hnonneg (ξ : canonicalOmega M n) : 0 ≤
      Pressure.supportedDistancePressure μ ν K hK.measurableSet hμ hν
        ξ.1 ξ.2 u k f 0 + 2 * T * ‖f‖ := by
    have h := Pressure.supportedDistancePressure_ge_neg_abs_mul μ ν K hK.measurableSet
      hμ hν (Nat.succ_pos n) ξ.1 ξ.2 u hu k hk f 0
    simp only [abs_zero, zero_mul, neg_zero] at h
    exact add_nonneg h (mul_nonneg (mul_nonneg (by norm_num) hT) (norm_nonneg _))
  calc
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (Pressure.supportedDistancePressure μ ν K hK.measurableSet
        hμ hν ξ.1 ξ.2 u k f 0 + 2 * T * ‖f‖) ∂canonicalLaw μ ν n :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal (∫ ξ, (Pressure.supportedDistancePressure μ ν K hK.measurableSet
        hμ hν ξ.1 ξ.2 u k f 0 + 2 * T * ‖f‖) ∂canonicalLaw μ ν n) :=
      (ofReal_integral_eq_lintegral_ofReal (hint.add (integrable_const _))
        (Eventually.of_forall hnonneg)).symm
    _ = _ := by
      congr 1
      have h := integral_add hint (integrable_const (2 * T * ‖f‖))
      simpa [integral_const, canonicalX, canonicalY, finslerSupportedPressure] using h
variable {u : M → ℝ} {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : ProbabilityMeasure M} {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ}
  {b : (ℚ → M) × ℝ → M} {r : ℝ} {δ loss : ℝ≥0∞}

omit [BorelSpace E] in
/-- The original explicit upper packet at zero tilt supplies one finite eventual
energy budget simultaneously for every actual tilted optimizer with `|t| ≤ T`. -/
theorem PopulationLocalPressureCore.exists_eventually_originalIID_supported_uniform_tilt_energy_bound
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ ((μ : Measure M).map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (f : (K × K) →ᵇ ℝ) (g : (M × M) →ᵇ ℝ) (ε probeError : ℝ)
    (hdata : D.originalSupportedWeightUnitDensityPressureData γ originalGap Q U
      retentionError splitError K hK hμ hν f g ε probeError
      (fun n ↦ canonicalLaw μ ν n) (fun n ↦ canonicalX n) (fun n ↦ canonicalY n))
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ t : ℝ, |t| ≤ T →
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (finslerMeanScale E n *
          ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂originalIIDOptimalPhysicalPlan
          (fun x y ↦ finslerMeanScale E n *
            ((F.lengthEDist x y).toReal - u y + u x) +
            t * finslerCarrierProbe μ ν K hK.measurableSet hμ hν f x y) 1 ξ
        ∂canonicalLaw μ ν n) ≤ ENNReal.ofReal C := by
  classical
  rcases hdata with ⟨N,refs,cells,hcells,hsub,hP₀,hmass,A,hA,cHaar,hcHaar,hmap,
    unitPressure,hunit,hupper⟩
  obtain ⟨B,hB⟩ : ∃ B : ℝ, ∀ᶠ n in atTop,
      (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        ξ.1 ξ.2 u (finslerMeanScale E n) f 0 ∂canonicalLaw μ ν n) ≤ B := by
    exact ⟨_, hupper 0 1 zero_lt_one⟩
  refine ⟨max 0 (B + 2 * T * ‖f‖), le_max_left _ _, ?_⟩
  filter_upwards [hB] with n hn
  intro t ht
  have hcmp : (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
      ξ.1 ξ.2 u (finslerMeanScale E n) f 0 ∂canonicalLaw μ ν n) + 2 * T * ‖f‖ ≤
      B + 2 * T * ‖f‖ := by linarith
  exact (lintegral_originalIIDOptimalPhysicalPlan_finsler_supported_uniform_slack_le_zero
    hcomplete μ ν K hK hμ hν u hu f T hT n t ht).trans
      (ENNReal.ofReal_le_ofReal (hcmp.trans (le_max_right _ _)))
end Finsler
end OTSelector.Reconstruction
