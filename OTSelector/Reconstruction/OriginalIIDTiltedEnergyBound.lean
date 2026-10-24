import OTSelector.Probability.CanonicalIidSampling
import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalPlan
import OTSelector.Reconstruction.FinslerOriginalPhysicalUnitDensitySupportedUpper

/-!
# Energy control of the actual original iid tilted optimizer

The same finite optimizer and canonical growing iid experiment are retained.
A bounded probe transfers the explicit physical pressure upper packet to a
finite expected scaled-slack budget, without removing its geometric errors.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped ENNReal BigOperators Topology NNReal BoundedContinuousFunction Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section Generic
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ} [NeZero n]

/-- The actual optimal tilted plan pays base energy bounded by its attained value
plus one bounded-probe correction. -/
theorem integral_originalIIDOptimalPhysicalPlan_tilt_base_le
    (base probe : X → Y → ℝ)
    (hb : Measurable (Function.uncurry base))
    (hp : Measurable (Function.uncurry probe))
    (G t : ℝ) (hG : ∀ x y, |probe x y| ≤ G)
    (ξ : (Fin n → X) × (Fin n → Y)) :
    (∫ p, base p.1 p.2
      ∂originalIIDOptimalPhysicalPlan (fun x y ↦ base x y + t * probe x y) 1 ξ) ≤
      perturbedAssignmentValue (fun i j ↦ base (ξ.1 i) (ξ.2 j) +
        t * probe (ξ.1 i) (ξ.2 j)) 0 0 / n + |t| * G := by
  let cost := fun x y ↦ base x y + t * probe x y
  let Γ := originalIIDOptimalPhysicalPlan cost 1 ξ
  have hiB : Integrable (fun p : X × Y ↦ base p.1 p.2) Γ :=
    integrable_originalIIDOptimalPhysicalPlan cost 1 ξ hb.stronglyMeasurable
  have hiP : Integrable (fun p : X × Y ↦ probe p.1 p.2) Γ :=
    integrable_originalIIDOptimalPhysicalPlan cost 1 ξ hp.stronglyMeasurable
  have heq := integral_originalIIDOptimalPhysicalPlan_cost cost (hb.add (hp.const_mul t)) 1 ξ
  simp only [one_mul] at heq
  have hsplit : (∫ p, cost p.1 p.2 ∂Γ) =
      (∫ p, base p.1 p.2 ∂Γ) + t * ∫ p, probe p.1 p.2 ∂Γ := by
    change (∫ p, (base p.1 p.2 + t * probe p.1 p.2) ∂Γ) = _
    rw [integral_add hiB (hiP.const_mul t), integral_const_mul]
  have hprobe : |∫ p : X × Y, probe p.1 p.2 ∂Γ| ≤ G := by
    have := norm_integral_le_of_norm_le_const
      (μ := Γ) (f := fun p : X × Y ↦ probe p.1 p.2)
      (Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using hG p.1 p.2))
    simpa [Real.norm_eq_abs, measureReal_def] using this
  have hcorr : -(t * ∫ p : X × Y, probe p.1 p.2 ∂Γ) ≤ |t| * G := by
    calc
      _ ≤ |t * ∫ p : X × Y, probe p.1 p.2 ∂Γ| := neg_le_abs _
      _ = |t| * |∫ p : X × Y, probe p.1 p.2 ∂Γ| := abs_mul _ _
      _ ≤ |t| * G := mul_le_mul_of_nonneg_left hprobe (abs_nonneg _)
  change (∫ p, base p.1 p.2 ∂Γ) ≤ _
  change (∫ p, cost p.1 p.2 ∂Γ) = _ at heq
  rw [hsplit] at heq
  linarith

/-- The nonnegative base-energy integral retains the actual tilted optimizer,
including every original observation and the exact first-minimum tie rule. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_tilt_base_le
    (base probe : X → Y → ℝ)
    (hb : Measurable (Function.uncurry base))
    (hp : Measurable (Function.uncurry probe))
    (hb0 : ∀ x y, 0 ≤ base x y)
    (G t : ℝ) (hG : ∀ x y, |probe x y| ≤ G)
    (ξ : (Fin n → X) × (Fin n → Y)) :
    (∫⁻ p, ENNReal.ofReal (base p.1 p.2)
      ∂originalIIDOptimalPhysicalPlan (fun x y ↦ base x y + t * probe x y) 1 ξ) ≤
      ENNReal.ofReal (perturbedAssignmentValue
        (fun i j ↦ base (ξ.1 i) (ξ.2 j) + t * probe (ξ.1 i) (ξ.2 j)) 0 0 / n + |t| * G) := by
  calc
    _ = ENNReal.ofReal (∫ p, base p.1 p.2
        ∂originalIIDOptimalPhysicalPlan (fun x y ↦ base x y + t * probe x y) 1 ξ) :=
      (ofReal_integral_eq_lintegral_ofReal
        (integrable_originalIIDOptimalPhysicalPlan
          (fun x y ↦ base x y + t * probe x y) 1 ξ hb.stronglyMeasurable)
        (Eventually.of_forall (fun p ↦ hb0 p.1 p.2))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (integral_originalIIDOptimalPhysicalPlan_tilt_base_le base probe hb hp G t hG ξ)

/-- Comparing the actual tilted optimizer to the exact zero-tilt competitor costs
at most two bounded-probe corrections in its base energy. -/
theorem integral_originalIIDOptimalPhysicalPlan_tilt_base_le_zero
    (base probe : X → Y → ℝ)
    (hb : Measurable (Function.uncurry base))
    (hp : Measurable (Function.uncurry probe))
    (G t : ℝ) (hG : ∀ x y, |probe x y| ≤ G)
    (ξ : (Fin n → X) × (Fin n → Y)) :
    (∫ p, base p.1 p.2
      ∂originalIIDOptimalPhysicalPlan (fun x y ↦ base x y + t * probe x y) 1 ξ) ≤
      perturbedAssignmentValue (fun i j ↦ base (ξ.1 i) (ξ.2 j)) 0 0 / n +
        2 * |t| * G := by
  let cb : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ base (ξ.1 i) (ξ.2 j)
  let ct : Matrix (Fin n) (Fin n) ℝ :=
    fun i j ↦ base (ξ.1 i) (ξ.2 j) + t * probe (ξ.1 i) (ξ.2 j)
  have hst := perturbedAssignmentValue_div_abs_sub_le_of_edge_bound
    (Nat.pos_of_ne_zero (NeZero.ne n)) ct 0 cb 0 0 0 (|t| * G) (fun i j ↦ by
      have hterm : |base (ξ.1 i) (ξ.2 j) + t * probe (ξ.1 i) (ξ.2 j) -
          base (ξ.1 i) (ξ.2 j)| ≤ |t| * G := by
        calc
          _ = |t| * |probe (ξ.1 i) (ξ.2 j)| := by
            rw [← abs_mul]
            congr 1
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hG _ _) (abs_nonneg _)
      simpa [perturbedEdgeCost, ct, cb] using hterm)
  have hle := (le_abs_self _).trans hst
  have hbnd := integral_originalIIDOptimalPhysicalPlan_tilt_base_le base probe hb hp G t hG ξ
  change _ ≤ perturbedAssignmentValue cb 0 0 / n + 2 * |t| * G
  change _ ≤ perturbedAssignmentValue ct 0 0 / n + |t| * G at hbnd
  linarith

end Generic
section Metric
variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- Exact finite-sample energy control for the original supported tilted optimizer. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_supported_slack_le
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (u : M → ℝ) (hu : LipschitzWith 1 u) (k : ℝ) (hk : 0 ≤ k)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) {n : ℕ} [NeZero n]
    (ξ : (Fin n → M) × (Fin n → M)) :
    (∫⁻ p, ENNReal.ofReal (k * (dist p.1 p.2 - u p.2 + u p.1))
      ∂originalIIDOptimalPhysicalPlan
        (fun x y ↦ k * (dist x y - u y + u x) +
          t * finslerCarrierProbe μ ν K hK hμ hν f x y) 1 ξ) ≤
      ENNReal.ofReal (Pressure.supportedDistancePressure μ ν K hK hμ hν
        ξ.1 ξ.2 u k f t + |t| * ‖f‖) := by
  have hb : Measurable (Function.uncurry (fun x y ↦ k * (dist x y - u y + u x))) :=
    (((measurable_fst.dist measurable_snd).sub
      (hu.continuous.measurable.comp measurable_snd)).add
      (hu.continuous.measurable.comp measurable_fst)).const_mul k
  have hp : Measurable (Function.uncurry (finslerCarrierProbe μ ν K hK hμ hν f)) :=
    f.continuous.measurable.comp
      (((measurable_supportProjection μ K hK hμ).comp measurable_fst).prodMk
        ((measurable_supportProjection ν K hK hν).comp measurable_snd))
  have hb0 (x y : M) : 0 ≤ k * (dist x y - u y + u x) := by
    have h := hu.le_add_mul y x
    simp only [NNReal.coe_one, one_mul, dist_comm y x] at h
    exact mul_nonneg hk (by linarith)
  have hbound (x y : M) : |finslerCarrierProbe μ ν K hK hμ hν f x y| ≤ ‖f‖ := by
    exact (Real.norm_eq_abs _).symm ▸ f.norm_coe_le_norm _
  have h := lintegral_originalIIDOptimalPhysicalPlan_tilt_base_le
    (fun x y ↦ k * (dist x y - u y + u x))
    (finslerCarrierProbe μ ν K hK hμ hν f) hb hp hb0 ‖f‖ t hbound ξ
  convert h using 1
  simp only [Pressure.supportedDistancePressure, perturbedAssignmentValue,
    perturbedEdgeCost_zero]
  congr 3

/-- The actual growing iid tilted plan has expected nonnegative slack energy
bounded by the original supported pressure mean plus the exact probe correction. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_supported_expected_slack_le
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (u : M → ℝ) (hu : LipschitzWith 1 u) (k : ℝ) (hk : 0 ≤ k)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) :
    (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (k * (dist p.1 p.2 - u p.2 + u p.1))
      ∂originalIIDOptimalPhysicalPlan
        (fun x y ↦ k * (dist x y - u y + u x) +
          t * finslerCarrierProbe μ ν K hK.measurableSet hμ hν f x y) 1 ξ
      ∂canonicalLaw μ ν n) ≤
      ENNReal.ofReal ((∫ ξ, Pressure.supportedDistancePressure μ ν K hK.measurableSet hμ hν
        ξ.1 ξ.2 u k f t ∂canonicalLaw μ ν n) + |t| * ‖f‖) := by
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
    u hu hu.continuous k f t (Nat.succ_pos n) hk hK hx hy
  have hnonneg (ξ : canonicalOmega M n) : 0 ≤
      Pressure.supportedDistancePressure μ ν K hK.measurableSet hμ hν
        ξ.1 ξ.2 u k f t + |t| * ‖f‖ := by
    have h := Pressure.supportedDistancePressure_ge_neg_abs_mul μ ν K
      hK.measurableSet hμ hν (Nat.succ_pos n) ξ.1 ξ.2 u hu k hk f t
    change -( |t| * ‖f‖) ≤ _ at h
    linarith
  calc
    _ ≤ ∫⁻ ξ, ENNReal.ofReal
        (Pressure.supportedDistancePressure μ ν K hK.measurableSet hμ hν
          ξ.1 ξ.2 u k f t + |t| * ‖f‖) ∂canonicalLaw μ ν n :=
      lintegral_mono fun ξ ↦ lintegral_originalIIDOptimalPhysicalPlan_supported_slack_le
        μ ν K hK.measurableSet hμ hν u hu k hk f t ξ
    _ = ENNReal.ofReal (∫ ξ, (Pressure.supportedDistancePressure μ ν K
        hK.measurableSet hμ hν ξ.1 ξ.2 u k f t + |t| * ‖f‖) ∂canonicalLaw μ ν n) :=
      (ofReal_integral_eq_lintegral_ofReal (hint.add (integrable_const _))
        (Eventually.of_forall hnonneg)).symm
    _ = _ := by
      congr 1
      have h := integral_add hint (integrable_const (|t| * ‖f‖))
      simpa [integral_const, canonicalX, canonicalY] using h
end Metric

section Finsler
universe u₁ u₂
variable {E : Type u₁} {M : Type u₂} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}

omit [MeasurableSpace E] [BorelSpace E] in
/-- The true growing-iid tilted physical optimizer spends at most the supported
pressure mean and one bounded-probe correction, at the full physical mean scale. -/
theorem lintegral_originalIIDOptimalPhysicalPlan_finsler_supported_expected_slack_le
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (u : M → ℝ) (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ) :
    (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (finslerMeanScale E n *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
      ∂originalIIDOptimalPhysicalPlan
        (fun x y ↦ finslerMeanScale E n *
          ((F.lengthEDist x y).toReal - u y + u x) +
          t * finslerCarrierProbe μ ν K hK.measurableSet hμ hν f x y) 1 ξ
      ∂canonicalLaw μ ν n) ≤
      ENNReal.ofReal ((∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        ξ.1 ξ.2 u (finslerMeanScale E n) f t ∂canonicalLaw μ ν n) + |t| * ‖f‖) := by
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace inferInstance
  have h := lintegral_originalIIDOptimalPhysicalPlan_supported_expected_slack_le
    μ ν K hK hμ hν u hu (finslerMeanScale E n)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) f t n
  exact h

variable {u : M → ℝ} {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : ProbabilityMeasure M} {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ}
  {b : (ℚ → M) × ℝ → M} {r : ℝ} {δ loss : ℝ≥0∞}

omit [BorelSpace E] [∀ j, SigmaFinite (κ j)] in
/-- The explicit original unit-density upper packet supplies a finite eventual
energy budget for the actual iid tilted optimizer. No energy-budget callback is assumed. -/
theorem PopulationLocalPressureCore.exists_eventually_originalIID_supported_tilt_energy_bound
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
    (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
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
        ξ.1 ξ.2 u (finslerMeanScale E n) f t ∂canonicalLaw μ ν n) ≤ B := by
    exact ⟨_, hupper t 1 zero_lt_one⟩
  refine ⟨max 0 (B + |t| * ‖f‖), le_max_left _ _, ?_⟩
  filter_upwards [hB] with n hn
  have hcmp : (∫ ξ, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
      ξ.1 ξ.2 u (finslerMeanScale E n) f t ∂canonicalLaw μ ν n) + |t| * ‖f‖ ≤
      B + |t| * ‖f‖ := by linarith
  exact (lintegral_originalIIDOptimalPhysicalPlan_finsler_supported_expected_slack_le
    hcomplete μ ν K hK hμ hν u hu f t n).trans
      (ENNReal.ofReal_le_ofReal (hcmp.trans (le_max_right _ _)))
/-- The original geometric and calibrated coupling data themselves provide the eventual
finite slack budget for actual growing iid optimizers; no population energy oracle is used. -/
theorem exists_original_physical_supported_iid_tilt_energy_bound
    (hcore : PopulationHaarPressureCoreLaw P a κ ((μ : Measure M).map a) μ ν ρ₀ ρ₁ v b r)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂(μ : Measure M), x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂(ν : Measure M), y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂(μ : Measure M), b (a x,u x) = x) (hνinv : ∀ᵐ y ∂(ν : Measure M), b (a y,u y) = y)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A) (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    (πOriginal : Measure (M × M)) (hπOriginal : Vlasov.IsCoupling πOriginal μ ν)
    (hcalOriginal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂πOriginal, u p.2 - u p.1 = dist p.1 p.2)
    (hδne : δ ≠ 0) (hlossne : loss ≠ 0) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (retentionError splitError : ℝ) (hretention : 0 < retentionError)
    (hretention1 : retentionError < 1) (hsplitError : 0 < splitError)
    (K : Set M) (hK : IsCompact K)
    (hμK : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hνK : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (f : (K × K) →ᵇ ℝ)
    {ε probeError : ℝ} (hε : 0 < ε) (hprobe : 0 < probeError)
    (hsmall : 3 * ε + 2 * ε ^ 2 < 1) (hq : 4 < Module.finrank ℝ E - 1) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (finslerMeanScale E n *
          ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂originalIIDOptimalPhysicalPlan
          (fun x y ↦ finslerMeanScale E n *
            ((F.lengthEDist x y).toReal - u y + u x) +
            t * finslerCarrierProbe μ ν K hK.measurableSet hμK hνK f x y) 1 ξ
        ∂canonicalLaw μ ν n) ≤ ENNReal.ofReal C := by
  obtain ⟨g,hgnorm,hg,I,hI,originalGap,hgap,γ,hγ,D,Q,U,hdata⟩ :=
    exists_original_physical_unit_density_supported_upper hcore hκ hF hcomplete hu ha hinj
      horder hb hμreg hνreg hμinv hνinv hA hB hAB hμA hνB
      πOriginal hπOriginal hcalOriginal hδne hlossne hδ hδ1
      retentionError splitError hretention hretention1 hsplitError K hK hμK hνK f
      (fun n ↦ canonicalLaw μ ν n) (fun n ↦ canonicalX n) (fun n ↦ canonicalY n)
      (fun n ↦ measurable_canonicalX n) (fun n ↦ measurable_canonicalY n)
      (fun n ↦ iIndepFun_canonicalX μ ν n) (fun n ↦ iIndepFun_canonicalY μ ν n)
      (fun n ↦ canonicalLaw_map_canonicalX μ ν n)
      (fun n ↦ canonicalLaw_map_canonicalY μ ν n)
      (fun n ↦ indepFun_canonicalArrays μ ν n) hε hprobe hsmall hq
  exact D.exists_eventually_originalIID_supported_tilt_energy_bound hcomplete hu
    γ originalGap Q U retentionError splitError K hK hμK hνK f g ε probeError hdata t

end Finsler

end OTSelector.Reconstruction
