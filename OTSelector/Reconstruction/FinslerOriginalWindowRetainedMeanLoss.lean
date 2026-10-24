import OTSelector.Reconstruction.FinslerOriginalWindowRetainedPairKernel
import OTSelector.Probability.NormalizedRetainedPairKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Actual original finite-core window losses vanish in the unchanged original
population integral. This gives the recorded coarse repair mass expression. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- Actual retained original conditional mass loss, including scalar
retention, tends to zero in the unchanged original root integral. The bound
by 1 and measurability come from the literal original masked kernels. -/
theorem tendsto_originalWindowRetainedPairKernel_mean_lost_mass
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ) (hgap : 0 ≤ gap)
    (rn : ℕ → ℝ) (δn lossn : ℕ → ℝ≥0∞)
    (D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      (rn n) (δn n) (lossn n))
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (width : ∀ n, Fin (D n).haar.continuous.count → ℝ)
    (Q : ∀ n i, FiniteScalarBins range (width n i))
    (hδ : ∀ n, δn n ≠ ⊤) (hδ1 : ∀ n, (δn n).toReal < 1)
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0))
    (hloss : (∑' n, lossn n) ≠ ⊤)
    (η : ℕ → ℝ) (hηlim : Tendsto η atTop (𝓝 0)) (hη : ∀ n, 0 ≤ η n ∧ η n ≤ 1) :
    let χ := fun n ↦ (D n).originalWindowRetainedPairKernel hcomplete (Q n) γ
    (∀ n, Integrable (fun z ↦ 1 - (1 - η n) * (χ n z).real univ) (μ.map a)) ∧
    Tendsto (fun n ↦ ∫ z, 1 - (1 - η n) * (χ n z).real univ ∂μ.map a) atTop (𝓝 0) := by
  let χ := fun n ↦ (D n).originalWindowRetainedPairKernel hcomplete (Q n) γ
  have hactual := originalWindowRetainedPairKernel_ae_mass_recovery hrange γ gap hgap rn δn lossn
    D hcomplete width Q hδ hδ1 hδlim hloss
  have hm1 n z : (χ n z).real univ ≤ 1 := by
    simpa only [measureReal_def,measure_univ,ENNReal.toReal_one] using
      ENNReal.toReal_mono (measure_ne_top (γ z) univ) (hactual.1 n z univ)
  have hweight0 n z : 0 ≤ (1 - η n) * (χ n z).real univ :=
    mul_nonneg (sub_nonneg.mpr (hη n).2) measureReal_nonneg
  have hweight1 n z : (1 - η n) * (χ n z).real univ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hm1 n z) (sub_nonneg.mpr (hη n).2)
    nlinarith only [hh,(hη n).1]
  have hmeas n : AEStronglyMeasurable (fun z ↦ 1 - (1 - η n) * (χ n z).real univ) (μ.map a) :=
    (measurable_const.sub (measurable_const.mul
      (measurable_originalRetainedPairMass (χ n)))).aestronglyMeasurable
  have hbound n : ∀ᵐ z ∂μ.map a, ‖1 - (1 - η n) * (χ n z).real univ‖ ≤ (1:ℝ) := by
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hweight1 n z))]
    linarith only [hweight0 n z]
  have hlimit : ∀ᵐ z ∂μ.map a,
      Tendsto (fun n ↦ 1 - (1 - η n) * (χ n z).real univ) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hactual.2] with z hz
    have hc : Tendsto (fun _n : ℕ ↦ (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hh := hc.sub ((hc.sub hηlim).mul hz)
    simpa only [sub_zero,one_mul,sub_self] using hh
  have hi n : Integrable (fun z ↦ 1 - (1 - η n) * (χ n z).real univ) (μ.map a) :=
    (integrable_const (1:ℝ)).mono' (hmeas n) (hbound n)
  refine ⟨hi,?_⟩
  have hh := tendsto_integral_of_dominated_convergence (fun _z : ℚ → M ↦ (1:ℝ))
    hmeas (integrable_const _) hbound hlimit
  simpa only [integral_zero] using hh

/-- The actual original conditional lost-mass budget makes the recorded
coarse repair expression vanish with any fixed original skeleton constant.
This statement concerns the mass expression; the physical finite repair
witness remains the existing original typed-cost factory. -/
theorem tendsto_originalWindowRetainedMass_repair_expression
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ) (hgap : 0 ≤ gap)
    (rn : ℕ → ℝ) (δn lossn : ℕ → ℝ≥0∞)
    (D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      (rn n) (δn n) (lossn n))
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (width : ∀ n, Fin (D n).haar.continuous.count → ℝ)
    (Q : ∀ n i, FiniteScalarBins range (width n i))
    (hδ : ∀ n, δn n ≠ ⊤) (hδ1 : ∀ n, (δn n).toReal < 1)
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0))
    (hloss : (∑' n, lossn n) ≠ ⊤)
    (η : ℕ → ℝ) (hηlim : Tendsto η atTop (𝓝 0)) (hη : ∀ n, 0 ≤ η n ∧ η n ≤ 1)
    (hdim : 6 ≤ finrank ℝ E) (A G t : ℝ) :
    let χ := fun n ↦ (D n).originalWindowRetainedPairKernel hcomplete (Q n) γ
    let mass := fun n ↦ ∫ z, 1 - (1 - η n) * (χ n z).real univ ∂μ.map a
    Tendsto (fun n ↦ A * mass n ^ (1 - 2/(((finrank ℝ E - 1 : ℕ) : ℝ))) +
      2 * |t| * G * mass n) atTop (𝓝 0) := by
  have hm := (tendsto_originalWindowRetainedPairKernel_mean_lost_mass hrange γ gap hgap rn δn lossn
    D hcomplete width Q hδ hδ1 hδlim hloss η hηlim hη).2
  let q : ℝ := ((finrank ℝ E - 1 : ℕ) : ℝ)
  have hq : 2 < q := by dsimp only [q]; exact_mod_cast (by omega : 2 < finrank ℝ E - 1)
  have hexp : 0 < 1 - 2/q := sub_pos.mpr ((div_lt_one (by linarith only [hq])).mpr hq)
  have hp := (Real.continuous_rpow_const hexp.le).continuousAt.tendsto.comp hm
  have hh := (hp.const_mul A).add (hm.const_mul (2 * |t| * G))
  simpa only [Real.zero_rpow hexp.ne',mul_zero,add_zero,q,Function.comp_def] using hh

end OTSelector.Reconstruction
