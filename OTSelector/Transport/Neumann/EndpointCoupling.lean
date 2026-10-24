import OTSelector.Analysis.Sobolev.MeasureWeakNeumannFlux
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates
import OTSelector.Transport.Coupling.CostEquivalence
import OTSelector.Transport.Coupling.OptimalPlanExistence
import OTSelector.Transport.DensityNeumannInterpolation
import OTSelector.Transport.Finite.RetainedPlanRepair
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.LegalRepairEndpointCoupling.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.LegalRepairEndpointCoupling`; the selected original proof blocks follow. -/
section

/-!
Conditions: Actual Neumann discrepancy bounds and compact probability carriers; the Wasserstein-1 reduction additionally assumes the explicit CapturesLipschitzDual smoothing/localization property. Finite-plan variants have the stated nonnegative marginals.

Objects: An actual distance-cost endpoint coupling with the proved C·M bound, and measure realizations of finite repaired plans.

Proof detail: Construct the Hilbert flux, bound smooth test values by Cauchy–Schwarz, use the assumed capture property and KR duality, then take an actual compact-carrier optimal plan; compute finite Dirac marginals directly.

Sources: Terence Tao, Section 1.4, Theorem 1.4.13, p. 53 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=62); Gabriel Peyré, Section 6.1, Proposition 6.1 and equation (6.1), pp. 106–107 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=110); Gabriel Peyré, Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf); Terence Tao, Section 1.4, Lemma 1.4.7 (Cauchy–Schwarz inequality), p. 48 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=57).
Relation: The first result is conditional Wasserstein-1 repair, not an unconditional quadratic Benamou–Brenier theorem. CapturesLipschitzDual remains an explicit hypothesis; the finite coupling branch is constructive algebra.
-/

/-!
# Endpoint transport coupling from the actual weak Neumann flux

The Neumann-repair chain constructs the actual weak flux of the residual
discrepancy of two original endpoint densities and proves the Hamilton--Jacobi /
Young value comparison for it. This file delivers the endpoint coupling in two
complementary forms.

## (a) The Kantorovich--Rubinstein reduction of the Benamou--Brenier inverse

* the actual weak flux, its test pairings and its energy bound are constructed
  from the residual gradient estimate (no flux is assumed);
* every smooth original test is paired with the flux and bounded by the flux
  energy through Cauchy--Schwarz in the physical L² space;
* Kantorovich--Rubinstein duality (the vendor `Vlasov` development) turns the
  resulting bound on the `1`-Lipschitz dual value into a bound on the exact
  Kantorovich--Rubinstein distance;
* an original distance-optimal coupling is produced by the library compact-carrier
  optimal-plan theorem, and its `edist` cost is identified with the
  Kantorovich--Rubinstein distance.

The single unproved analytic input is `CapturesLipschitzDual`: compactly
supported smooth original tests capture every `1`-Lipschitz dual value with a
uniform physical gradient bound. This is the localization/smoothing statement
(mollification of a Lipschitz potential with pointwise gradient control). It is
not a repair callback: the flux, its energy, the dual comparison, the optimal
plan and the cost identity are all proved.

## (b) The finite repaired plan as an actual measure coupling

The corrected finite retained plan of `LegalRepairNeumannValue` is realized as
an actual measure on the product of the finite index types. It is proved to be a
`Vlasov` coupling of the two full endpoint measures with exact original
marginals, its total mass is the retained mass plus the common residual port
mass, and its actual extended cost is at most the retained cost plus the
explicit constant `L` times the common residual port mass.
-/
open Set MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace BoundedContinuousFunction ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual residual endpoint measure of the Neumann discrepancy: the
original reference measure weighted by the residual density. -/
def residualDensityMeasure (μ : Measure (ι → ℝ)) (f : (ι → ℝ) → ℝ) : Measure (ι → ℝ) :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))

/-- The compactly supported smooth original tests capture every `1`-Lipschitz
dual value with a uniform physical gradient bound. This is the remaining
localization/smoothing input of the Benamou--Brenier inverse: a Lipschitz
potential must be replaceable, without changing its value against the two
residual measures, by an original compactly supported smooth test whose physical
gradient stays in the ball of radius `M` in the reference `L²` space. -/
def CapturesLipschitzDual (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (f g : (ι → ℝ) → ℝ) (M : ℝ) : Prop :=
  ∀ (φ : (ι → ℝ) → ℝ), LipschitzWith 1 φ → ∀ ε > 0,
    ∃ ψ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖smoothPhysicalGradientLtwo K μ ψ‖ ≤ M ∧
      |((∫ x, φ x ∂(residualDensityMeasure μ f)) -
          ∫ x, φ x ∂(residualDensityMeasure μ g)) -
        ((∫ x, ψ x ∂(residualDensityMeasure μ f)) -
          ∫ x, ψ x ∂(residualDensityMeasure μ g))| ≤ ε

/-- **Endpoint transport coupling from the weak Neumann flux.** For two original
residual probability densities on a finite reference measure, the actual weak
flux constructed from the gradient estimate pairs with every original smooth
test and has bounded energy. If compactly supported smooth tests capture the
`1`-Lipschitz dual values with physical gradient norm at most `M`, then the two
residual measures admit an actual coupling whose extended-distance cost is at
most `C * M`, where `C` is the Neumann energy constant. -/
theorem exists_endpointCoupling_edist_le_of_neumannFlux
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (f g : (ι → ℝ) → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    {ρ C M : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hfl : ∀ᵐ x ∂μ, ρ ≤ f x) (hgl : ∀ᵐ x ∂μ, ρ ≤ g x)
    (hprobS : IsProbabilityMeasure (residualDensityMeasure μ f))
    (hprobT : IsProbabilityMeasure (residualDensityMeasure μ g))
    {K₀ : Set (ι → ℝ)} (hK₀ : IsCompact K₀)
    (hsuppS : ∀ᵐ x ∂(residualDensityMeasure μ f), x ∈ K₀)
    (hsuppT : ∀ᵐ x ∂(residualDensityMeasure μ g), x ∈ K₀)
    (hbound : ∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖(∫ x, φ x * f x ∂μ) - ∫ x, φ x * g x ∂μ‖ ≤
        C * ‖smoothPhysicalGradientLtwo K μ φ‖)
    (hcapture : CapturesLipschitzDual K μ f g M) :
    ∃ π : Measure ((ι → ℝ) × (ι → ℝ)),
      Vlasov.IsCoupling π (residualDensityMeasure μ f) (residualDensityMeasure μ g) ∧
      (∫⁻ z, edist z.1 z.2 ∂π) ≤ ENNReal.ofReal (C * M) := by
  have hfp : ∀ᵐ x ∂μ, 0 ≤ f x := hfl.mono fun _ hx => hρ.le.trans hx
  have hgp : ∀ᵐ x ∂μ, 0 ≤ g x := hgl.mono fun _ hx => hρ.le.trans hx
  haveI : IsFiniteMeasure (residualDensityMeasure μ f) :=
    isFiniteMeasure_withDensity_ofReal hf.2
  haveI : IsFiniteMeasure (residualDensityMeasure μ g) :=
    isFiniteMeasure_withDensity_ofReal hg.2
  -- the actual weak flux, its test pairings and its energy bound
  obtain ⟨j, hflux, hjI, hjE, -⟩ := exists_originalMeasure_weakNeumannFlux K μ
    (residualDensityMeasure μ f) (residualDensityMeasure μ g) hC (by
      intro φ
      simpa only [residualDensityMeasure,
        originalDensity_test_integral K μ φ hf.aemeasurable hfp,
        originalDensity_test_integral K μ φ hg.aemeasurable hgp] using hbound φ)
  have hfluxEnergy : ‖j‖ ≤ C := by
    have hsq : ‖j‖ ^ 2 ≤ C ^ 2 := by
      rw [physicalFlux_norm_sq]
      exact hjE
    calc ‖j‖ = Real.sqrt (‖j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg j)).symm
      _ ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt hsq
      _ = C := Real.sqrt_sq hC
  -- every smooth original test with bounded physical gradient is bounded by the
  -- actual flux energy
  have htestBound : ∀ ψ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖smoothPhysicalGradientLtwo K μ ψ‖ ≤ M →
      (∫ x, ψ x ∂(residualDensityMeasure μ f)) -
        (∫ x, ψ x ∂(residualDensityMeasure μ g)) ≤ C * M := by
    intro ψ hψM
    rw [← hflux ψ, ← inner_smoothPhysicalGradientLtwo K μ j ψ]
    calc inner ℝ j (smoothPhysicalGradientLtwo K μ ψ)
        ≤ |inner ℝ j (smoothPhysicalGradientLtwo K μ ψ)| := le_abs_self _
      _ ≤ ‖j‖ * ‖smoothPhysicalGradientLtwo K μ ψ‖ := abs_real_inner_le_norm _ _
      _ ≤ C * M := mul_le_mul hfluxEnergy hψM (norm_nonneg _) hC
  -- the `1`-Lipschitz dual value is bounded by the same constant
  have hdualBound : ∀ (φ : (ι → ℝ) → ℝ), LipschitzWith 1 φ →
      (∫ x, φ x ∂(residualDensityMeasure μ f)) -
        (∫ x, φ x ∂(residualDensityMeasure μ g)) ≤ C * M := by
    intro φ hφ
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨ψ, hψM, hψε⟩ := hcapture φ hφ ε hε
    have hψle := htestBound ψ hψM
    have habs := (abs_le.mp hψε).2
    linarith
  -- Kantorovich--Rubinstein dual bound
  have hwasserstein : Vlasov.wasserstein1 (residualDensityMeasure μ f)
      (residualDensityMeasure μ g) ≤ ENNReal.ofReal (C * M) := by
    rw [Vlasov.wasserstein1_eq_iSup_lipschitz]
    exact iSup_le fun φ => iSup_le fun hφ => ENNReal.ofReal_le_ofReal (hdualBound φ hφ)
  -- the actual original distance-optimal coupling on the compact carrier
  haveI := hprobS
  haveI := hprobT
  obtain ⟨π, hπopt⟩ := exists_isOptimalCoupling_edist_of_compact_carrier
    (residualDensityMeasure μ f) (residualDensityMeasure μ g) hK₀ hsuppS hsuppT
  refine ⟨π, hπopt.1, ?_⟩
  -- finite first moments on the compact carrier
  have hfinS : Integrable (fun y => dist y 0) (residualDensityMeasure μ f) := by
    obtain ⟨Rm, hRm⟩ := hK₀.isBounded.exists_norm_le
    refine Integrable.mono' (integrable_const Rm)
      (continuous_id.dist continuous_const).aestronglyMeasurable ?_
    filter_upwards [hsuppS] with y hy
    rw [Real.norm_eq_abs, dist_zero_right, abs_of_nonneg (norm_nonneg _)]
    exact hRm y hy
  have hfinT : Integrable (fun y => dist y 0) (residualDensityMeasure μ g) := by
    obtain ⟨Rm, hRm⟩ := hK₀.isBounded.exists_norm_le
    refine Integrable.mono' (integrable_const Rm)
      (continuous_id.dist continuous_const).aestronglyMeasurable ?_
    filter_upwards [hsuppT] with y hy
    rw [Real.norm_eq_abs, dist_zero_right, abs_of_nonneg (norm_nonneg _)]
    exact hRm y hy
  -- Kantorovich--Rubinstein duality identifies the optimal cost with the dual value
  have hKR : Vlasov.wasserstein1 (residualDensityMeasure μ f)
      (residualDensityMeasure μ g) =
      Vlasov.wasserstein1Coupling (residualDensityMeasure μ f)
        (residualDensityMeasure μ g) :=
    Vlasov.wasserstein1_eq_coupling _ _ 0 hfinS hfinT
  have hcost : (∫⁻ z, edist z.1 z.2 ∂π) ≤
      Vlasov.wasserstein1Coupling (residualDensityMeasure μ f)
        (residualDensityMeasure μ g) := by
    rw [Vlasov.wasserstein1Coupling]
    exact le_iInf fun κ => le_iInf fun hκ => by
      simpa only [couplingCost] using hπopt.2 κ hκ
  calc (∫⁻ z, edist z.1 z.2 ∂π)
      ≤ Vlasov.wasserstein1Coupling (residualDensityMeasure μ f)
          (residualDensityMeasure μ g) := hcost
    _ = Vlasov.wasserstein1 (residualDensityMeasure μ f)
          (residualDensityMeasure μ g) := hKR.symm
    _ ≤ ENNReal.ofReal (C * M) := hwasserstein

/-! ## (b) The finite repaired plan as an actual measure coupling -/

section MeasuredRepairedCoupling
variable {S T : Type*} [Fintype S] [Fintype T]
  [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T]

/-- The finite discrete measure with the given real weights. -/
def finiteWeightedMeasure (w : S → ℝ) : Measure S :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

/-- The finite plan measure with the given real weights on the product. -/
def finitePlanMeasure (q : S → T → ℝ) : Measure (S × T) :=
  ∑ p : S × T, ENNReal.ofReal (q p.1 p.2) • Measure.dirac p

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
/-- The continuous-discrete source marginal of an actual finite plan. -/
theorem finitePlanMeasure_fst (q : S → T → ℝ) (hq : ∀ i j, 0 ≤ q i j) :
    (finitePlanMeasure q).map Prod.fst = finiteWeightedMeasure (fun i => ∑ j, q i j) := by
  rw [finitePlanMeasure, finiteWeightedMeasure,
    Measure.map_finset_sum' (f := Prod.fst) measurable_fst.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac' measurable_fst]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (∑ y : T, ENNReal.ofReal (q i y) • Measure.dirac i) =
    ENNReal.ofReal (∑ j, q i j) • Measure.dirac i
  rw [← Finset.sum_smul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => hq i j)]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
/-- The continuous-discrete target marginal of an actual finite plan. -/
theorem finitePlanMeasure_snd (q : S → T → ℝ) (hq : ∀ i j, 0 ≤ q i j) :
    (finitePlanMeasure q).map Prod.snd = finiteWeightedMeasure (fun j => ∑ i, q i j) := by
  rw [finitePlanMeasure, finiteWeightedMeasure,
    Measure.map_finset_sum' (f := Prod.snd) measurable_snd.aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac' measurable_snd]
  rw [Fintype.sum_prod_type]
  change (∑ i : S, ∑ y : T, ENNReal.ofReal (q i y) • Measure.dirac y) =
    (∑ j : T, ENNReal.ofReal (∑ i : S, q i j) • Measure.dirac j)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (∑ i : S, ENNReal.ofReal (q i j) • Measure.dirac j) =
    ENNReal.ofReal (∑ i, q i j) • Measure.dirac j
  rw [← Finset.sum_smul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => hq i j)]

omit [MeasurableSingletonClass S] in
/-- The total mass of the finite weighted measure. -/
theorem finiteWeightedMeasure_univ {w : S → ℝ} (hw : ∀ i, 0 ≤ w i) :
    finiteWeightedMeasure w univ = ENNReal.ofReal (∑ i, w i) := by
  rw [finiteWeightedMeasure, Measure.finsetSum_apply,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => hw i)]
  simp

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
/-- **The repaired retained plan is an actual full coupling.** The corrected finite
plan is realized as an actual measure on the product; it is a coupling of the two
full endpoint measures, i.e. it has the exact full source and target marginals. -/
theorem repairedRetainedPlan_measure_isCoupling
    {p : S → T → ℝ} {rsrc : S → ℝ} {rtgt : T → ℝ} {a : S → ℝ} {b : T → ℝ}
    (hp : ∀ i j, 0 ≤ p i j) (hrsrc : ∀ i, 0 ≤ rsrc i) (hrtgt : ∀ j, 0 ≤ rtgt j)
    (hmass : (∑ i, rsrc i) = ∑ j, rtgt j)
    (hrow : ∀ i, (∑ j, p i j) + rsrc i = a i)
    (hcol : ∀ j, (∑ i, p i j) + rtgt j = b j) :
    Vlasov.IsCoupling (finitePlanMeasure (repairedRetainedPlan p rsrc rtgt))
      (finiteWeightedMeasure a) (finiteWeightedMeasure b) := by
  have hq : ∀ i j, 0 ≤ repairedRetainedPlan p rsrc rtgt i j :=
    repairedRetainedPlan_nonneg hp hrsrc hrtgt
  constructor
  · rw [finitePlanMeasure_fst _ hq]
    congr 1
    funext i
    exact repairedRetainedPlan_row_sum hrsrc hmass hrow i
  · rw [finitePlanMeasure_snd _ hq]
    congr 1
    funext j
    exact repairedRetainedPlan_col_sum hrtgt hmass hcol j

/-- The actual extended cost of the repaired finite plan measure. -/
theorem repairedRetainedPlan_measureCost
    {p : S → T → ℝ} {rsrc : S → ℝ} {rtgt : T → ℝ} {cost : S → T → ℝ}
    (hp : ∀ i j, 0 ≤ p i j) (hrsrc : ∀ i, 0 ≤ rsrc i) (hrtgt : ∀ j, 0 ≤ rtgt j)
    (hcost : ∀ i j, 0 ≤ cost i j) :
    (∫⁻ z, ENNReal.ofReal (cost z.1 z.2) ∂
        finitePlanMeasure (repairedRetainedPlan p rsrc rtgt)) =
      ENNReal.ofReal (∑ i, ∑ j, repairedRetainedPlan p rsrc rtgt i j * cost i j) := by
  have hq : ∀ i j, 0 ≤ repairedRetainedPlan p rsrc rtgt i j :=
    repairedRetainedPlan_nonneg hp hrsrc hrtgt
  rw [finitePlanMeasure, lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  change (∑ i : S, ∑ j : T, ENNReal.ofReal (repairedRetainedPlan p rsrc rtgt i j) *
      ENNReal.ofReal (cost i j)) =
    ENNReal.ofReal (∑ i, ∑ j, repairedRetainedPlan p rsrc rtgt i j * cost i j)
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hq i j) (hcost i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg
    (fun j _ => mul_nonneg (hq i j) (hcost i j))]
  exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_mul (hq i j)).symm

/-- **The explicit cost comparison for the repaired finite coupling.** If every
original cost entry is nonnegative and bounded by `L`, then the actual extended
cost of the repaired measure coupling is at most the retained plan cost plus
`L` times the common residual port mass. -/
theorem repairedRetainedPlan_measureCost_le
    {p : S → T → ℝ} {rsrc : S → ℝ} {rtgt : T → ℝ} {cost : S → T → ℝ} {L : ℝ}
    (hp : ∀ i j, 0 ≤ p i j) (hrsrc : ∀ i, 0 ≤ rsrc i) (hrtgt : ∀ j, 0 ≤ rtgt j)
    (hmass : (∑ i, rsrc i) = ∑ j, rtgt j)
    (hcost : ∀ i j, 0 ≤ cost i j) (hcostL : ∀ i j, cost i j ≤ L) :
    (∫⁻ z, ENNReal.ofReal (cost z.1 z.2) ∂
        finitePlanMeasure (repairedRetainedPlan p rsrc rtgt)) ≤
      ENNReal.ofReal ((∑ i, ∑ j, p i j * cost i j) + L * ∑ i, rsrc i) := by
  rw [repairedRetainedPlan_measureCost hp hrsrc hrtgt hcost]
  apply ENNReal.ofReal_le_ofReal
  have hadd : (∑ i, ∑ j, (repairedRetainedPlan p rsrc rtgt i j - p i j) * cost i j) ≤
      L * ∑ i, rsrc i :=
    repairedRetainedPlan_addedCost_le (p := p) hrsrc hrtgt hmass hcostL
  have hsplit : (∑ i, ∑ j, repairedRetainedPlan p rsrc rtgt i j * cost i j) =
      (∑ i, ∑ j, p i j * cost i j) +
        (∑ i, ∑ j, (repairedRetainedPlan p rsrc rtgt i j - p i j) * cost i j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsplit]
  linarith

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] in
/-- **The full repaired coupling, its exact marginals and its mass.** Combining the
measure-level coupling with the mass computation: the repaired plan is an actual
coupling of the two full endpoint measures whose total mass is the retained plan
mass plus the common residual port mass. -/
theorem repairedRetainedPlan_fullCoupling
    {p : S → T → ℝ} {rsrc : S → ℝ} {rtgt : T → ℝ} {a : S → ℝ} {b : T → ℝ}
    (hp : ∀ i j, 0 ≤ p i j) (hrsrc : ∀ i, 0 ≤ rsrc i) (hrtgt : ∀ j, 0 ≤ rtgt j)
    (hmass : (∑ i, rsrc i) = ∑ j, rtgt j)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hrow : ∀ i, (∑ j, p i j) + rsrc i = a i)
    (hcol : ∀ j, (∑ i, p i j) + rtgt j = b j) :
    Vlasov.IsCoupling (finitePlanMeasure (repairedRetainedPlan p rsrc rtgt))
        (finiteWeightedMeasure a) (finiteWeightedMeasure b) ∧
      (finiteWeightedMeasure a) univ = ENNReal.ofReal (∑ i, a i) ∧
      (finiteWeightedMeasure b) univ = ENNReal.ofReal (∑ j, b j) ∧
      (∑ i, a i) = (∑ i, ∑ j, p i j) + ∑ i, rsrc i := by
  have hcoupling := repairedRetainedPlan_measure_isCoupling hp hrsrc hrtgt hmass hrow hcol
  have haMass := finiteWeightedMeasure_univ ha
  have hbMass := finiteWeightedMeasure_univ hb
  refine ⟨hcoupling, haMass, hbMass, ?_⟩
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (hrow i).symm

end MeasuredRepairedCoupling

end OTSelector.Reconstruction

end
end
