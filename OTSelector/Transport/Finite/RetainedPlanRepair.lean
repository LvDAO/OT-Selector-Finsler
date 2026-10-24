import OTSelector.Analysis.HamiltonJacobiFluxYoung
import OTSelector.Analysis.Sobolev.MeasureWeakNeumannFlux
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates
import OTSelector.Transport.DensityNeumannInterpolation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.LegalRepairNeumannValue.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.LegalRepairNeumannValue`; the selected original proof blocks follow. -/
section

/-!
Conditions: Finite reference measure, actual weak flux/discrepancy bounds, positive density lower bound and actual Hamilton–Jacobi-admissible tests; finite-plan variants have equal nonnegative residual masses.

Objects: Signed endpoint-value energy comparison and an actual retained-plus-product repaired finite plan with exact marginals and cost bound.

Proof detail: Apply pointwise Young to the true flux pairing and integrate; construct the residual normalized product, then sum its rows, columns, mass and bounded added cost.

Sources: Stephen Boyd, Section 3.3.2, Fenchel’s inequality and quadratic example, p. 94 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=108); Terence Tao, Section 1.4, Theorem 1.4.13, p. 53 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=62); Gabriel Peyré, Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf).
Relation: Combination of Hilbert weak flux, quadratic Young and elementary product coupling. The exact signed bound and repair assembly are locally proved.
-/

/-!
# The legal residual-repair signed value comparison

The Neumann-repair chain constructs the actual weak flux of the residual
discrepancy of the two original endpoint measures and proves the
Hamilton--Jacobi/Young comparison for the same flux. This file closes the next
step: the signed value comparison for a repaired pair of original endpoint
potentials.

For a finite original physical reference measure `μ`, two residual endpoint
densities `f` (source) and `g` (target) that share the positive lower bound
`ρ`, and a weak flux `j` realizing the actual residual discrepancy, any pair of
original compactly supported smooth tests `Asrc`, `Atgt` that is admissible for
the Hamilton--Jacobi inequality

  `Atgt x - Asrc x + ‖∇Asrc x‖² / 2 ≤ 0`

has its signed endpoint value controlled by half the flux energy:

  `∫ Atgt ∂ν₁ - ∫ Asrc ∂ν₀ ≤ ρ⁻¹ * ∫ ‖j‖² / 2`.

Applying the actual flux construction turns the right-hand side into the
explicit constant `ρ⁻¹ C² / 2`. No repair callback is assumed: the flux, its
test pairings and its energy are outputs of the Neumann construction, and the
Hamilton--Jacobi admissibility is a pointwise property of the two actual tests.
-/
open Set MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2200000
set_option linter.style.haveILetI false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bounded-continuous physical gradient of an original smooth test is
exactly the packed coordinate gradient of its Fréchet derivative. -/
theorem smoothPhysicalGradient_eq_physicalCoordinateGradient
    (K : Compacts (ι → ℝ)) (φ : 𝓓_{K}(ι → ℝ, ℝ)) (x : ι → ℝ) :
    smoothPhysicalGradient K φ x = physicalCoordinateGradient ι (fderiv ℝ φ x) := by
  ext i
  rw [smoothPhysicalGradient_apply, physicalCoordinateGradient_apply]

omit [DecidableEq ι] in
/-- A function with finite second moment on a finite measure has integrable norm;
this is the domination used for the flux/gradient pairing. -/
theorem integrable_norm_of_integrable_sq
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {j : X → EuclideanSpace ℝ ι} (hjm : AEStronglyMeasurable j μ)
    (hj : Integrable (fun x => ‖j x‖ ^ 2) μ) :
    Integrable (fun x => ‖j x‖) μ := by
  have h1 : Integrable (fun x : X => ‖j x‖ ^ 2 + 1) μ :=
    hj.add (integrable_const (1 : ℝ))
  have h2 : Integrable (fun x : X => (‖j x‖ ^ 2 + 1) / 2) μ := h1.div_const 2
  refine h2.mono' ?_ ?_
  · exact hjm.norm
  · filter_upwards with x
    have h : ‖j x‖ ≤ (‖j x‖ ^ 2 + 1) / 2 := by
      nlinarith [sq_nonneg (‖j x‖ - 1)]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h

/-- **Signed legal residual-repair value comparison.** For the actual weak flux
`j` of the residual discrepancy between the source residual density `f` and
the target residual density `g`, and for any original compactly supported
smooth endpoint potentials satisfying the pointwise Hamilton--Jacobi
admissibility, the signed endpoint value is at most half the flux energy divided
by the positive lower density bound. -/
theorem legalRepair_valueComparison_of_flux
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (f g : (ι → ℝ) → ℝ)
    (Asrc Atgt : 𝓓_{K}(ι → ℝ, ℝ))
    (j : Lp (EuclideanSpace ℝ ι) 2 μ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hg : Integrable g μ) (hgl : ∀ᵐ x ∂μ, ρ ≤ g x)
    (hjI : Integrable (fun x => ‖j x‖ ^ 2) μ)
    (hflux : (∫ x, inner ℝ (j x) (physicalCoordinateGradient ι (fderiv ℝ Asrc x)) ∂μ) =
      (∫ x, Asrc x * f x ∂μ) - ∫ x, Asrc x * g x ∂μ)
    (hHJ : ∀ x, Atgt x - Asrc x +
      ‖physicalCoordinateGradient ι (fderiv ℝ Asrc x)‖ ^ 2 / 2 ≤ 0) :
    (∫ x, Atgt x * g x ∂μ) - (∫ x, Asrc x * f x ∂μ) ≤
      ρ⁻¹ * (∫ x, ‖j x‖ ^ 2 ∂μ) / 2 := by
  -- the packed gradient and its uniform bound
  set p : (ι → ℝ) → EuclideanSpace ℝ ι :=
    fun x => physicalCoordinateGradient ι (fderiv ℝ Asrc x) with hp
  have hpdef : ∀ x, p x = physicalCoordinateGradient ι (fderiv ℝ Asrc x) := fun _ => rfl
  have hpmem : ∀ x, ‖p x‖ ≤ ‖smoothPhysicalGradient K Asrc‖ := by
    intro x
    rw [hpdef x, ← smoothPhysicalGradient_eq_physicalCoordinateGradient K Asrc x]
    exact (smoothPhysicalGradient K Asrc).norm_coe_le_norm x
  have hpmeas : AEStronglyMeasurable p μ := by
    have hEq : p = ⇑(smoothPhysicalGradient K Asrc) :=
      funext fun x => (smoothPhysicalGradient_eq_physicalCoordinateGradient K Asrc x).symm
    rw [hEq]
    exact (smoothPhysicalGradient K Asrc).continuous.aestronglyMeasurable
  -- the increment potential is nonpositive
  have hincnonpos : ∀ x, Atgt x - Asrc x ≤ 0 := by
    intro x
    have h := hHJ x
    have hsq : 0 ≤ ‖p x‖ ^ 2 / 2 := by positivity
    linarith
  -- integrability of the incremental density pairing
  have hAsrcInt : Integrable (fun x => Asrc x) μ :=
    BoundedContinuousFunction.integrable μ
      (ContDiffMapSupportedIn.toBoundedContinuousFunctionLM ℝ Asrc)
  have hAtgtInt : Integrable (fun x => Atgt x) μ :=
    BoundedContinuousFunction.integrable μ
      (ContDiffMapSupportedIn.toBoundedContinuousFunctionLM ℝ Atgt)
  have hdr : Integrable (fun x => (Atgt x - Asrc x) * ρ) μ :=
    (hAtgtInt.sub hAsrcInt).mul_const ρ
  -- integrability of the flux/gradient pairing
  have hjnorm : Integrable (fun x => ‖j x‖) μ :=
    integrable_norm_of_integrable_sq (j := fun x => j x) (Lp.aestronglyMeasurable j) hjI
  have hjp : Integrable (fun x => inner ℝ (j x) (p x)) μ := by
    have hdom : Integrable (fun x => ‖smoothPhysicalGradient K Asrc‖ * ‖j x‖) μ := by
      have h := hjnorm.mul_const ‖smoothPhysicalGradient K Asrc‖
      simpa only [mul_comm] using h
    refine hdom.mono' ?_ ?_
    · exact (Lp.aestronglyMeasurable j).inner hpmeas
    · filter_upwards with x
      calc ‖inner ℝ (j x) (p x)‖ ≤ ‖j x‖ * ‖p x‖ := norm_inner_le_norm _ _
        _ ≤ ‖j x‖ * ‖smoothPhysicalGradient K Asrc‖ :=
            mul_le_mul_of_nonneg_left (hpmem x) (norm_nonneg _)
        _ = ‖smoothPhysicalGradient K Asrc‖ * ‖j x‖ := by ring
  -- integrability of the weighted flux action
  have hact : Integrable (fun x => ‖j x‖ ^ 2 / ρ) μ := by
    have h := hjI.mul_const ρ⁻¹
    simpa only [div_eq_mul_inv] using h
  -- the density-weighted Young comparison
  have hKey : (∫ x, (Atgt x - Asrc x) * ρ ∂μ) - (∫ x, inner ℝ (j x) (p x) ∂μ) ≤
      (∫ x, ‖j x‖ ^ 2 / ρ ∂μ) / 2 := by
    refine integral_hamiltonJacobi_flux_le μ (fun x => j x) p
      (fun x => Atgt x - Asrc x) (fun _ => ρ) hdr hjp hact ?_ ?_
    · exact ae_of_all _ fun _ => hρ
    · exact ae_of_all _ fun x => hHJ x
  -- the actual density comparison and the flux integral
  have hAg : Integrable (fun x => Asrc x * g x) μ :=
    hg.mul_of_top_right
      (BoundedContinuousFunction.memLp_top
        (ContDiffMapSupportedIn.toBoundedContinuousFunctionLM ℝ Asrc))
  have hIncg : Integrable (fun x => (Atgt x - Asrc x) * g x) μ := by
    have h : Integrable (fun x => (Atgt x * g x) - (Asrc x * g x)) μ := by
      have hAtgtg : Integrable (fun x => Atgt x * g x) μ :=
        hg.mul_of_top_right
          (BoundedContinuousFunction.memLp_top
            (ContDiffMapSupportedIn.toBoundedContinuousFunctionLM ℝ Atgt))
      exact hAtgtg.sub hAg
    refine h.congr ?_
    filter_upwards with x
    ring
  have hdensity : (∫ x, (Atgt x - Asrc x) * g x ∂μ) ≤
      ∫ x, (Atgt x - Asrc x) * ρ ∂μ := by
    refine integral_mono_ae hIncg hdr ?_
    filter_upwards [hgl] with x hx
    exact mul_le_mul_of_nonpos_left hx (hincnonpos x)
  -- the value splits into the incremental density term and the flux pairing
  have hsplit : (∫ x, Atgt x * g x ∂μ) =
      (∫ x, (Atgt x - Asrc x) * g x ∂μ) + ∫ x, Asrc x * g x ∂μ := by
    have hEq : (fun x => Atgt x * g x) =
        (fun x => (Atgt x - Asrc x) * g x + Asrc x * g x) := by
      funext x
      ring
    rw [hEq, integral_add hIncg hAg]
  have hflux' : (∫ x, inner ℝ (j x) (p x) ∂μ) =
      (∫ x, Asrc x * f x ∂μ) - ∫ x, Asrc x * g x ∂μ := by
    simpa only [hpdef] using hflux
  have hnormEq : (∫ x, ‖j x‖ ^ 2 / ρ ∂μ) = ρ⁻¹ * ∫ x, ‖j x‖ ^ 2 ∂μ := by
    rw [show (fun x => ‖j x‖ ^ 2 / ρ) = (fun x => ‖j x‖ ^ 2 * ρ⁻¹) from
      funext fun x => by rw [div_eq_mul_inv]]
    rw [integral_mul_const]
    ring
  calc
    (∫ x, Atgt x * g x ∂μ) - (∫ x, Asrc x * f x ∂μ)
        = (∫ x, (Atgt x - Asrc x) * g x ∂μ) +
            ((∫ x, Asrc x * g x ∂μ) - ∫ x, Asrc x * f x ∂μ) := by
          rw [hsplit]
          ring
    _ = (∫ x, (Atgt x - Asrc x) * g x ∂μ) -
          (∫ x, inner ℝ (j x) (p x) ∂μ) := by
          rw [hflux']
          ring
    _ ≤ (∫ x, (Atgt x - Asrc x) * ρ ∂μ) -
          (∫ x, inner ℝ (j x) (p x) ∂μ) := by linarith [hdensity]
    _ ≤ (∫ x, ‖j x‖ ^ 2 / ρ ∂μ) / 2 := hKey
    _ = ρ⁻¹ * (∫ x, ‖j x‖ ^ 2 ∂μ) / 2 := by rw [hnormEq]

/-- **The legal residual-repair value comparison with explicit constants.** The
actual weak Neumann flux of the residual discrepancy is constructed from the
actual gradient bound `C` on the two residual densities, so the signed repaired
endpoint value is at most the explicit constant `ρ⁻¹ C² / 2`. No flux, energy
or comparison is assumed. -/
theorem legalResidualRepair_signedValue_le
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (f g : (ι → ℝ) → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hfl : ∀ᵐ x ∂μ, ρ ≤ f x) (hgl : ∀ᵐ x ∂μ, ρ ≤ g x)
    (hbound : ∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖(∫ x, φ x * f x ∂μ) - ∫ x, φ x * g x ∂μ‖ ≤
        C * ‖smoothPhysicalGradientLtwo K μ φ‖)
    (Asrc Atgt : 𝓓_{K}(ι → ℝ, ℝ))
    (hHJ : ∀ x, Atgt x - Asrc x +
      ‖physicalCoordinateGradient ι (fderiv ℝ Asrc x)‖ ^ 2 / 2 ≤ 0) :
    (∫ x, Atgt x * g x ∂μ) - (∫ x, Asrc x * f x ∂μ) ≤ ρ⁻¹ * C ^ 2 / 2 := by
  have hfp : ∀ᵐ x ∂μ, 0 ≤ f x := hfl.mono fun _ hx => hρ.le.trans hx
  have hgp : ∀ᵐ x ∂μ, 0 ≤ g x := hgl.mono fun _ hx => hρ.le.trans hx
  haveI : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (f x)) :=
    isFiniteMeasure_withDensity_ofReal hf.2
  haveI : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (g x)) :=
    isFiniteMeasure_withDensity_ofReal hg.2
  obtain ⟨j, hflux, hjI, hjE, -⟩ := exists_originalMeasure_weakNeumannFlux K μ
    (μ.withDensity fun x => ENNReal.ofReal (f x))
    (μ.withDensity fun x => ENNReal.ofReal (g x)) hC (by
      intro φ
      simpa only [originalDensity_test_integral K μ φ hf.aemeasurable hfp,
        originalDensity_test_integral K μ φ hg.aemeasurable hgp] using hbound φ)
  have hfluxA : (∫ x, inner ℝ (j x)
        (physicalCoordinateGradient ι (fderiv ℝ Asrc x)) ∂μ) =
      (∫ x, Asrc x * f x ∂μ) - ∫ x, Asrc x * g x ∂μ := by
    have h := hflux Asrc
    simpa only [originalDensity_test_integral K μ Asrc hf.aemeasurable hfp,
      originalDensity_test_integral K μ Asrc hg.aemeasurable hgp] using h
  have hvalue := legalRepair_valueComparison_of_flux K μ f g Asrc Atgt j hρ hg hgl hjI hfluxA hHJ
  have henergy : ρ⁻¹ * (∫ x, ‖j x‖ ^ 2 ∂μ) / 2 ≤ ρ⁻¹ * C ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left hjE (inv_nonneg.mpr hρ.le)
    linarith
  exact hvalue.trans henergy

/-- **Absolute signed value comparison.** If the two original endpoint
potentials are admissible in both Hamilton--Jacobi directions, the signed
repaired value is bounded in absolute value by the explicit constant
`ρ⁻¹ C² / 2`. The reverse direction is the same actual flux construction for
the swapped residual discrepancy, so no additional energy is assumed. -/
theorem legalResidualRepair_absSignedValue_le
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (f g : (ι → ℝ) → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    {ρ C : ℝ} (hρ : 0 < ρ) (hC : 0 ≤ C)
    (hfl : ∀ᵐ x ∂μ, ρ ≤ f x) (hgl : ∀ᵐ x ∂μ, ρ ≤ g x)
    (hbound : ∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖(∫ x, φ x * f x ∂μ) - ∫ x, φ x * g x ∂μ‖ ≤
        C * ‖smoothPhysicalGradientLtwo K μ φ‖)
    (Asrc Atgt : 𝓓_{K}(ι → ℝ, ℝ))
    (hHJsrc : ∀ x, Atgt x - Asrc x +
      ‖physicalCoordinateGradient ι (fderiv ℝ Asrc x)‖ ^ 2 / 2 ≤ 0)
    (hHJtgt : ∀ x, Asrc x - Atgt x +
      ‖physicalCoordinateGradient ι (fderiv ℝ Atgt x)‖ ^ 2 / 2 ≤ 0) :
    |(∫ x, Atgt x * g x ∂μ) - (∫ x, Asrc x * f x ∂μ)| ≤ ρ⁻¹ * C ^ 2 / 2 := by
  have hupper := legalResidualRepair_signedValue_le K μ f g hf hg hρ hC hfl hgl
    hbound Asrc Atgt hHJsrc
  have hbound' : ∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖(∫ x, φ x * g x ∂μ) - ∫ x, φ x * f x ∂μ‖ ≤
        C * ‖smoothPhysicalGradientLtwo K μ φ‖ := by
    intro φ
    simpa only [norm_sub_rev] using hbound φ
  have hlower := legalResidualRepair_signedValue_le K μ g f hg hf hρ hC hgl hfl
    hbound' Atgt Asrc hHJtgt
  refine abs_le.mpr ⟨?_, hupper⟩
  linarith


/-! ## The corrected finite retained plan

The actual retained finite plan leaves two residual port masses uncoupled. On
finite index types the following construction keeps every retained atom and
couples the two residual port masses by the normalized product plan carrying
exactly their common total residual mass. The corrected plan has the exact
full source and target marginals, keeps all retained atoms, conserves total
mass additively, and its added cost is at most the explicit constant
`L * residual mass` for any cost bounded by `L`. -/
section FiniteCorrectedPlan
variable {S T : Type*} [Fintype S] [Fintype T]

/-- The corrected finite retained plan: each retained atom is kept unchanged
and the residual source and target port masses are coupled by the product plan
normalized by their common total residual mass. -/
def repairedRetainedPlan (p : S → T → ℝ) (rsrc : S → ℝ) (rtgt : T → ℝ) : S → T → ℝ :=
  fun i j => p i j + rsrc i * rtgt j / ∑ k, rsrc k

omit [Fintype T] in
/-- Every entry of the corrected plan is nonnegative. -/
theorem repairedRetainedPlan_nonneg {p : S → T → ℝ} {rsrc : S → ℝ} {rtgt : T → ℝ}
    (hp : ∀ i j, 0 ≤ p i j) (hrsrc : ∀ i, 0 ≤ rsrc i) (hrtgt : ∀ j, 0 ≤ rtgt j) :
    ∀ i j, 0 ≤ repairedRetainedPlan p rsrc rtgt i j := by
  intro i j
  have hm : 0 ≤ ∑ k, rsrc k := Finset.sum_nonneg fun k _ => hrsrc k
  exact add_nonneg (hp i j) (div_nonneg (mul_nonneg (hrsrc i) (hrtgt j)) hm)

omit [Fintype T] in
/-- Every retained atom survives the correction unchanged. -/
theorem le_repairedRetainedPlan {p : S → T → ℝ} {rsrc : S → ℝ} {rtgt : T → ℝ}
    (hrsrc : ∀ i, 0 ≤ rsrc i) (hrtgt : ∀ j, 0 ≤ rtgt j) :
    ∀ i j, p i j ≤ repairedRetainedPlan p rsrc rtgt i j := by
  intro i j
  have hm : 0 ≤ ∑ k, rsrc k := Finset.sum_nonneg fun k _ => hrsrc k
  exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (hrsrc i) (hrtgt j)) hm)

/-- The total mass of the corrected plan is the retained mass plus the common
residual port mass; no mass is created or lost. -/
theorem repairedRetainedPlan_mass {p : S → T → ℝ} {rsrc : S → ℝ} {rtgt : T → ℝ}
    (hrsrc : ∀ i, 0 ≤ rsrc i)
    (hmass : (∑ i, rsrc i) = ∑ j, rtgt j) :
    (∑ i, ∑ j, repairedRetainedPlan p rsrc rtgt i j) =
      (∑ i, ∑ j, p i j) + ∑ i, rsrc i := by
  have hm_nonneg : 0 ≤ ∑ k, rsrc k := Finset.sum_nonneg fun k _ => hrsrc k
  have hmass0 : (∑ i, ∑ j, rsrc i * rtgt j / (∑ k, rsrc k)) = ∑ i, rsrc i := by
    by_cases hm0 : (∑ k, rsrc k) = 0
    · have hzero : ∀ i, rsrc i = 0 := by
        intro i
        have hle : rsrc i ≤ ∑ k, rsrc k :=
          Finset.single_le_sum (fun k _ => hrsrc k) (Finset.mem_univ i)
        rw [hm0] at hle
        exact le_antisymm hle (hrsrc i)
      simp only [hzero, zero_mul, zero_div, Finset.sum_const_zero]
    · have hsum (i : S) : (∑ j, rsrc i * rtgt j / (∑ k, rsrc k)) = rsrc i := by
        have hstep : (∑ j, rsrc i * rtgt j / (∑ k, rsrc k)) =
            rsrc i * (∑ j, rtgt j) / (∑ k, rsrc k) := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
        rw [hstep, ← hmass]
        exact mul_div_cancel_right₀ (rsrc i) hm0
      exact Finset.sum_congr rfl fun i _ => hsum i
  calc (∑ i, ∑ j, repairedRetainedPlan p rsrc rtgt i j)
      = (∑ i, ∑ j, p i j) + ∑ i, ∑ j, rsrc i * rtgt j / (∑ k, rsrc k) := by
        simp only [repairedRetainedPlan, Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, p i j) + ∑ i, rsrc i := by rw [hmass0]

/-- The correction restores the exact full source marginal: at every source
node the corrected row sum is the retained row sum plus the source deficit. -/
theorem repairedRetainedPlan_row_sum
    {p : S → T → ℝ} {rsrc : S → ℝ} {rtgt : T → ℝ} {a : S → ℝ}
    (hrsrc : ∀ i, 0 ≤ rsrc i)
    (hmass : (∑ i, rsrc i) = ∑ j, rtgt j)
    (hrow : ∀ i, (∑ j, p i j) + rsrc i = a i) :
    ∀ i, (∑ j, repairedRetainedPlan p rsrc rtgt i j) = a i := by
  have hsum (i : S) : (∑ j, rsrc i * rtgt j / (∑ k, rsrc k)) = rsrc i := by
    have hstep : (∑ j, rsrc i * rtgt j / (∑ k, rsrc k)) =
        rsrc i * (∑ j, rtgt j) / (∑ k, rsrc k) := by
      rw [← Finset.sum_div, ← Finset.mul_sum]
    rw [hstep, ← hmass]
    by_cases hm0 : (∑ k, rsrc k) = 0
    · have hle : rsrc i ≤ ∑ k, rsrc k :=
        Finset.single_le_sum (fun k _ => hrsrc k) (Finset.mem_univ i)
      rw [hm0] at hle
      rw [hm0]
      simp only [mul_zero, zero_div]
      exact (le_antisymm hle (hrsrc i)).symm
    · exact mul_div_cancel_right₀ (rsrc i) hm0
  intro i
  calc (∑ j, repairedRetainedPlan p rsrc rtgt i j)
      = (∑ j, p i j) + ∑ j, rsrc i * rtgt j / (∑ k, rsrc k) := by
        simp only [repairedRetainedPlan, Finset.sum_add_distrib]
    _ = (∑ j, p i j) + rsrc i := by rw [hsum i]
    _ = a i := hrow i

/-- The correction restores the exact full target marginal: at every target
node the corrected column sum is the retained column sum plus the target
deficit. -/
theorem repairedRetainedPlan_col_sum
    {p : S → T → ℝ} {rsrc : S → ℝ} {rtgt : T → ℝ} {b : T → ℝ}
    (hrtgt : ∀ j, 0 ≤ rtgt j)
    (hmass : (∑ i, rsrc i) = ∑ j, rtgt j)
    (hcol : ∀ j, (∑ i, p i j) + rtgt j = b j) :
    ∀ j, (∑ i, repairedRetainedPlan p rsrc rtgt i j) = b j := by
  have hsum (j : T) : (∑ i, rsrc i * rtgt j / (∑ k, rsrc k)) = rtgt j := by
    have hstep : (∑ i, rsrc i * rtgt j / (∑ k, rsrc k)) =
        (∑ i, rsrc i) * rtgt j / (∑ k, rsrc k) := by
      rw [← Finset.sum_div, ← Finset.sum_mul]
    rw [hstep]
    by_cases hm0 : (∑ k, rsrc k) = 0
    · have hrt : (∑ j, rtgt j) = 0 := by rw [← hmass]; exact hm0
      have hle : rtgt j ≤ ∑ j', rtgt j' :=
        Finset.single_le_sum (fun k _ => hrtgt k) (Finset.mem_univ j)
      rw [hrt] at hle
      rw [hm0]
      simp only [div_zero]
      exact (le_antisymm hle (hrtgt j)).symm
    · exact mul_div_cancel_left₀ (rtgt j) hm0
  intro j
  calc (∑ i, repairedRetainedPlan p rsrc rtgt i j)
      = (∑ i, p i j) + ∑ i, rsrc i * rtgt j / (∑ k, rsrc k) := by
        simp only [repairedRetainedPlan, Finset.sum_add_distrib]
    _ = (∑ i, p i j) + rtgt j := by rw [hsum j]
    _ = b j := hcol j

/-- The corrected plan raises the original cost by at most the explicit
constant `L` times the common residual port mass, whenever the original cost
is bounded by `L` on the whole finite carrier. -/
theorem repairedRetainedPlan_addedCost_le
    {p : S → T → ℝ} {rsrc : S → ℝ} {rtgt : T → ℝ} {cost : S → T → ℝ} {L : ℝ}
    (hrsrc : ∀ i, 0 ≤ rsrc i) (hrtgt : ∀ j, 0 ≤ rtgt j)
    (hmass : (∑ i, rsrc i) = ∑ j, rtgt j)
    (hcost : ∀ i j, cost i j ≤ L) :
    (∑ i, ∑ j, (repairedRetainedPlan p rsrc rtgt i j - p i j) * cost i j) ≤
      L * ∑ i, rsrc i := by
  have hm_nonneg : 0 ≤ ∑ k, rsrc k := Finset.sum_nonneg fun k _ => hrsrc k
  have hmass0 : (∑ i, ∑ j, rsrc i * rtgt j / (∑ k, rsrc k)) = ∑ i, rsrc i := by
    by_cases hm0 : (∑ k, rsrc k) = 0
    · have hzero : ∀ i, rsrc i = 0 := by
        intro i
        have hle : rsrc i ≤ ∑ k, rsrc k :=
          Finset.single_le_sum (fun k _ => hrsrc k) (Finset.mem_univ i)
        rw [hm0] at hle
        exact le_antisymm hle (hrsrc i)
      simp only [hzero, zero_mul, zero_div, Finset.sum_const_zero]
    · have hsum (i : S) : (∑ j, rsrc i * rtgt j / (∑ k, rsrc k)) = rsrc i := by
        have hstep : (∑ j, rsrc i * rtgt j / (∑ k, rsrc k)) =
            rsrc i * (∑ j, rtgt j) / (∑ k, rsrc k) := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
        rw [hstep, ← hmass]
        exact mul_div_cancel_right₀ (rsrc i) hm0
      exact Finset.sum_congr rfl fun i _ => hsum i
  calc (∑ i, ∑ j, (repairedRetainedPlan p rsrc rtgt i j - p i j) * cost i j)
      = ∑ i, ∑ j, (rsrc i * rtgt j / (∑ k, rsrc k)) * cost i j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [repairedRetainedPlan]
        ring
    _ ≤ ∑ i, ∑ j, (rsrc i * rtgt j / (∑ k, rsrc k)) * L := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_left (hcost i j)
          (div_nonneg (mul_nonneg (hrsrc i) (hrtgt j)) hm_nonneg)
    _ = L * ∑ i, ∑ j, rsrc i * rtgt j / (∑ k, rsrc k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = L * ∑ i, rsrc i := by rw [hmass0]

end FiniteCorrectedPlan

end OTSelector.Reconstruction

end
end
