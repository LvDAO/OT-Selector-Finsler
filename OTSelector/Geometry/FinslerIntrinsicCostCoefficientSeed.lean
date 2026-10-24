import OTSelector.Geometry.FinslerIntrinsicCostCoefficientFlow
import OTSelector.Geometry.FinslerPolynomialFamilyJet

/-!
# The original seed and the normalized polynomial seed have the same intrinsic kernel

The calibrated original core fixes the polynomial normalization's first jet.
The true inverse Legendre branch then gives matching tangent seeds, so the same
prescribed flow produces exactly the original intrinsic label Hessian at all times.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle Module
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Original core calibration identifies the normalized polynomial tangent jet
with the unnormalized actual potential tangent seed in the same labels. -/
theorem polynomial_tangent_seed_same_firstJet_of_core
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [IsAddHaarMeasure m]
    {C : Set E} (hCt : C ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinterior : letI : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm C
        (OTSelector.Geometry.calibratedInterior u))
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    (hactual : ∀ y ∈ C,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {x : E} (hxC : x ∈ C)
    (hdensity : Tendsto (fun r ↦ m (C ∩ closedBall x r) / m (closedBall x r))
      (𝓝[>] 0) (𝓝 1))
    (hsecond : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    (hlegal : (x, fderiv ℝ G x) ∈ eL.target)
    (henergy : F.chartEnergy old (eL.symm (x, fderiv ℝ G x)) = 1 / 2)
    {O : Set (ScalarSecondJet E)} {B : Set W}
    (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : W) ∈ B)
    (hj : (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) ∈ O)
    {σ : ScalarSecondJet E × W → E} (hσ : ContDiffOn ℝ 1 σ (O ×ˢ B))
    (hσ₀ : σ ((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), 0) = x)
    {ρ : W → E}
    (hρ : HasFDerivAt ρ
      (fderiv ℝ (fun w ↦ σ ((x, G x, fderiv ℝ G x,
        fderiv ℝ (fderiv ℝ G) x), w)) 0) 0)
    (hρ₀ : ρ 0 = x)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) :
    let j : ScalarSecondJet E :=
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    let N : W → E × E := fun w ↦ F.covectorNormalization old eL (1 / 2)
      (σ (j, w), fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, w)))
    let X : W → E × E := fun w ↦ eL.symm (ρ w, fderiv ℝ G (ρ w))
    N 0 = X 0 ∧ N 0 ∈ chartEnergyDomain old ∧
      ∃ D : W →L[ℝ] E × E, HasFDerivAt N D 0 ∧ HasFDerivAt X D 0 := by
  let j : ScalarSecondJet E :=
    (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  let s : W → E := fun w ↦ σ (j, w)
  let q : W → E × (E →L[ℝ] ℝ) := fun w ↦
    (s w, fderiv ℝ (scalarSecondJetPolynomial j) (s w))
  let N : W → E × E := fun w ↦ F.covectorNormalization old eL (1 / 2) (q w)
  let Γ := F.polynomialPhaseFamily old Φ eL σ j
  have hq₀ : q 0 = (x, fderiv ℝ G x) := by
    change (s 0, fderiv ℝ (scalarSecondJetPolynomial j) (s 0)) = _
    rw [show s 0 = x from hσ₀]
    exact Prod.ext rfl (hasFDerivAt_scalarSecondJetPolynomial_center j).fderiv
  have hs : ContDiffAt ℝ 1 s 0 :=
    (hσ.contDiffAt ((hO.prod hB).mem_nhds ⟨hj, h0B⟩)).comp 0
      (contDiffAt_const.prodMk contDiffAt_id)
  have hP : ContDiff ℝ ∞ (scalarSecondJetPolynomial j) :=
    contDiff_scalarSecondJetPolynomial_joint.comp (contDiff_const.prodMk contDiff_id)
  have hq : ContinuousAt q 0 :=
    hs.continuousAt.prodMk ((hP.fderiv_right (m := ∞) (by simp)).continuous.continuousAt.comp hs.continuousAt)
  have hqlegal : q 0 ∈ eL.target := by rw [hq₀]; exact hlegal
  obtain ⟨_, hNdiff, hNspec⟩ := hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hN : ContinuousAt N 0 :=
    (hNdiff.contDiffAt (eL.open_target.mem_nhds hqlegal)).continuousAt.comp hq
  have hN₀ : N 0 = eL.symm (x, fderiv ℝ G x) := by
    change F.covectorNormalization old eL (1 / 2) (q 0) = _
    rw [hq₀]
    exact (hNspec _ hlegal).2.2.2.2 henergy
  have hNsource : N 0 ∈ eL.source := by rw [hN₀]; exact eL.map_target hlegal
  have hnear : ∀ᶠ w in 𝓝 (0 : W), N w ∈ eL.source :=
    hN (eL.open_source.mem_nhds hNsource)
  obtain ⟨hvalue, hphase⟩ :=
    hF.polynomialPhaseFamily_initial_firstJet_of_calibrated_core hcomplete old m
      hCt hu hinterior hG hactual hxC hdensity hsecond heL hsource hInv hlegal henergy
      hO hB h0B hj hσ hσ₀ hEL hinit
  let R := fderiv ℝ s 0
  let P := R.prod ((fderiv ℝ (fderiv ℝ G) x).comp R)
  let A := fderiv ℝ eL.symm (x, fderiv ℝ G x)
  have hE : HasFDerivAt eL.symm A (x, fderiv ℝ G x) :=
    ((hInv.contDiffAt (eL.open_target.mem_nhds hlegal)).differentiableAt (by simp)).hasFDerivAt
  have hEΓ : HasFDerivAt eL.symm A (F.chartMomentumFamily old Γ (0, 0)) := by
    rw [hvalue]
    exact hE
  have hNjet : HasFDerivAt N (A.comp P) 0 := by
    apply (HasFDerivAt.comp (f := fun w : W ↦ F.chartMomentumFamily old Γ (w, 0))
      (g := eL.symm) 0 hEΓ hphase).congr_of_eventuallyEq
    filter_upwards [hnear] with w hw
    have hz : N w ∈ chartEnergyDomain old := hsource hw
    have heq : F.chartMomentumFamily old Γ (w, 0) = eL (N w) := by
      rw [heL]
      exact hF.chartMomentum_of_tangent_eq (hEL _ hz 0 (mem_univ _)) old hz (hinit _ hz)
    change N w = eL.symm (F.chartMomentumFamily old Γ (w, 0))
    rw [heq, eL.left_inv hw]
  have hsecondρ : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) (ρ 0) := by
    rwa [hρ₀]
  have hrough : HasFDerivAt (fun w ↦ (ρ w, fderiv ℝ G (ρ w))) P 0 :=
    hρ.prodMk (hsecondρ.comp 0 hρ)
  have hEρ : HasFDerivAt eL.symm A (ρ 0, fderiv ℝ G (ρ 0)) := by
    rw [hρ₀]
    exact hE
  exact ⟨by dsimp only; rw [hρ₀]; exact hN₀,
    hsource hNsource, A.comp P, hNjet, hEρ.comp 0 hrough⟩

variable [Fintype ι] [DecidableEq ι]

/-- The polynomial comparison and the original potential family have the same
intrinsic Hessian and the same integrated coefficient in their unchanged labels. -/
theorem polynomial_intrinsic_data_eq_original_of_core
    (hF : F.IsSmoothStronglyConvex) (bW : Basis ι ℝ W)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [IsAddHaarMeasure m]
    {C : Set E} (hCt : C ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinterior : letI : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm C
        (OTSelector.Geometry.calibratedInterior u))
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    (hactual : ∀ y ∈ C,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {x : E} (hxC : x ∈ C)
    (hdensity : Tendsto (fun r ↦ m (C ∩ closedBall x r) / m (closedBall x r))
      (𝓝[>] 0) (𝓝 1))
    (hsecond : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    (hlegal : (x, fderiv ℝ G x) ∈ eL.target)
    (henergy : F.chartEnergy old (eL.symm (x, fderiv ℝ G x)) = 1 / 2)
    {O : Set (ScalarSecondJet E)} {B : Set W}
    (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : W) ∈ B)
    (hj : (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) ∈ O)
    {σ : ScalarSecondJet E × W → E} (hσ : ContDiffOn ℝ 1 σ (O ×ˢ B))
    (hσ₀ : σ ((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), 0) = x)
    {ρ : W → E}
    (hρ : HasFDerivAt ρ
      (fderiv ℝ (fun w ↦ σ ((x, G x, fderiv ℝ G x,
        fderiv ℝ (fderiv ℝ G) x), w)) 0) 0)
    (hρ₀ : ρ 0 = x)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) :
    let j : ScalarSecondJet E :=
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    let X : W → E × E := fun w ↦ eL.symm (ρ w, fderiv ℝ G (ρ w))
    (∀ t : ℝ,
      F.familyLabelHessianMatrix bW
        (fun q ↦ F.polynomialPhaseFamily old Φ eL σ j q.1 q.2) (0, t) =
      F.familyLabelHessianMatrix bW (fun q ↦ Φ (X q.1) q.2) (0, t)) ∧
    ∀ (a b : ℝ) (w : W × W),
      F.intrinsicLengthQuadratic bW (F.polynomialPhaseFamily old Φ eL σ j) 0 a b w =
      F.intrinsicLengthQuadratic bW (fun z t ↦ Φ (X z) t) 0 a b w := by
  obtain ⟨hvalue, hlegalN, D, hN, hX⟩ :=
    hF.polynomial_tangent_seed_same_firstJet_of_core hcomplete old m hCt hu hinterior
      hG hactual hxC hdensity hsecond heL hsource hInv hlegal henergy
      hO hB h0B hj hσ hσ₀ hρ hρ₀ hEL hinit
  exact ⟨fun t ↦ hF.familyLabelHessianMatrix_complete_seed_eq old bW hEL hinit
    hN hX hvalue hlegalN t,
    fun a b w ↦ hF.intrinsicLengthQuadratic_complete_seed_eq old bW hEL hinit
      hN hX hvalue hlegalN a b w⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
