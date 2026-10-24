import OTSelector.Geometry.FinslerCalibratedTubeData
import OTSelector.Geometry.FinslerPolynomialCoefficientIdentification
import OTSelector.Geometry.Finsler.CompleteTangentSmooth

/-!
# Geometric data for the actual polynomial phase family

The family uses the original inverse Legendre branch and its explicit unit-speed
normalization. A calibrated tube for this exact family supplies joint action
regularity, stationarity, and the integrated length-Hessian quadratic coefficient.
-/

open Set Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The prescribed flow from the actual normalized polynomial covector on its
selected level section, retaining the same inverse branch and time parameter. -/
def polynomialPhaseFamily (F : ContinuousFinslerNorm E M) (old : M)
    (Φ : (E × E) → ℝ → M)
    (eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
    (σ : ScalarSecondJet E × W → E) (j : ScalarSecondJet E)
    (w : W) (t : ℝ) : M :=
  Φ (F.covectorNormalization old eL (1 / 2)
    (σ (j, w), fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, w)))) t

namespace IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- A calibrated tube of the actual normalized polynomial family supplies its
joint C3 action, frozen stationarity, and actual integrated length coefficient. -/
theorem polynomialPhase_data_of_calibratedTube
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {x : E}
    (hlegal : (x, fderiv ℝ G x) ∈ eL.target)
    (henergy : F.chartEnergy old (eL.symm (x, fderiv ℝ G x)) = 1 / 2)
    {O : Set (ScalarSecondJet E)} {B : Set W}
    (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : W) ∈ B)
    (hj : (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) ∈ O)
    {σ : ScalarSecondJet E × W → E} (hσ : ContDiffOn ℝ 1 σ (O ×ˢ B))
    (hσ₀ : ∀ j ∈ O, σ (j, 0) = j.1)
    (hσlevel : ∀ j ∈ O, ∀ w ∈ B,
      scalarSecondJetPolynomial j (σ (j, w)) = j.2.1)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a b : ℝ}
    (D : F.CalibratedTube (F.polynomialPhaseFamily old Φ eL σ
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)) a b u) :
    let j : ScalarSecondJet E :=
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    let z := eL.symm (x, fderiv ℝ G x)
    ContDiffAt ℝ 3 (F.parameterizedPhaseLengthAction old Φ) ((j, (a, b)), (z, z)) ∧
      HasFDerivAt (F.phaseLengthAction old Φ (scalarSecondJetPolynomial j) a b)
        (0 : ((E × E) × (E × E)) →L[ℝ] ℝ) (z, z) ∧
      ∀ w : W × W, F.polynomialPhaseQuadratic old Φ eL σ j (a, b) w =
        D.quadratic w := by
  dsimp only
  have hPhi := (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth old
    (isOpen_chartEnergyDomain old) hEL (ι := id) contDiffOn_id
    (fun _ hz ↦ hz) hinit).1
  let j : ScalarSecondJet E := (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  let z := eL.symm (x, fderiv ℝ G x)
  have hz : z ∈ chartEnergyDomain old := hsource (eL.map_target hlegal)
  have hnormal := ((hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)).2.2 _ hlegal).2.2.2.2 henergy
  have hsame : Φ z = F.polynomialPhaseFamily old Φ eL σ j 0 := by
    change Φ z = Φ (F.covectorNormalization old eL (1 / 2)
      (σ (j, 0), fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, 0))))
    rw [hσ₀ j hj, (hasFDerivAt_scalarSecondJetPolynomial_center j).fderiv]
    exact (congrArg Φ hnormal).symm
  have hΛ : F.IsEulerLagrangeOn (F.polynomialPhaseFamily old Φ eL σ j 0) univ := by
    rw [← hsame]
    exact hEL z hz
  have hmatch := hF.scalarSecondJetPolynomial_matches_unit_inverse_length_covector
    old heL hsource (j := j) hlegal henergy
  have hjet := hF.parameterizedPhaseLengthAction_jet_of_calibrated_curve
    hcomplete old hEL hinit hPhi hz hmatch D.smooth D.smooth_symm D.coe_eq
    D.energy_eq D.timeOrigin D.covector_le D.ordered hΛ hsame D.stay D.minimizing
    hu D.saturation D.differentiable
  refine ⟨hjet.1, hjet.2, ?_⟩
  intro w
  exact hF.polynomialPhaseQuadratic_eq_tubeLengthQuadratic hcomplete old
    heL hsource hInv hG hlegal henergy hO hB h0B hj hσ hσ₀ hσlevel hEL hinit hPhi
    (fun _ _ ↦ rfl) D.smooth D.smooth_symm D.coe_eq D.energy_eq D.timeOrigin
    D.covector_le D.ordered D.stay D.minimizing hu D.saturation D.differentiable w

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
