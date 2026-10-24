import OTSelector.Geometry.FinslerCalibratedTubeFromClock
import OTSelector.Geometry.FinslerPolynomialTubeData
import OTSelector.Geometry.Finsler.OriginalCoreClock

/-!
# Polynomial tube calibration from the original core

The actual original covector and two calibrated partners determine the central
unit-speed curve and its clock. Normalization fixes this central state exactly.
Consequently the same polynomial family inherits all central calibration data
from the original core; only its smooth tube geometry is supplied separately.
-/

open Set Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Original core calibration completes the data of a smooth polynomial tube,
without separately assuming central energy, speed, clock or endpoint calibration. -/
def polynomialTubeOfOriginalCore (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {C : Set E} (hCt : C ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {G : E → ℝ} (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) C)
    (hactual : ∀ y ∈ C,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : letI : MetricSpace M := F.metricSpace
      ∀ y ∈ C, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u l = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) r = δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ)
    {x : E} (hx : x ∈ C) {σ : ScalarSecondJet E × W → E}
    (hσ₀ : σ ((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), 0) = x)
    {Y : OpenPartialHomeomorph (ℝ × W) M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦
      F.polynomialPhaseFamily old Φ eL σ
        (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (F.polynomialPhaseFamily old Φ eL σ
          (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) q.2)
        ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ y ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) y,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) y v)
        (F.toFun ⟨y, v⟩ : ℝ))
    {a b : ℝ} (hab : a < b) (ha : a ∈ Ioo (-δ) δ) (hb : b ∈ Ioo (-δ) δ)
    (hstay : ∀ t ∈ Icc a b, (t, (0 : W)) ∈ Y.source) :
    F.CalibratedTube (F.polynomialPhaseFamily old Φ eL σ
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)) a b u := by
  let j : ScalarSecondJet E := (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  let z := eL.symm (x, fderiv ℝ G x)
  have hz : z ∈ chartEnergyDomain old := hsource (eL.map_target (hlegal x hx))
  have hcore := hF.original_core_unit_energy_and_clock hcomplete old hu
    hCt hval hactual hEL hinit heL hsource hlegal hδ hpartners x hx
  have hnormal := ((hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)).2.2 _ (hlegal x hx)).2.2.2.2 hcore.2.1
  have hcentral : F.polynomialPhaseFamily old Φ eL σ
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) 0 = Φ z := by
    funext t
    change Φ (F.covectorNormalization old eL (1 / 2)
      (σ (j, 0), fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, 0)))) t = Φ z t
    rw [hσ₀, (hasFDerivAt_scalarSecondJetPolynomial_center j).fderiv, hnormal]
  have hunit : ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨t, (1 : ℝ)⟩) = 1 := by
    intro t
    rw [hF.speed_eq_of_isEulerLagrangeOn (hEL z hz) isPreconnected_univ
      (mem_univ t) (mem_univ 0), hinit z hz]
    change F.chartLength old z = 1
    exact_mod_cast hcore.1
  apply hF.calibratedTubeOfClock (c := G x) hcomplete hu hY hi heq hhalf t₀ hbound hab hstay
    (by simpa only [hcentral] using hEL z hz)
    (by simpa only [hcentral] using hunit) hδ ha hb
  simpa only [hcentral] using hcore.2.2

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
