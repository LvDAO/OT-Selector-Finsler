import OTSelector.Geometry.FinslerStationaryPhaseAction
import OTSelector.Geometry.FinslerPhaseActionTube
import OTSelector.Analysis.Calculus.ParameterizedSecondJetLevel
import OTSelector.Geometry.FinslerCalibratedTubeDistanceJet

/-!
# Joint regularity of the original phase action

Independent polynomial coefficients and both elapsed times are retained as
parameters of one and the same initial-state family. Genuine tube-distance C3
regularity pulls back through the smooth inverse and the actual endpoint maps.
Only the reference endpoints must lie in the tube: nearby polynomial jets need
not be calibrated. This is a geometric adapter, not a proof that every original
calibrated endpoint pair already has such a tube-distance C3 neighborhood.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W A M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- C3 of the actual tube-coordinate distance transfers to any C3 endpoint
maps. Only the inverse chart, endpoint membership, and local distance are used. -/
theorem contDiffAt_distance_comp_of_manifoldTube (F : ContinuousFinslerNorm E M)
    {Y : OpenPartialHomeomorph (ℝ × W) M}
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    {q₀ : (ℝ × W) × (ℝ × W)} (ha : q₀.1 ∈ Y.source) (hb : q₀.2 ∈ Y.source)
    (hd : ContDiffAt ℝ 3 (F.tubeCoordinateDistance Y) q₀)
    {f g : A → M} {x₀ : A}
    (hf : ContMDiffAt 𝓘(ℝ, A) 𝓘(ℝ, E) 3 f x₀)
    (hg : ContMDiffAt 𝓘(ℝ, A) 𝓘(ℝ, E) 3 g x₀)
    (hfa : f x₀ = Y q₀.1) (hgb : g x₀ = Y q₀.2) :
    ContDiffAt ℝ 3 (fun x ↦ (F.lengthEDist (f x) (g x)).toReal) x₀ := by
  have hft : f x₀ ∈ Y.target := hfa ▸ Y.map_source ha
  have hgt : g x₀ ∈ Y.target := hgb ▸ Y.map_source hb
  let K : A → (ℝ × W) × (ℝ × W) := fun x ↦ (Y.symm (f x), Y.symm (g x))
  have hK : K x₀ = q₀ := by
    dsimp only [K]
    rw [hfa, hgb, Y.left_inv ha, Y.left_inv hb]
  have hKC : ContDiffAt ℝ 3 K x₀ :=
    (((hi.contMDiffAt (Y.open_target.mem_nhds hft)).of_le (by simp)).comp x₀ hf).contDiffAt
      |>.prodMk ((((hi.contMDiffAt (Y.open_target.mem_nhds hgt)).of_le
        (by simp)).comp x₀ hg).contDiffAt)
  have heq : (fun x ↦ (F.lengthEDist (f x) (g x)).toReal) =ᶠ[𝓝 x₀]
      F.tubeCoordinateDistance Y ∘ K := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds (Y.open_target.mem_nhds hft),
      hg.continuousAt.preimage_mem_nhds (Y.open_target.mem_nhds hgt)] with x hfx hgx
    simp only [Function.comp_apply, tubeCoordinateDistance, K,
      Y.right_inv hfx, Y.right_inv hgx]
  rw [← hK] at hd
  exact (hd.comp x₀ hKC).congr_of_eventuallyEq heq

/-- Independent polynomial jet and elapsed-time parameters, followed by the two
initial slit states. Both endpoints always use the same prescribed family. -/
abbrev PhaseActionParameters (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (ScalarSecondJet E × (ℝ × ℝ)) × ((E × E) × (E × E))

/-- The original phase action, with no freezing of polynomial coefficients or times. -/
def parameterizedPhaseLengthAction (F : ContinuousFinslerNorm E M) (old : M)
    (Phi : (E × E) → ℝ → M) (z : PhaseActionParameters E) : ℝ :=
  F.phaseLengthAction old Phi (scalarSecondJetPolynomial z.1.1)
    z.1.2.1 z.1.2.2 z.2

/-- Original C1 data and a continuous actual Hessian on a compact core give a
compact set of joint polynomial/time parameters and original phase centers.
The same supplied inverse Legendre branch is retained throughout. -/
theorem isCompact_original_phaseAction_parameters
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    {K : Set E} (hK : IsCompact K)
    (hH : ContinuousOn (fderiv ℝ (fderiv ℝ G)) K)
    {T : Set (ℝ × ℝ)} (hT : IsCompact T)
    (eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
    (hlegal : ∀ x ∈ K, (x, fderiv ℝ G x) ∈ eL.target) :
    IsCompact ((fun q : E × (ℝ × ℝ) ↦
      (((q.1, G q.1, fderiv ℝ G q.1, fderiv ℝ (fderiv ℝ G) q.1), q.2),
        (eL.symm (q.1, fderiv ℝ G q.1), eL.symm (q.1, fderiv ℝ G q.1)))) ''
      (K ×ˢ T)) := by
  have hDG : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  have hjet : ContinuousOn
      (fun x ↦ (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)) K :=
    continuousOn_id.prodMk (hG.continuous.continuousOn.prodMk
      (hDG.continuousOn.prodMk hH))
  have hphase : ContinuousOn (fun x ↦ eL.symm (x, fderiv ℝ G x)) K :=
    eL.continuousOn_symm.comp (continuousOn_id.prodMk hDG.continuousOn) hlegal
  have hfst : MapsTo (Prod.fst : E × (ℝ × ℝ) → E) (K ×ˢ T) K :=
    fun _ hq ↦ hq.1
  have hjoint := (hjet.comp continuousOn_fst hfst).prodMk continuousOn_snd
  have hz := hphase.comp continuousOn_fst hfst
  exact (hK.prod hT).image_of_continuousOn (hjoint.prodMk (hz.prodMk hz))

namespace IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ E] in
/-- Joint C3 regularity of the same actual phase action follows from the smooth
all-slit tangent flow and genuine C3 distance in one tube around the reference
endpoint pair. No calibration of the neighboring independent jets is required. -/
theorem contDiffAt_parameterizedPhaseLengthAction_of_manifoldTube
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {Phi : (E × E) → ℝ → M}
    (hPhi : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z₀ : PhaseActionParameters E}
    (hz₁ : z₀.2.1 ∈ chartEnergyDomain old)
    (hz₂ : z₀.2.2 ∈ chartEnergyDomain old)
    {Y : OpenPartialHomeomorph (ℝ × W) M}
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    {q₀ : (ℝ × W) × (ℝ × W)} (ha : q₀.1 ∈ Y.source) (hb : q₀.2 ∈ Y.source)
    (hfa : Phi z₀.2.1 z₀.1.2.1 = Y q₀.1)
    (hgb : Phi z₀.2.2 z₀.1.2.2 = Y q₀.2)
    (hd : ContDiffAt ℝ 3 (F.tubeCoordinateDistance Y) q₀) :
    ContDiffAt ℝ 3 (F.parameterizedPhaseLengthAction old Phi) z₀ := by
  have hpos : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) ∞
      (fun q ↦ Phi q.1 q.2) (chartEnergyDomain old ×ˢ univ) := by
    intro q hq
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (hPhi q hq)).1
  have hposAt (z : E × E) (hz : z ∈ chartEnergyDomain old) (t : ℝ) :
      ContMDiffAt 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) 3
        (fun q ↦ Phi q.1 q.2) (z, t) :=
    (hpos.contMDiffAt (((isOpen_chartEnergyDomain old).prod isOpen_univ).mem_nhds
      (show (z, t) ∈ chartEnergyDomain old ×ˢ univ from ⟨hz, mem_univ _⟩))).of_le
        (by simp)
  have harg₁ : ContDiffAt ℝ 3
      (fun z : PhaseActionParameters E ↦ (z.2.1, z.1.2.1)) z₀ :=
    contDiffAt_snd.fst.prodMk contDiffAt_fst.snd.fst
  have harg₂ : ContDiffAt ℝ 3
      (fun z : PhaseActionParameters E ↦ (z.2.2, z.1.2.2)) z₀ :=
    contDiffAt_snd.snd.prodMk contDiffAt_fst.snd.snd
  have hf : ContMDiffAt 𝓘(ℝ, PhaseActionParameters E) 𝓘(ℝ, E) 3
      (fun z ↦ Phi z.2.1 z.1.2.1) z₀ :=
    (hposAt _ hz₁ _).comp z₀
      harg₁.contMDiffAt
  have hg : ContMDiffAt 𝓘(ℝ, PhaseActionParameters E) 𝓘(ℝ, E) 3
      (fun z ↦ Phi z.2.2 z.1.2.2) z₀ :=
    (hposAt _ hz₂ _).comp z₀
      harg₂.contMDiffAt
  have hdist := F.contDiffAt_distance_comp_of_manifoldTube hi ha hb hd hf hg hfa hgb
  have hpa : ContDiffAt ℝ 3
      (fun z : PhaseActionParameters E ↦ scalarSecondJetPolynomial z.1.1 z.2.1.1) z₀ :=
    (contDiff_scalarSecondJetPolynomial_joint.contDiffAt.of_le (by simp)).comp z₀
      (contDiffAt_fst.fst.prodMk contDiffAt_snd.fst.fst)
  have hpb : ContDiffAt ℝ 3
      (fun z : PhaseActionParameters E ↦ scalarSecondJetPolynomial z.1.1 z.2.2.1) z₀ :=
    (contDiff_scalarSecondJetPolynomial_joint.contDiffAt.of_le (by simp)).comp z₀
      (contDiffAt_fst.fst.prodMk contDiffAt_snd.snd.fst)
  have hlength (z : E × E) (hz : z ∈ chartEnergyDomain old) :
      ContDiffAt ℝ 3 (fun q : E × E ↦ (F.chartLength old q : ℝ)) z :=
    ((hF.contDiffOn_chartLength old).contDiffAt
      ((isOpen_chartEnergyDomain old).mem_nhds hz)).of_le (by simp)
  have hs₁ : ContDiffAt ℝ 3
      (fun z : PhaseActionParameters E ↦ (F.chartLength old z.2.1 : ℝ)) z₀ :=
    (hlength _ hz₁).comp z₀
      (f := fun z : PhaseActionParameters E ↦ z.2.1) contDiffAt_snd.fst
  have hs₂ : ContDiffAt ℝ 3
      (fun z : PhaseActionParameters E ↦ (F.chartLength old z.2.2 : ℝ)) z₀ :=
    (hlength _ hz₂).comp z₀
      (f := fun z : PhaseActionParameters E ↦ z.2.2) contDiffAt_snd.snd
  exact (((hdist.sub hpb).add hpa).sub (contDiffAt_fst.snd.snd.mul hs₂)).add
    (contDiffAt_fst.snd.fst.mul hs₁)


/-- A calibrated tube for the reference curve supplies the distance regularity
internally. The independent neighboring jets still use the same all-slit `Phi`;
no tube or calibration is requested for those neighboring jets. -/
theorem contDiffAt_parameterizedPhaseLengthAction_of_calibrated_curve
    [FiniteDimensional ℝ W] [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {Phi : (E × E) → ℝ → M}
    (hPhi : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {j : ScalarSecondJet E} {z : E × E} (hz : z ∈ chartEnergyDomain old)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ))
    {a b : ℝ} (hab : a < b) {w : W}
    (hΛ : F.IsEulerLagrangeOn (Λ w) univ)
    (hsame : Phi z = Λ w)
    (hstay : ∀ t ∈ Icc a b, (t, w) ∈ Y.source)
    (hmin : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Λ w a) (Λ w b) = Manifold.pathELength 𝓘(ℝ, E) (Λ w) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Λ w b) - u (Λ w a) = dist (Λ w a) (Λ w b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Λ w a)) :
    ContDiffAt ℝ 3 (F.parameterizedPhaseLengthAction old Phi) ((j, (a, b)), (z, z)) := by
  have hd := hF.tubeCoordinateDistance_jet_of_calibrated_curve hcomplete hY hi heq
    hhalf t₀ hbound hab hΛ hstay hmin hu hsat hdu
  have hfa : Phi z a = Y (a, w) := by
    rw [heq]
    exact congrFun hsame a
  have hgb : Phi z b = Y (b, w) := by
    rw [heq]
    exact congrFun hsame b
  exact hF.contDiffAt_parameterizedPhaseLengthAction_of_manifoldTube old hPhi hz hz
    hi (hstay a (left_mem_Icc.mpr hab.le)) (hstay b (right_mem_Icc.mpr hab.le))
    hfa hgb (hd.1.of_le (by simp))

omit [FiniteDimensional ℝ E] in
/-- At a unit-energy inverse state, the actual jet polynomial already has the
original length covector. This supplies the match used by stationary phase action. -/
theorem scalarSecondJetPolynomial_matches_unit_inverse_length_covector
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    {j : ScalarSecondJet E} (hp : (j.1, j.2.2.1) ∈ eL.target)
    (henergy : F.chartEnergy old (eL.symm (j.1, j.2.2.1)) = 1 / 2) :
    fderiv ℝ (scalarSecondJetPolynomial j) (eL.symm (j.1, j.2.2.1)).1 =
      fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) (eL.symm (j.1, j.2.2.1)) := by
  have hz := hsource (eL.map_target hp)
  have hf := (parametricLegendre_inverse_components heL hp).1
  have hp' : fiberLegendre (F.chartEnergy old) (eL.symm (j.1, j.2.2.1)) = j.2.2.1 :=
    (parametricLegendre_inverse_components heL hp).2
  have hunit : (F.chartLength old (eL.symm (j.1, j.2.2.1)) : ℝ) = 1 := by
    rw [F.chartLength_eq_sqrt_energy, henergy]
    norm_num
  rw [hf, (hasFDerivAt_scalarSecondJetPolynomial_center j).fderiv]
  exact hp'.symm.trans (by
    simpa only [fiberLegendre, hunit, one_smul] using
      hF.chartLegendre_eq_length_smul_fderiv old hz)

/-- The same calibrated reference tube gives joint C3 action regularity and the
zero derivative of its frozen initial-state action. The supplied explicit jet
polynomial has its length covector matched at the central state. -/
theorem parameterizedPhaseLengthAction_jet_of_calibrated_curve
    [FiniteDimensional ℝ W] [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hPhi : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {j : ScalarSecondJet E} {z : E × E} (hz : z ∈ chartEnergyDomain old)
    (hmatch : fderiv ℝ (scalarSecondJetPolynomial j) z.1 =
      fiberLegendre (fun q ↦ (F.chartLength old q : ℝ)) z)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ))
    {a b : ℝ} (hab : a < b) {w : W}
    (hΛ : F.IsEulerLagrangeOn (Λ w) univ)
    (hsame : Phi z = Λ w)
    (hstay : ∀ t ∈ Icc a b, (t, w) ∈ Y.source)
    (hmin : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Λ w a) (Λ w b) = Manifold.pathELength 𝓘(ℝ, E) (Λ w) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Λ w b) - u (Λ w a) = dist (Λ w a) (Λ w b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Λ w a)) :
    ContDiffAt ℝ 3 (F.parameterizedPhaseLengthAction old Phi) ((j, (a, b)), (z, z)) ∧
      HasFDerivAt (F.phaseLengthAction old Phi (scalarSecondJetPolynomial j) a b)
        (0 : ((E × E) × (E × E)) →L[ℝ] ℝ) (z, z) := by
  have hd := hF.tubeCoordinateDistance_jet_of_calibrated_curve hcomplete hY hi heq
    hhalf t₀ hbound hab hΛ hstay hmin hu hsat hdu
  have ha := hstay a (left_mem_Icc.mpr hab.le)
  have hb := hstay b (right_mem_Icc.mpr hab.le)
  have hfa : Phi z a = Y (a, w) := by
    rw [heq]
    exact congrFun hsame a
  have hgb : Phi z b = Y (b, w) := by
    rw [heq]
    exact congrFun hsame b
  have hP : ContDiffAt ℝ 2 (scalarSecondJetPolynomial j) z.1 :=
    (contDiff_secondJetPolynomial j.1 j.2.1 j.2.2.1 j.2.2.2).contDiffAt.of_le (by simp)
  exact ⟨hF.contDiffAt_parameterizedPhaseLengthAction_of_manifoldTube old hPhi hz hz
      hi ha hb hfa hgb (hd.1.of_le (by simp)),
    (hF.stationary_phaseLengthAction_of_manifoldTube old hEL hinit
      (hPhi.of_le (by simp)) hz hP hmatch hY hi heq ha hb hsame
      (hd.1.of_le (by simp)) hd.2.2).2⟩

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
