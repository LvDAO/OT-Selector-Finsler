import OTSelector.Geometry.Finsler.TubeCoordinateCalibratedDistance
import OTSelector.Geometry.Finsler.LengthMomentumVariation
import OTSelector.Analysis.Calculus.Variational.EndpointHessianCalculus
import OTSelector.Geometry.FinslerTubeCoordinateCompliance

/-!
# The original distance Hessian in genuine tube coordinates

The literal tangent pullback retains the original energy homogeneity, length momentum
and radial Hessian identity. Calibration identifies the exact correction from energy
momentum variation to length momentum variation in the actual tube coordinates.
Intrinsic first variation identifies the real endpoint derivative of the original distance.
An actual minimizing endpoint family then gives its full compliance Hessian, including
the radial correction. The minimizing family is an explicit input of this module.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E V W P M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem tubeCoordinateEnergy_smul (F : ContinuousFinslerNorm E M)
    (Y : OpenPartialHomeomorph V M) (q v : V) (r : ℝ) :
    F.tubeCoordinateEnergy Y (q, r • v) = r ^ 2 * F.tubeCoordinateEnergy Y (q, v) := by
  change F.fiberEnergy (Y q) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y q (r • v)) = _
  rw [_root_.map_smul, F.fiberEnergy_smul]
  rfl

/-- The actual tube length covector is the pullback of the original tangent covector. -/
theorem tubeLength_fiberLegendre_eq (F : ContinuousFinslerNorm E M)
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ E]
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {q : V} (hq : q ∈ Y.source) (v : V) :
    fiberLegendre (F.tubeCoordinateLength Y) (q, v) =
      (fderiv ℝ (fun η : TangentSpace 𝓘(ℝ, E) (Y q) ↦
        (F.toFun ⟨Y q, η⟩ : ℝ)) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y q v)).comp
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y q) := by
  let instTubeLengthFiberNorm : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) (Y q)) :=
    inferInstanceAs (NormedAddCommGroup E)
  let instTubeLengthFiberSpace : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) (Y q)) :=
    inferInstanceAs (NormedSpace ℝ E)
  let B : V →L[ℝ] TangentSpace 𝓘(ℝ, E) (Y q) := mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y q
  let A : V ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (Y q) :=
    (LinearEquiv.ofBijective B.toLinearMap
      (mfderiv_tubeCoordinate_bijective hY hi hq)).toContinuousLinearEquiv
  change fderiv ℝ ((fun η : TangentSpace 𝓘(ℝ, E) (Y q) ↦
    (F.toFun ⟨Y q, η⟩ : ℝ)) ∘ A) v = _
  exact A.comp_right_fderiv

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

private theorem tubeLength_fiberLegendre_of_curve [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ E] (F : ContinuousFinslerNorm E M)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {c : ℝ → M} {t : ℝ} (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t)
    (hx : c t ∈ Y.target) :
    fiberLegendre (F.tubeCoordinateLength Y)
      ((Y.symm ∘ c) t, deriv (Y.symm ∘ c) t) =
      (fderiv ℝ (fun η : TangentSpace 𝓘(ℝ, E) (c t) ↦
        (F.toFun ⟨c t, η⟩ : ℝ)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1)).comp
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y (Y.symm (c t))) := by
  have hiC := (hi.contMDiffAt (Y.open_target.mem_nhds hx)).mdifferentiableAt (by simp)
  have hYC := (hY.contMDiffAt (Y.open_source.mem_nhds (Y.map_target hx))).mdifferentiableAt
    (by simp)
  have he : (Y : V → M) ∘ (Y.symm ∘ c) =ᶠ[𝓝 t] c := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds (Y.open_target.mem_nhds hx)] with s hs
    exact Y.right_inv hs
  have hvel : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) Y (Y.symm (c t))
      (deriv (Y.symm ∘ c) t) = mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1 := by
    have h := mfderiv_comp_apply t hYC (hiC.comp t hc) (1 : ℝ)
    rw [he.mfderiv_eq, mfderiv_eq_fderiv] at h
    exact h.symm
  have h := F.tubeLength_fiberLegendre_eq hY hi (Y.map_target hx)
    (deriv (Y.symm ∘ c) t)
  rw [hvel, Y.right_inv hx] at h
  exact h

private theorem tube_endpoint_covector [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ E] (F : ContinuousFinslerNorm E M)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : P → ℝ → M} {p₀ : P} {t : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ p₀) t)
    (A : P →L[ℝ] V) (hA : A p₀ ∈ Y.source)
    (he : (fun p ↦ Γ p t) =ᶠ[𝓝 p₀] (Y : V → M) ∘ A) :
    (fderiv ℝ (fun η : TangentSpace 𝓘(ℝ, E) (Γ p₀ t) ↦
      (F.toFun ⟨Γ p₀ t, η⟩ : ℝ)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ p₀) t 1)).comp
        (mfderiv 𝓘(ℝ, P) 𝓘(ℝ, E) (fun p ↦ Γ p t) p₀) =
      (fiberLegendre (F.tubeCoordinateLength Y)
        (tubeCoordinateTangentFamily Y Γ (p₀, t))).comp A := by
  have hbase : Γ p₀ t = Y (A p₀) := he.eq_of_nhds
  have hx : Γ p₀ t ∈ Y.target := hbase ▸ Y.map_source hA
  have hq : Y.symm (Γ p₀ t) = A p₀ := by rw [hbase, Y.left_inv hA]
  change _ = (fiberLegendre (F.tubeCoordinateLength Y)
    ((Y.symm ∘ Γ p₀) t, deriv (Y.symm ∘ Γ p₀) t)).comp A
  rw [tubeLength_fiberLegendre_of_curve F hY hi hc hx, hq,
    ContinuousLinearMap.comp_assoc]
  congr 1
  rw [he.mfderiv_eq, mfderiv_comp p₀
    ((hY.contMDiffAt (Y.open_source.mem_nhds hA)).mdifferentiableAt (by simp))
    A.hasFDerivAt.hasMFDerivAt.mdifferentiableAt, mfderiv_eq_fderiv, A.fderiv]

private theorem tubeEndpointDistance_hasFDerivAt_of_branch [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ W] (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph (ℝ × W) M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    {Γ : ((ℝ × W) × (ℝ × W)) → ℝ → M} {B : Set ((ℝ × W) × (ℝ × W))}
    (hB : IsOpen B) (hBY : B ⊆ Y.source ×ˢ Y.source)
    (hEL : ∀ q ∈ B, F.IsEulerLagrangeOn (Γ q) univ)
    (hG : ContMDiffOn 𝓘(ℝ, ((ℝ × W) × (ℝ × W)) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun r ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ r.1) ⟨r.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {a b : ℝ} (hab : a ≤ b)
    (hend : ∀ q ∈ B, Γ q a = Y q.1 ∧ Γ q b = Y q.2)
    (hbranch : let _instTubeGradientENorm : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) :=
        F.enorm
      ∀ q ∈ B, F.lengthEDist (Y q.1) (Y q.2) = pathELength 𝓘(ℝ, E) (Γ q) a b)
    {q₀ : (ℝ × W) × (ℝ × W)} (hq : q₀ ∈ B) :
    HasFDerivAt (F.tubeCoordinateDistance Y)
      ((fiberLegendre (F.tubeCoordinateLength Y)
        (tubeCoordinateTangentFamily Y Γ (q₀, b))).comp
          (ContinuousLinearMap.snd ℝ (ℝ × W) (ℝ × W)) -
       (fiberLegendre (F.tubeCoordinateLength Y)
        (tubeCoordinateTangentFamily Y Γ (q₀, a))).comp
          (ContinuousLinearMap.fst ℝ (ℝ × W) (ℝ × W))) q₀ := by
  let instTubeGradientProofENorm : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  have hd := hF.hasFDerivAt_family_pathELength_mfderiv_across_charts
    hB isOpen_univ hG hq hab (subset_univ _) (hEL q₀ hq)
  have ha : (fun q ↦ Γ q a) =ᶠ[𝓝 q₀]
      (Y : ℝ × W → M) ∘ ContinuousLinearMap.fst ℝ (ℝ × W) (ℝ × W) := by
    filter_upwards [hB.mem_nhds hq] with q hq'
    exact (hend q hq').1
  have hb : (fun q ↦ Γ q b) =ᶠ[𝓝 q₀]
      (Y : ℝ × W → M) ∘ ContinuousLinearMap.snd ℝ (ℝ × W) (ℝ × W) := by
    filter_upwards [hB.mem_nhds hq] with q hq'
    exact (hend q hq').2
  have hca := (hF.contMDiffAt_of_isEulerLagrangeAt
    (hEL q₀ hq a (mem_univ _))).mdifferentiableAt (by simp)
  have hcb := (hF.contMDiffAt_of_isEulerLagrangeAt
    (hEL q₀ hq b (mem_univ _))).mdifferentiableAt (by simp)
  dsimp only at hd
  rw [tube_endpoint_covector F hY hi hca _ (hBY hq).1 ha,
    tube_endpoint_covector F hY hi hcb _ (hBY hq).2 hb] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hB.mem_nhds hq] with q hq'
  exact congrArg ENNReal.toReal (hbranch q hq')

private theorem tubeLegendre_eq_length_smul_fderiv (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {z : V × V} (hz : z ∈ Y.source ×ˢ {v : V | v ≠ 0}) :
    fiberLegendre (F.tubeCoordinateEnergy Y) z = F.tubeCoordinateLength Y z •
      fiberLegendre (F.tubeCoordinateLength Y) z := by
  have hc := (hF.contDiffOn_tubeCoordinateLength Y hY hi).contDiffAt
    ((Y.open_source.prod isOpen_ne).mem_nhds hz)
  have hd : DifferentiableAt ℝ (fun v ↦ F.tubeCoordinateLength Y (z.1, v)) z.2 :=
    (hc.comp z.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  change fderiv ℝ (fun v ↦ F.tubeCoordinateEnergy Y (z.1, v)) z.2 = _
  simp only [F.tubeCoordinateEnergy_eq_half_sq]
  have hh := (hd.hasFDerivAt.pow 2).const_smul (1 / 2 : ℝ)
  convert! hh.fderiv using 1
  · congr 1
    funext v
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · ext v
    simp [fiberLegendre]
    ring

/-- Actual length momentum variation at unit speed has its genuine speed correction. -/
theorem tubeLengthMomentum_parameter_fderiv_of_unit (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Z : P → V × V} {p₀ : P} (hZ : DifferentiableAt ℝ Z p₀)
    (hz : Z p₀ ∈ Y.source ×ˢ {v : V | v ≠ 0})
    (hs : F.tubeCoordinateLength Y (Z p₀) = 1) (u : P) :
    fderiv ℝ (fiberLegendre (F.tubeCoordinateLength Y) ∘ Z) p₀ u =
      fderiv ℝ (fiberLegendre (F.tubeCoordinateEnergy Y) ∘ Z) p₀ u -
        (fderiv ℝ (F.tubeCoordinateLength Y ∘ Z) p₀ u) •
          fiberLegendre (F.tubeCoordinateEnergy Y) (Z p₀) := by
  have hL := (hF.contDiffOn_tubeCoordinateLength Y hY hi).contDiffAt
    ((Y.open_source.prod isOpen_ne).mem_nhds hz)
  apply fderiv_normalized_covector_of_unit
    ((hL.differentiableAt (by simp)).comp p₀ hZ)
    (((contDiffAt_fiberLegendre hL).differentiableAt (by simp)).comp p₀ hZ) _ hs
  filter_upwards [hZ.continuousAt.preimage_mem_nhds
    ((Y.open_source.prod isOpen_ne).mem_nhds hz)] with p hp
  exact hF.tubeLegendre_eq_length_smul_fderiv hY hi hp

private theorem tubeEnergy_verticalHessian_symm (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {z : V × V} (hz : z ∈ Y.source ×ˢ {v : V | v ≠ 0}) (u v : V) :
    verticalEnergyHessian (F.tubeCoordinateEnergy Y) z u v =
      verticalEnergyHessian (F.tubeCoordinateEnergy Y) z v u := by
  have hL := (hF.contDiffOn_tubeCoordinateEnergy Y hY hi).contDiffAt
    ((Y.open_source.prod isOpen_ne).mem_nhds hz)
  have hf : ContDiffAt ℝ ∞ (fun w ↦ F.tubeCoordinateEnergy Y (z.1, w)) z.2 := by
    simpa only [Function.comp_def] using!
      hL.comp z.2 (contDiffAt_const.prodMk (contDiffAt_id (x := z.2)))
  exact hf.isSymmSndFDerivAt (by simp) u v

private theorem tubeEnergy_hessian_radial (hF : F.IsSmoothStronglyConvex)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {z : V × V} (hz : z ∈ Y.source ×ˢ {v : V | v ≠ 0}) :
    verticalEnergyHessian (F.tubeCoordinateEnergy Y) z z.2 =
      fiberLegendre (F.tubeCoordinateEnergy Y) z := by
  have hc (v : V) (hv : v ≠ 0) :
      ContDiffAt ℝ ∞ (fun w ↦ F.tubeCoordinateEnergy Y (z.1, w)) v := by
    have h := (hF.contDiffOn_tubeCoordinateEnergy Y hY hi).contDiffAt
      ((Y.open_source.prod isOpen_ne).mem_nhds
        (show (z.1, v) ∈ Y.source ×ˢ {v : V | v ≠ 0} from ⟨hz.1, hv⟩))
    simpa only [Function.comp_def] using!
      h.comp v (contDiffAt_const.prodMk (contDiffAt_id (x := v)))
  exact twoHomogeneous_fderiv2_radial
    (fun r _ v ↦ F.tubeCoordinateEnergy_smul Y z.1 v r)
    (fun v hv ↦ (hc v hv).differentiableAt (by simp)) hz.2
    (((hc z.2 hz.2).fderiv_right (m := 1) (by simp)).differentiableAt_one)

/-- The literal tube inverse fiber Hessian retains the actual radial pairing. -/
theorem tubeEnergy_inverseHessian_radial_pairing [FiniteDimensional ℝ V]
    (hF : F.IsSmoothStronglyConvex) {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {z : V × V} (hz : z ∈ Y.source ×ˢ {v : V | v ≠ 0}) (p : V →L[ℝ] ℝ) :
    fiberLegendre (F.tubeCoordinateEnergy Y) z
      (ContinuousLinearMap.inverse (verticalEnergyHessian (F.tubeCoordinateEnergy Y) z) p) =
        p z.2 := by
  let d := positive_dualMap_equiv (verticalEnergyHessian (F.tubeCoordinateEnergy Y) z)
    (fun v hv ↦ hF.tubeCoordinateEnergy_fiber_hessian_pos hY hi hz.1 hz.2 hv)
  rw [show ContinuousLinearMap.inverse (verticalEnergyHessian (F.tubeCoordinateEnergy Y) z) =
    d.symm.toContinuousLinearMap from ContinuousLinearMap.inverse_equiv d]
  rw [← hF.tubeEnergy_hessian_radial hY hi hz]
  change verticalEnergyHessian (F.tubeCoordinateEnergy Y) z z.2 (d.symm p) = p z.2
  rw [hF.tubeEnergy_verticalHessian_symm hY hi hz]
  exact congrArg (fun q : V →L[ℝ] ℝ ↦ q z.2) (d.apply_symm_apply p)

private theorem tubeSpeed_parameter_fderiv_eq_momentum_radial
    (hF : F.IsSmoothStronglyConvex) (Y : OpenPartialHomeomorph (ℝ × W) M)
    {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target) (t₀ : ℝ)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ))
    {Z : P → (ℝ × W) × (ℝ × W)} {p₀ : P} (hZ : DifferentiableAt ℝ Z p₀)
    (hx : (Z p₀).1 ∈ Y.source) (hv : (Z p₀).2 = (1, 0)) (u : P) :
    fderiv ℝ (F.tubeCoordinateLength Y ∘ Z) p₀ u =
      fderiv ℝ (fiberLegendre (F.tubeCoordinateEnergy Y) ∘ Z) p₀ u (1, 0) := by
  let p := ContinuousLinearMap.fst ℝ ℝ W
  have hz : Z p₀ ∈ Y.source ×ˢ {v : ℝ × W | v ≠ 0} := ⟨hx, by rw [hv]; simp⟩
  have hident := hF.tubeCoordinateEnergy_calibrated_identities Y hY hi t₀ heq hhalf hbound hx
  have hzeq : Z p₀ = ((Z p₀).1, (1, 0)) := Prod.ext rfl hv
  have hL := (hF.contDiffOn_tubeCoordinateEnergy Y hY hi).contDiffAt
    ((Y.open_source.prod isOpen_ne).mem_nhds hz)
  have hG := (hF.contDiffOn_tubeCoordinateLength Y hY hi).contDiffAt
    ((Y.open_source.prod isOpen_ne).mem_nhds hz)
  have hP := (contDiffAt_fiberLegendre hL).differentiableAt (by simp)
  have hsplit := energy_partials_zero_of_hessian_base_zero
    (Y.open_source.prod isOpen_ne) (hF.contDiffOn_tubeCoordinateEnergy Y hY hi) hz
    (by rw [hzeq]; exact hident.2.2.2.2.2.2.1)
  have hmomentum : fiberLegendre (F.tubeCoordinateEnergy Y) (Z p₀) = p := by
    rw [hzeq]; exact hident.2.2.1
  have hfirst : fderiv ℝ (F.tubeCoordinateEnergy Y) (Z p₀) =
      p.comp (ContinuousLinearMap.snd ℝ (ℝ × W) (ℝ × W)) := by
    rw [hzeq]; exact hident.2.2.2.2.2.1
  have hs : F.tubeCoordinateLength Y (Z p₀) = 1 := by
    rw [hzeq]
    exact (F.tubeCoordinate_timeColumn_unit hY heq hhalf hx).2
  have hspeed : fderiv ℝ (F.tubeCoordinateLength Y) (Z p₀) =
      p.comp (ContinuousLinearMap.snd ℝ (ℝ × W) (ℝ × W)) := by
    have h := (((hG.differentiableAt (by simp)).hasFDerivAt.pow 2).const_smul
      (1 / 2 : ℝ)).fderiv
    have he : (fun z ↦ (1 / 2 : ℝ) • F.tubeCoordinateLength Y z ^ 2) =
        F.tubeCoordinateEnergy Y := by
      funext z
      rw [F.tubeCoordinateEnergy_eq_half_sq]
      simp only [smul_eq_mul]
      ring
    change fderiv ℝ (fun z ↦ (1 / 2 : ℝ) • F.tubeCoordinateLength Y z ^ 2)
      (Z p₀) = _ at h
    rw [he, hfirst] at h
    norm_num [hs, smul_smul] at h
    exact h.symm
  have hrad (d : (ℝ × W) × (ℝ × W)) :
      fderiv ℝ (fiberLegendre (F.tubeCoordinateEnergy Y)) (Z p₀) d (1, 0) = p d.2 := by
    have hdecomp : d = (d.1, 0) + (0, d.2) := by ext <;> simp
    rw [hdecomp, map_add, hsplit.2, zero_add]
    have hvertical := congrArg (fun A ↦ A d.2) (fiberLegendre_fderiv_vertical hL)
    change fderiv ℝ (fiberLegendre (F.tubeCoordinateEnergy Y)) (Z p₀) (0, d.2) =
      verticalEnergyHessian (F.tubeCoordinateEnergy Y) (Z p₀) d.2 at hvertical
    rw [hvertical, ← hv, hF.tubeEnergy_verticalHessian_symm hY hi hz,
      hF.tubeEnergy_hessian_radial hY hi hz, hmomentum]
    simp only [Prod.snd_add, zero_add]
  rw [fderiv_comp p₀ (hG.differentiableAt (by simp)) hZ, fderiv_comp p₀ hP hZ]
  exact (congrArg (fun A ↦ A (fderiv ℝ Z p₀ u)) hspeed).trans
    (hrad (fderiv ℝ Z p₀ u)).symm

/-- The calibrated genuine tube determines the exact radial correction to the actual
length momentum variation; no speed differential or Hessian identity is assumed. -/
theorem tubeLengthMomentum_parameter_fderiv_of_calibrated
    (hF : F.IsSmoothStronglyConvex) (Y : OpenPartialHomeomorph (ℝ × W) M)
    {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target) (t₀ : ℝ)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ))
    {Z : P → (ℝ × W) × (ℝ × W)} {p₀ : P} (hZ : DifferentiableAt ℝ Z p₀)
    (hx : (Z p₀).1 ∈ Y.source) (hv : (Z p₀).2 = (1, 0)) (u : P) :
    fderiv ℝ (fiberLegendre (F.tubeCoordinateLength Y) ∘ Z) p₀ u =
      fderiv ℝ (fiberLegendre (F.tubeCoordinateEnergy Y) ∘ Z) p₀ u -
        (fderiv ℝ (fiberLegendre (F.tubeCoordinateEnergy Y) ∘ Z) p₀ u (1, 0)) •
          ContinuousLinearMap.fst ℝ ℝ W := by
  have hz : Z p₀ ∈ Y.source ×ˢ {v : ℝ × W | v ≠ 0} := ⟨hx, by rw [hv]; simp⟩
  have hzeq : Z p₀ = ((Z p₀).1, (1, 0)) := Prod.ext rfl hv
  have hs : F.tubeCoordinateLength Y (Z p₀) = 1 := by
    rw [hzeq]
    exact (F.tubeCoordinate_timeColumn_unit hY heq hhalf hx).2
  have hmomentum : fiberLegendre (F.tubeCoordinateEnergy Y) (Z p₀) =
      ContinuousLinearMap.fst ℝ ℝ W := by
    rw [hzeq]
    exact (hF.tubeCoordinateEnergy_calibrated_identities Y hY hi t₀
      heq hhalf hbound hx).2.2.1
  rw [hF.tubeLengthMomentum_parameter_fderiv_of_unit hY hi hZ hz hs u,
    hF.tubeSpeed_parameter_fderiv_eq_momentum_radial Y hY hi t₀ heq hhalf hbound
      hZ hx hv u, hmomentum]

/-- The original global distance has its full compliance Hessian on the same actual
endpoint branch in a genuine calibrated tube. All momentum responses and the radial
correction are derived from the literal original energy and intrinsic family. -/
theorem tubeCoordinateDistance_hessian_of_calibrated_branch
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
    (hF : F.IsSmoothStronglyConvex) (Y : OpenPartialHomeomorph (ℝ × W) M)
    {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target) (t₀ : ℝ)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ))
    {Γ : ((ℝ × W) × (ℝ × W)) → ℝ → M} {B : Set ((ℝ × W) × (ℝ × W))}
    (hB : IsOpen B) (hBY : B ⊆ Y.source ×ˢ Y.source)
    (hEL : ∀ q ∈ B, F.IsEulerLagrangeOn (Γ q) univ)
    (hG : ContMDiffOn 𝓘(ℝ, ((ℝ × W) × (ℝ × W)) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun r ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ r.1) ⟨r.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {a b : ℝ} (hab : a < b)
    (hend : ∀ q ∈ B, Γ q a = Y q.1 ∧ Γ q b = Y q.2)
    (hbranch : let _instTubeHessianBranchENorm :
        ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      ∀ q ∈ B, F.lengthEDist (Y q.1) (Y q.2) = pathELength 𝓘(ℝ, E) (Γ q) a b)
    {q₀ : (ℝ × W) × (ℝ × W)} (hq₀ : q₀ ∈ B) {w : W}
    (hcentral : Γ q₀ = Λ w) (hstay : ∀ t ∈ Icc a b, (t, w) ∈ Y.source)
    (h k : (ℝ × W) × (ℝ × W)) :
    fderiv ℝ (fderiv ℝ (F.tubeCoordinateDistance Y)) q₀ h k =
      (F.tubeEndpointCompliance Y (Γ q₀) a b).inverse
        (h.2 - h.1) (k.2 - k.1) -
          (h.2 - h.1).1 * (k.2 - k.1).1 / (b - a) := by
  let Z (t : ℝ) (q : (ℝ × W) × (ℝ × W)) := tubeCoordinateTangentFamily Y Γ (q, t)
  let P (t : ℝ) := fiberLegendre (F.tubeCoordinateLength Y) ∘ Z t
  let C := F.tubeInverseEnergyHessian Y (Γ q₀)
  let S := F.tubeEndpointCompliance Y (Γ q₀) a b
  let p := ContinuousLinearMap.fst ℝ ℝ W
  have hYval (t : ℝ) : Y (t, w) = Λ w t := congrFun heq (t, w)
  have hx (t : ℝ) (ht : t ∈ Icc a b) : Γ q₀ t ∈ Y.target := by
    rw [hcentral, ← hYval]
    exact Y.map_source (hstay t ht)
  have hphase (t : ℝ) (ht : t ∈ Icc a b) : Z t q₀ = ((t, w), (1, 0)) := by
    have hn : (fun r : ℝ ↦ (r, w)) ⁻¹' Y.source ∈ 𝓝 t :=
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
        (Y.open_source.mem_nhds (hstay t ht))
    have he : (Y.symm ∘ Γ q₀) =ᶠ[𝓝 t] (fun r ↦ (r, w)) := by
      filter_upwards [hn] with r hr
      change Y.symm (Γ q₀ r) = (r, w)
      rw [hcentral, ← hYval]
      exact Y.left_inv hr
    change ((Y.symm ∘ Γ q₀) t, deriv (Y.symm ∘ Γ q₀) t) = _
    rw [he.eq_of_nhds, he.deriv_eq]
    congr 1
    exact (hasDerivAt_id t |>.prodMk (hasDerivAt_const t w)).deriv
  have hz (t : ℝ) (ht : t ∈ Icc a b) :
      Z t q₀ ∈ Y.source ×ˢ {v : ℝ × W | v ≠ 0} := by
    rw [hphase t ht]
    exact ⟨hstay t ht, by simp⟩
  have hZd (t : ℝ) (ht : t ∈ Icc a b) : DifferentiableAt ℝ (Z t) q₀ := by
    let D := (B ×ˢ (univ : Set ℝ)) ∩
      (fun r : ((ℝ × W) × (ℝ × W)) × ℝ ↦ Γ r.1 r.2) ⁻¹' Y.target
    have hc : ContinuousOn (fun r : ((ℝ × W) × (ℝ × W)) × ℝ ↦ Γ r.1 r.2)
        (B ×ˢ univ) :=
      (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp_continuousOn hG.continuousOn
    have hD : IsOpen D := hc.isOpen_inter_preimage (hB.prod isOpen_univ) Y.open_target
    have hT := contDiffOn_tubeCoordinateTangentFamily hi hD (hG.mono inter_subset_left)
      (fun _ hr ↦ hr.2)
    exact ((hT.contDiffAt (hD.mem_nhds ⟨⟨hq₀, mem_univ _⟩, hx t ht⟩)).comp q₀
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)
  have hPd (t : ℝ) (ht : t ∈ Icc a b) : DifferentiableAt ℝ (P t) q₀ :=
    ((contDiffAt_fiberLegendre
      ((hF.contDiffOn_tubeCoordinateLength Y hY hi).contDiffAt
        ((Y.open_source.prod isOpen_ne).mem_nhds (hz t ht)))).differentiableAt
          (by simp)).comp q₀ (hZd t ht)
  have hzero (t : ℝ) (ht : t ∈ Icc a b) (u : ℝ × W) :
      fderiv ℝ (fderiv ℝ (F.tubeCoordinateEnergy Y)) (Z t q₀) (u, 0) = 0 := by
    rw [hphase t ht]
    exact (hF.tubeCoordinateEnergy_calibrated_identities Y hY hi t₀ heq hhalf hbound
      (hstay t ht)).2.2.2.2.2.2.1 u
  have hmomentum (t : ℝ) (ht : t ∈ Icc a b) :
      fiberLegendre (F.tubeCoordinateEnergy Y) (Z t q₀) = p := by
    rw [hphase t ht]
    exact (hF.tubeCoordinateEnergy_calibrated_identities Y hY hi t₀ heq hhalf hbound
      (hstay t ht)).2.2.1
  have hC : ContinuousOn C (Icc a b) := fun t ht ↦
    (hF.continuousAt_tubeInverseEnergyHessian hY hi
      (hEL q₀ hq₀ t (mem_univ _)) (hx t ht)).continuousWithinAt
  have hSinv : S.IsInvertible := hF.isInvertible_tubeEndpointCompliance hY hi hab
    (fun t _ ↦ hEL q₀ hq₀ t (mem_univ _)) hx
  have hrad (t : ℝ) (ht : t ∈ Icc a b) (Q : (ℝ × W) →L[ℝ] ℝ) :
      p (C t Q) = Q (1, 0) := by
    have hh := hF.tubeEnergy_inverseHessian_radial_pairing hY hi (hz t ht) Q
    rw [hmomentum t ht] at hh
    exact hh.trans (congrArg (fun z ↦ Q z.2) (hphase t ht))
  have hradinv (v : ℝ × W) : S.inverse v (1, 0) = p v / (b - a) :=
    endpointCompliance_inverse_radial_pairing hab hC p (1, 0) hrad hSinv v
  have hstart : (fun q ↦ Y.symm (Γ q a)) =ᶠ[𝓝 q₀] Prod.fst := by
    filter_upwards [hB.mem_nhds hq₀] with q hq
    rw [(hend q hq).1, Y.left_inv (hBY hq).1]
  have hend' : (fun q ↦ Y.symm (Γ q b)) =ᶠ[𝓝 q₀] Prod.snd := by
    filter_upwards [hB.mem_nhds hq₀] with q hq
    rw [(hend q hq).2, Y.left_inv (hBY hq).2]
  have hresponse (t : ℝ) (ht : t ∈ Icc a b) (u : (ℝ × W) × (ℝ × W)) :
      fderiv ℝ (fiberLegendre (F.tubeCoordinateEnergy Y) ∘ Z t) q₀ u =
        S.inverse (u.2 - u.1) := by
    have hP : DifferentiableAt ℝ (fiberLegendre (F.tubeCoordinateEnergy Y) ∘ Z t) q₀ :=
      ((contDiffAt_fiberLegendre
        ((hF.contDiffOn_tubeCoordinateEnergy Y hY hi).contDiffAt
          ((Y.open_source.prod isOpen_ne).mem_nhds (hz t ht)))).differentiableAt
            (by simp)).comp q₀ (hZd t ht)
    have hΨ : DifferentiableAt ℝ (fun q ↦ F.tubeCoordinateMomentumFamily Y Γ (q, t)) q₀ :=
      (hZd t ht).fst.prodMk hP
    have hsecond := congrArg (fun D : ((ℝ × W) × (ℝ × W)) →L[ℝ]
      ((ℝ × W) →L[ℝ] ℝ) ↦ D u) hΨ.hasFDerivAt.snd.fderiv
    have hr := hF.tubeMomentumVariation_eq_compliance_inverse hY hi hB hEL hG hq₀
      hab hx hzero u t ht
    rw [hstart.fderiv_eq, hend'.fderiv_eq, fderiv_fst, fderiv_snd] at hr
    exact hsecond.trans hr
  have hnormalized (t : ℝ) (ht : t ∈ Icc a b) (u : (ℝ × W) × (ℝ × W)) :
      fderiv ℝ (P t) q₀ u =
        S.inverse (u.2 - u.1) - (p (u.2 - u.1) / (b - a)) • p := by
    have hv : (Z t q₀).2 = (1, 0) := congrArg Prod.snd (hphase t ht)
    have hh := hF.tubeLengthMomentum_parameter_fderiv_of_calibrated Y hY hi t₀ heq hhalf
      hbound (hZd t ht) (hz t ht).1 hv u
    rw [hresponse t ht u, hradinv] at hh
    exact hh
  apply endpoint_hessian_of_momentum_response
    (hPd a (left_mem_Icc.mpr hab.le)) (hPd b (right_mem_Icc.mpr hab.le))
    (Filter.Eventually.mono (hB.mem_nhds hq₀) (fun q hq ↦
      (hF.tubeEndpointDistance_hasFDerivAt_of_branch hY hi hB hBY hEL hG hab.le
        hend hbranch hq).fderiv)) S.inverse p (b - a)
    (hnormalized a (left_mem_Icc.mpr hab.le))
    (hnormalized b (right_mem_Icc.mpr hab.le)) h k

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
