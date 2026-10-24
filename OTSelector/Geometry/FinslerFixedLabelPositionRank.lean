import OTSelector.LinearAlgebra.Dual.FixedProjectionKernelEquiv
import OTSelector.Geometry.Finsler.C11LevelSmoothTube

/-!
# Position rank and smooth tubes in the original fixed labels

The actual phase jet of a fixed-projection section transfers the existing calibrated
position comparison to its original labels. The smooth tube is then constructed
directly for that same family, without changing its coordinates or flow.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M] in
/-- The established position comparison applies to the same family in fixed labels
when its initial phase derivative is the actual fixed-projection section derivative. -/
theorem levelPositionComparison_of_fixedProjection_phaseJet
    (old : M) {G : E → ℝ} {A : E → ℝ → M} {δ : ℝ} {x : E}
    (hcmp : F.HasC11LevelPositionComparisonAt old G A δ x)
    (p₀ : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0)
    (hp : (fderiv ℝ G x) v₀ ≠ 0)
    {B : Set p₀.ker} {Γ : p₀.ker → ℝ → M}
    (hB : IsOpen B) (h0 : (0 : p₀.ker) ∈ B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hsource : ∀ w ∈ B, Γ w 0 ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hjet :
      let R := p₀.ker.subtypeL -
        ((fderiv ℝ G x).comp p₀.ker.subtypeL).smulRight
          (((fderiv ℝ G x) v₀)⁻¹ • v₀)
      HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, 0))
        (R.prod ((fderiv ℝ (fderiv ℝ G) x).comp R)) 0)
    (hvalue : F.chartMomentumFamily old Γ (0, 0) = (x, fderiv ℝ G x)) :
    let R := p₀.ker.subtypeL -
      ((fderiv ℝ G x).comp p₀.ker.subtypeL).smulRight
        (((fderiv ℝ G x) v₀)⁻¹ • v₀)
    A x = Γ 0 ∧ ∀ (terminal : M) (t : ℝ), |t| < δ →
      Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
      HasFDerivAt (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ w t))
        ((fderiv ℝ (fun y ↦ extChartAt 𝓘(ℝ, E) terminal (A y t)) x).comp R) 0 ∧
      Function.Injective
        (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ w t)) 0) := by
  let p := fderiv ℝ G x
  let H := fderiv ℝ (fderiv ℝ G) x
  let R := p₀.ker.subtypeL - (p.comp p₀.ker.subtypeL).smulRight ((p v₀)⁻¹ • v₀)
  let L : p₀.ker ≃L[ℝ] p.ker := fixedProjectionKernelEquiv p₀ p v₀ hp₀ hp
  have hL0 : L 0 = 0 := L.map_zero
  have hLs0 : L.symm 0 = 0 := L.symm.map_zero
  have hR : R = p.ker.subtypeL.comp L.toContinuousLinearMap :=
    (fixedProjectionKernelEquiv_subtype_comp p₀ p v₀ hp₀ hp).symm
  let B' := L.symm ⁻¹' B
  let Γ' : p.ker → ℝ → M := fun w ↦ Γ (L.symm w)
  have hB' : IsOpen B' := hB.preimage L.symm.continuous
  have h0' : (0 : p.ker) ∈ B' := by simpa only [B', mem_preimage, hLs0] using h0
  have hjet0 : HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, 0))
      (R.prod (H.comp R)) (L.symm 0) := by simpa only [hLs0] using hjet
  have hjet' : HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ' (w, 0))
      (p.ker.subtypeL.prod (H.comp p.ker.subtypeL)) 0 := by
    have hh := hjet0.comp 0 L.symm.hasFDerivAt
    have hmap : (R.prod (H.comp R)).comp L.symm.toContinuousLinearMap =
        p.ker.subtypeL.prod (H.comp p.ker.subtypeL) := by
      ext w <;> simp [hR]
    rw [hmap] at hh
    exact hh
  have hvalue' : F.chartMomentumFamily old Γ' (0, 0) = (x, p) := by
    simpa only [Γ', ContinuousFinslerNorm.chartMomentumFamily, hLs0] using hvalue
  obtain ⟨hcenter, hrank⟩ := hcmp B' Γ' hB' h0'
    (fun w hw ↦ hEL (L.symm w) hw)
    (fun w hw ↦ hsource (L.symm w) hw) hjet' hvalue'
  have hcenter' : A x = Γ 0 := by simpa only [Γ', hLs0] using hcenter
  refine ⟨hcenter', fun terminal t ht hlegal ↦ ?_⟩
  have hlegal' : Γ' 0 t ∈ (extChartAt 𝓘(ℝ, E) terminal).source := by
    simpa only [Γ', hLs0] using hlegal
  obtain ⟨_, hD, _, _, _, hinj⟩ := hrank terminal t ht hlegal'
  have hD0 : HasFDerivAt (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ' w t))
      ((fderiv ℝ (fun y ↦ extChartAt 𝓘(ℝ, E) terminal (A y t)) x).comp
        p.ker.subtypeL) (L 0) := by simpa only [hL0] using hD
  have hcomp := hD0.comp 0 L.hasFDerivAt
  have hDΓ : HasFDerivAt (fun w ↦ extChartAt 𝓘(ℝ, E) terminal (Γ w t))
      ((fderiv ℝ (fun y ↦ extChartAt 𝓘(ℝ, E) terminal (A y t)) x).comp R) 0 := by
    simpa only [Function.comp_def, Γ', L.symm_apply_apply,
      ContinuousLinearMap.comp_assoc, ← hR] using hcomp
  refine ⟨hDΓ, ?_⟩
  rw [hDΓ.fderiv, hR, ← ContinuousLinearMap.comp_assoc, ← hD.fderiv]
  exact hinj.comp L.injective

/-- The same fixed-label family has a smooth tube and inverse-time calibration on
each compact inner time set. The initial phase jet supplies position rank through
the existing calibrated comparison, and the fixed covector supplies the dimension. -/
theorem exists_smooth_calibratedTube_of_fixedProjection_phaseJet
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {G P : E → ℝ} {A : E → ℝ → M} {δ : ℝ} {x : E}
    (hcmp : F.HasC11LevelPositionComparisonAt old G A δ x)
    (p₀ : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0)
    (hp : (fderiv ℝ G x) v₀ ≠ 0)
    {B : Set p₀.ker} {σ v : p₀.ker → E}
    {a : p₀.ker → ℝ} {Γ : p₀.ker → ℝ → M}
    (hB : IsOpen B) (h0 : (0 : p₀.ker) ∈ B)
    (hP : ∀ w ∈ B, DifferentiableAt ℝ P (σ w))
    (hσ : ContDiffOn ℝ ∞ σ B) (hσ0 : σ 0 = x)
    (hlevel : ∀ w ∈ B, P (σ w) = P x)
    (hv : ContDiffOn ℝ ∞ v B) (ha0 : a 0 = 1)
    (hDP : fderiv ℝ P x = fderiv ℝ G x)
    (hdomain : ∀ w ∈ B, (σ w, v w) ∈ chartEnergyDomain old)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hinit : ∀ w ∈ B,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (σ w, v w))
    (hm : ∀ w ∈ B, F.chartMomentumFamily old Γ (w, 0) =
      potentialConormalState P σ a w)
    (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = 1 / 2)
    (hjet :
      let R := p₀.ker.subtypeL -
        ((fderiv ℝ G x).comp p₀.ker.subtypeL).smulRight
          (((fderiv ℝ G x) v₀)⁻¹ • v₀)
      HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, 0))
        (R.prod ((fderiv ℝ (fderiv ℝ G) x).comp R)) 0)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc (-δ) δ ↦ A x t))
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : J ⊆ Ioo (-δ) δ) :
    A x = Γ 0 ∧
    ContMDiffOn 𝓘(ℝ, p₀.ker × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (B ×ˢ univ) ∧
    ∃ (T : Set ℝ) (V : Set p₀.ker) (e : OpenPartialHomeomorph (ℝ × p₀.ker) M),
      IsOpen T ∧ IsOpen V ∧ J ⊆ T ∧ (0 : p₀.ker) ∈ V ∧
      T ×ˢ V ⊆ univ ×ˢ B ∧
      (e : ℝ × p₀.ker → M) = (fun q ↦ Γ q.2 q.1) ∧
      e.source = T ×ˢ V ∧
      e.target = (fun q : ℝ × p₀.ker ↦ Γ q.2 q.1) '' (T ×ˢ V) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × p₀.ker) 𝓘(ℝ, E) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × p₀.ker) ∞ e.symm e.target ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (manifoldFlowTimePotential e 1 0) e.target ∧
      (∀ y ∈ e.target, ∀ z : TangentSpace 𝓘(ℝ, E) y,
        @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 0) y z)
          (F.toFun ⟨y, z⟩ : ℝ)) ∧
      ∀ q ∈ e.source,
        manifoldFlowTimePotential e 1 0 (Γ q.2 q.1) = q.1 ∧
        HasDerivAt (fun t ↦ manifoldFlowTimePotential e 1 0 (Γ q.2 t)) 1 q.1 ∧
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 0) (Γ q.2 q.1) =
          fderiv ℝ (F.fiberEnergy (Γ q.2 q.1))
            (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) q.1 1) := by
  have hdim : Module.finrank ℝ p₀.ker + 1 = Module.finrank ℝ E := by
    simpa using (covectorSplitting p₀ v₀ hp₀).toLinearEquiv.finrank_eq
  have hseed : ContDiffOn ℝ ∞ (fun w ↦ (σ w, v w)) B := hσ.prodMk hv
  have hΓ := (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth old hB hEL
    hseed hdomain hinit).1
  have hΓ₂ := hΓ.of_le (by simp : (2 : ℕ∞ω) ≤ ∞)
  have hsource (w : p₀.ker) (hw : w ∈ B) :
      Γ w 0 ∈ (extChartAt 𝓘(ℝ, E) old).source := by
    have hb : Γ w 0 = (extChartAt 𝓘(ℝ, E) old).symm (σ w) := by
      have h := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hinit w hw)
      rw [tangentChart_symm_eq old (hdomain w hw).1] at h
      exact h
    rw [hb]
    exact (extChartAt 𝓘(ℝ, E) old).map_target (hdomain w hw).1
  have hvalue : F.chartMomentumFamily old Γ (0, 0) = (x, fderiv ℝ G x) := by
    simpa only [potentialConormalState, hσ0, ha0, one_smul, hDP] using hm 0 h0
  obtain ⟨hcenter, hrank⟩ := levelPositionComparison_of_fixedProjection_phaseJet
    old hcmp p₀ v₀ hp₀ hp hB h0 hEL hsource hjet hvalue
  have hnormal (w : p₀.ker) (hw : w ∈ B) (t : ℝ) (terminal : M)
      (ht : Γ w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source) (ξ : p₀.ker) :
      (F.chartMomentumFamily terminal Γ (w, t)).2
        (fderiv ℝ (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (Γ z t)) w ξ) = 0 := by
    apply hF.chartMomentumFamily_gauss_zero_of_potential_initial hB hEL hΓ₂
      henergy old 0 hm hw (hsource w hw) (hP w hw)
      ((hσ.contDiffAt (hB.mem_nhds hw)).differentiableAt (by simp))
      (c := P x) _ terminal t ht ξ
    filter_upwards [hB.mem_nhds hw] with z hz
    exact hlevel z hz
  have hisoΓ : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc (-δ) δ ↦ Γ 0 t) := by
    rwa [← hcenter]
  have hregular (t : ℝ) (ht : t ∈ J) :
      HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) 0 := by
    intro terminal hlegal
    exact (hrank terminal t (abs_lt.mpr (hJsub ht)) hlegal).2
  refine ⟨hcenter, ?_⟩
  simpa only [sub_zero] using
    hF.exists_smooth_manifoldTube_calibration_of_chartSeed hdim hB hEL old
      hseed hdomain hinit henergy hnormal h0 hisoΓ hJ
      (fun _ ht ↦ ⟨(hJsub ht).1.le, (hJsub ht).2.le⟩) hregular 0

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
