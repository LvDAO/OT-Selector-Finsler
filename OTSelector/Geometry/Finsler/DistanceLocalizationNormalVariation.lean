import Mathlib.Analysis.Calculus.Rademacher
import OTSelector.Analysis.Calculus.CompactSmoothLipschitz
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.CovectorNormalization
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.InitialPhaseMomentum
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.SignedSpeed
import OTSelector.Geometry.Manifold.TangentFamilyPosition
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceLocalizationNormalVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceLocalizationNormalVariation`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.DistanceLocalizationNormalVariation

* **Conditions:** One smooth complete actual flow with unit/constant-energy normalized conormal seed data and a differentiable or Lipschitz path of initial states.
* **Objects:** Signed endpoint momentum-variation identities, vanishing normal variation and the actual diagonal tangent split.
* **Proof detail:** Compose the actual smooth first variation with the state path, use the constant-speed differential and initial conormal to kill its pairing, and apply Rademacher for the AE path form.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): The path need only be differentiable at the stated point or almost everywhere; no C2 state path or chosen-label segment differentiability is imposed.
-/

/-!
# Normal variations along Lipschitz paths of actual initial states

Signed first variation for the smooth complete phase flow is composed with an
arbitrary differentiable path of initial states. Constant speed and the actual
initial conormal kill its terminal normal variation. The path itself need not
be twice differentiable, nor differentiable on every prescribed label segment.
-/

open Set Filter Manifold Bundle MeasureTheory Metric
open scoped Topology ContDiff NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- The actual length momentum preserves a phase direction tangent to the
constant-speed shell. No nearby minimizing or calibrated family is required. -/
theorem lengthMomentum_phase_direction_eq_initial
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hC2 : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z : E × E} (hz : z ∈ chartEnergyDomain old) (t : ℝ) (v : E × E)
    (hspeed : fderiv ℝ (fun q ↦ (F.chartLength old q : ℝ)) z v = 0) :
    let p := fderiv ℝ
      (fun w : TangentSpace 𝓘(ℝ, E) (Phi z t) ↦ (F.toFun ⟨Phi z t, w⟩ : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) t 1)
    p (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (fun q ↦ Phi q t) z v) =
      fiberLegendre (fun q ↦ (F.chartLength old q : ℝ)) z v.1 := by
  have hvar := hF.hasFDerivAt_signed_speed_of_complete_tangentFamily
    old 0 hEL hinit hC2 hz t
  have hspeedD := ((hF.contDiffOn_chartLength old).contDiffAt
    ((isOpen_chartEnergyDomain old).mem_nhds hz)).differentiableAt (by simp)
  have hd := hvar.unique (hspeedD.hasFDerivAt.const_mul (t - 0))
  have heq := congrArg (fun L : (E × E) →L[ℝ] ℝ ↦ L v) hd
  have hzero := hF.initial_lengthMomentum_comp_parameterDeriv old hinit hz
    (hEL z hz 0 (mem_univ _))
  have hi := congrArg (fun L : (E × E) →L[ℝ] ℝ ↦ L v) hzero
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    smul_apply, smul_eq_mul, hspeed, mul_zero] at heq
  exact (sub_eq_zero.mp heq).trans hi

/-- Constant original speed along a differentiable initial-state path preserves
its conormal evaluation at every elapsed time. Differentiability is needed only
at the one path parameter under consideration. -/
theorem lengthMomentum_path_variation_eq_initial
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hC2 : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z : ℝ → E × E} {s : ℝ} {v : E × E}
    (hz : z s ∈ chartEnergyDomain old) (hzD : HasDerivAt z v s)
    {c : ℝ} (hunit : (fun q ↦ (F.chartLength old (z q) : ℝ)) =ᶠ[𝓝 s] fun _ ↦ c)
    (t : ℝ) :
    let p := fderiv ℝ
      (fun w : TangentSpace 𝓘(ℝ, E) (Phi (z s) t) ↦ (F.toFun ⟨Phi (z s) t, w⟩ : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi (z s)) t 1)
    p (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun q ↦ Phi (z q) t) s 1) =
      fiberLegendre (fun q ↦ (F.chartLength old q : ℝ)) (z s) v.1 := by
  have hsmooth := ((hF.contDiffOn_chartLength old).contDiffAt
    ((isOpen_chartEnergyDomain old).mem_nhds hz)).differentiableAt (by simp)
  have hs := hsmooth.hasFDerivAt.comp_hasDerivAt s hzD
  have hc : HasDerivAt (fun q ↦ (F.chartLength old (z q) : ℝ)) 0 s :=
    (hasDerivAt_const s c).congr_of_eventuallyEq hunit
  have hspeed := hs.unique hc
  have hpos : MDifferentiableAt 𝓘(ℝ, E × E) 𝓘(ℝ, E)
      (fun q ↦ Phi q t) (z s) :=
    (contMDiffAt_positionParameter_of_tangentFamily
      (isOpen_chartEnergyDomain old) hC2 hz t).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp_apply s hpos hzD.differentiableAt.mdifferentiableAt (1 : ℝ)
  have hv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E × E) z s (1 : ℝ) = v := by
    rw [mfderiv_eq_fderiv]
    exact hzD.deriv
  have heq := hcomp.trans (congrArg
    (mfderiv 𝓘(ℝ, E × E) 𝓘(ℝ, E) (fun q ↦ Phi q t) (z s)) hv)
  exact (congrArg _ heq).trans
    (hF.lengthMomentum_phase_direction_eq_initial old hEL hinit hC2 hz t v hspeed)

/-- Normalize the actual differential of a C1 potential along a level path.
At every parameter where the normalized state is differentiable, its position
variation is annihilated by the original terminal length covector. -/
theorem lengthMomentum_normalized_level_path_zero
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hC2 : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {G : E → ℝ} {σ : ℝ → E} {s : ℝ}
    (hG : DifferentiableAt ℝ G (σ s))
    (hlegal : ∀ᶠ q in 𝓝 s, (σ q, fderiv ℝ G (σ q)) ∈ eL.target)
    {c : ℝ} (hlevel : (fun q ↦ G (σ q)) =ᶠ[𝓝 s] fun _ ↦ c)
    (hstate : DifferentiableAt ℝ
      (fun q ↦ F.covectorNormalization old eL (1 / 2) (σ q, fderiv ℝ G (σ q))) s)
    (t : ℝ) :
    let z := fun q ↦ F.covectorNormalization old eL (1 / 2) (σ q, fderiv ℝ G (σ q))
    let p := fderiv ℝ
      (fun w : TangentSpace 𝓘(ℝ, E) (Phi (z s) t) ↦ (F.toFun ⟨Phi (z s) t, w⟩ : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi (z s)) t 1)
    p (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun q ↦ Phi (z q) t) s 1) = 0 := by
  let z := fun q ↦ F.covectorNormalization old eL (1 / 2) (σ q, fderiv ℝ G (σ q))
  have hN := (hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)).2.2
  have hNs := hN _ hlegal.self_of_nhds
  have hunit : (fun q ↦ (F.chartLength old (z q) : ℝ)) =ᶠ[𝓝 s] fun _ ↦ 1 := by
    filter_upwards [hlegal] with q hq
    have he := (hN _ hq).2.2.1
    rw [F.chartEnergy_eq_chartLength_sq] at he
    dsimp only [z]
    nlinarith [NNReal.coe_nonneg (F.chartLength old
      (F.covectorNormalization old eL (1 / 2) (σ q, fderiv ℝ G (σ q))))]
  have hzero : fderiv ℝ G (σ s) (deriv z s).1 = 0 := by
    have hd := hG.hasFDerivAt.comp_hasDerivAt s hstate.hasDerivAt.fst
    exact hd.unique ((hasDerivAt_const s c).congr_of_eventuallyEq hlevel)
  have hm := hNs.2.2.2.1
  have hu : (F.chartLength old (z s) : ℝ) = 1 := hunit.self_of_nhds
  dsimp only [z] at hu
  rw [hF.chartLegendre_eq_length_smul_fderiv old hNs.2.1, hu, one_smul] at hm
  have hvar := hF.lengthMomentum_path_variation_eq_initial old hEL hinit hC2
    hNs.2.1 hstate.hasDerivAt hunit t
  refine hvar.trans ?_
  change (fderiv ℝ (fun v ↦ (F.chartLength old ((z s).1, v) : ℝ)) (z s).2)
    (deriv z s).1 = 0
  rw [hm]
  simp only [smul_apply, smul_eq_mul, hzero, mul_zero]

/-- Every prescribed Lipschitz path in an actual C1,1 level section has
almost-everywhere normal cancellation after the actual complete flow. The
normalization's Lipschitz bound is produced on the compact path image; no
ambient almost-everywhere statement is restricted to the chosen path. -/
theorem ae_lengthMomentum_normalized_level_path_zero
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hC2 : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {L : ℝ≥0}
    (hDG : LipschitzWith L (fderiv ℝ G))
    {σ : ℝ → E} {a b : ℝ} {C : ℝ≥0}
    (hσ : LipschitzOnWith C σ (Icc a b))
    (hlegal : ∀ q ∈ Icc a b, (σ q, fderiv ℝ G (σ q)) ∈ eL.target)
    {c : ℝ} (hlevel : ∀ q ∈ Icc a b, G (σ q) = c) :
    let z := fun q ↦ F.covectorNormalization old eL (1 / 2) (σ q, fderiv ℝ G (σ q))
    ∀ᵐ s ∂volume.restrict (Ioo a b), DifferentiableAt ℝ z s ∧ ∀ t : ℝ,
      let p := fderiv ℝ
        (fun w : TangentSpace 𝓘(ℝ, E) (Phi (z s) t) ↦ (F.toFun ⟨Phi (z s) t, w⟩ : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi (z s)) t 1)
      p (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun q ↦ Phi (z q) t) s 1) = 0 := by
  let q : ℝ → E × (E →L[ℝ] ℝ) := fun s ↦ (σ s, fderiv ℝ G (σ s))
  let z := fun s ↦ F.covectorNormalization old eL (1 / 2) (q s)
  have hq : LipschitzOnWith (max C (L * C)) q (Icc a b) :=
    hσ.prodMk (hDG.comp_lipschitzOnWith hσ)
  have hK : IsCompact (q '' Icc a b) := isCompact_Icc.image_of_continuousOn hq.continuousOn
  have hKU : q '' Icc a b ⊆ eL.target := by
    rintro _ ⟨s, hs, rfl⟩
    exact hlegal s hs
  have hN := (hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)).2.1
  obtain ⟨r, _, _, _, Cn, hNl⟩ := exists_lipschitzOnWith_cthickening_of_contDiffOn
    hK eL.open_target hKU (hN.of_le (by simp))
  have hz : LipschitzOnWith (Cn * max C (L * C)) z (Icc a b) :=
    hNl.comp hq (fun s hs ↦ self_subset_cthickening (q '' Icc a b) (mem_image_of_mem q hs))
  filter_upwards [ae_restrict_of_ae (hz.ae_differentiableWithinAt_of_mem (μ := volume)),
    ae_restrict_mem measurableSet_Ioo] with s hs hsI
  have hscc : s ∈ Icc a b := Ioo_subset_Icc_self hsI
  have hsn : Icc a b ∈ 𝓝 s := Icc_mem_nhds hsI.1 hsI.2
  have hdz : DifferentiableAt ℝ z s := (hs hscc).differentiableAt hsn
  refine ⟨hdz, fun t ↦ ?_⟩
  apply hF.lengthMomentum_normalized_level_path_zero old hEL hinit hC2 heL hsource hInv
    (c := c) (hG.differentiable one_ne_zero _) _ _ hdz t
  · filter_upwards [hsn] with s hs
    exact hlegal s hs
  · filter_upwards [hsn] with s hs
    exact hlevel s hs

omit [FiniteDimensional ℝ E] in
/-- The actual moving-time competitor has the central unit velocity plus its
fixed-time label variation. Only one derivative of the initial-state path is used. -/
theorem complete_family_diagonal_velocity_split
    (old : M) {Phi : (E × E) → ℝ → M}
    (hC2 : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z : ℝ → E × E} {s : ℝ} (hz : z s ∈ chartEnergyDomain old)
    (hzD : DifferentiableAt ℝ z s) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun q ↦ Phi (z q) q) s 1 =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun q ↦ Phi (z q) s) s 1 +
        mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi (z s)) s 1 := by
  have hposOn : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) 2
      (fun q ↦ Phi q.1 q.2) (chartEnergyDomain old ×ˢ univ) :=
    fun q hq ↦ (Bundle.contMDiffWithinAt_totalSpace.mp (hC2 q hq)).1
  have hpos : MDifferentiableAt 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E)
      (fun q : (E × E) × ℝ ↦ Phi q.1 q.2) (z s, s) := (hposOn.contMDiffAt
    (((isOpen_chartEnergyDomain old).prod isOpen_univ).mem_nhds
      (show (z s, s) ∈ chartEnergyDomain old ×ˢ univ from ⟨hz, mem_univ _⟩))).mdifferentiableAt
      (by norm_num)
  have hd := hzD.hasDerivAt.prodMk (hasDerivAt_id s)
  have hi : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, (E × E) × ℝ) (fun q ↦ (z q, q)) s (1 : ℝ) =
      (deriv z s, (1 : ℝ)) := by
    rw [mfderiv_eq_fderiv]
    exact hd.deriv
  have htotal := mfderiv_comp_apply (f := fun q ↦ (z q, q))
    (g := fun q : (E × E) × ℝ ↦ Phi q.1 q.2) s hpos hd.differentiableAt.mdifferentiableAt (1 : ℝ)
  have htotal' := htotal.trans (congrArg
    (mfderiv 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) (fun q ↦ Phi q.1 q.2) (z s, s)) hi)
  have hleftD := hzD.hasDerivAt.prodMk (hasDerivAt_const s s)
  have hrightD := (hasDerivAt_const s (z s)).prodMk (hasDerivAt_id s)
  have hl := mfderiv_comp_apply (f := fun q ↦ (z q, s))
    (g := fun q : (E × E) × ℝ ↦ Phi q.1 q.2) s hpos
    hleftD.differentiableAt.mdifferentiableAt (1 : ℝ)
  have hr := mfderiv_comp_apply (f := fun q ↦ (z s, q))
    (g := fun q : (E × E) × ℝ ↦ Phi q.1 q.2) s hpos
    hrightD.differentiableAt.mdifferentiableAt (1 : ℝ)
  have hli : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, (E × E) × ℝ) (fun q ↦ (z q, s)) s (1 : ℝ) =
      (deriv z s, (0 : ℝ)) := by
    rw [mfderiv_eq_fderiv]
    exact hleftD.deriv
  have hri : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, (E × E) × ℝ) (fun q ↦ (z s, q)) s (1 : ℝ) =
      (0, (1 : ℝ)) := by
    rw [mfderiv_eq_fderiv]
    exact hrightD.deriv
  let A := mfderiv 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) (fun q ↦ Phi q.1 q.2) (z s, s)
  have hl' := hl.trans (congrArg A hli)
  have hr' := hr.trans (congrArg A hri)
  have hsplit : A (deriv z s, (1 : ℝ)) = A (deriv z s, 0) + A (0, 1) := by
    rw [← map_add]
    congr 1
    change (deriv z s, (1 : ℝ)) = (deriv z s, 0) + (0, 1)
    simp
  exact htotal'.trans (hsplit.trans (congrArg₂ (· + ·) hl'.symm hr'.symm))

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
