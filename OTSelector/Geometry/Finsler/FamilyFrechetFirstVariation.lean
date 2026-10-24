import OTSelector.Analysis.Calculus.VariationDerivatives
import OTSelector.Analysis.CompactFrechetIntegral
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FamilyLengthFirstVariation
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.Variation.Lagrangian
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Geometry.Finsler.FamilyFrechetFirstVariation

* **Conditions:** A finite-dimensional parameter family with jointly regular actual tangents and nonzero central velocity.
* **Objects:** Frechet differentiability of original integrated length and its intrinsic endpoint-momentum differential.
* **Proof detail:** Differentiate the genuine speed integral with a compact bound, test each parameter line by scalar first variation and identify the full continuous-linear differential.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=46): Exercises 253Y(f)(i)–(vii), 253Y(g)–(h), pp. 46–47: Banach-valued L1, bounded bilinear maps and section integrals.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerFamilyFrechetFirstVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerFamilyFrechetFirstVariation`; the selected original proof blocks follow. -/
section

/-!
# Frechet first variation for actual manifold families

Joint regularity of the original total tangent family gives differentiability of its
original length integral for a finite-dimensional parameter space. The actual scalar
first-variation theorem along each parameter line identifies this Frechet differential
with the two endpoint momentum pairings of the same family.
-/

open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

namespace ContinuousFinslerNorm

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
/-- The real value of original path length is the integral of its actual speed
whenever that nonnegative speed is interval integrable. -/
theorem pathELength_toReal_eq_integral_speed (F : ContinuousFinslerNorm E M)
    {c : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hi : IntervalIntegrable
      (fun t ↦ (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ))
      volume a b) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    (pathELength 𝓘(ℝ, E) c a b).toReal =
      ∫ t in a..b, (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ) := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  have heq : pathELength 𝓘(ℝ, E) c a b = ENNReal.ofReal
      (∫ t in a..b, (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) : ℝ)) := by
    rw [pathELength_eq_lintegral_mfderiv_Ioo, intervalIntegral.integral_of_le hab,
      integral_Ioc_eq_integral_Ioo, ofReal_integral_eq_lintegral_ofReal
        (hi.1.mono_set Ioo_subset_Ioc_self)
        (Eventually.of_forall (fun _ ↦ NNReal.coe_nonneg _))]
    apply lintegral_congr
    intro t
    exact ENNReal.ofReal_coe_nnreal.symm
  rw [heq, ENNReal.toReal_ofReal
    (intervalIntegral.integral_nonneg hab (fun _ _ ↦ NNReal.coe_nonneg _))]

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- The actual original path length is Frechet differentiable in all finite-dimensional
parameters. Compactness and joint tangent regularity supply integral domination. -/
theorem differentiableAt_family_pathELength {Γ : W → ℝ → M}
    {B : Set W} {I : Set ℝ} (hB : IsOpen B) (hI : IsOpen I)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ I))
    {s₀ : W} {a b : ℝ} (hs₀ : s₀ ∈ B) (hab : a ≤ b) (hsegment : Icc a b ⊆ I)
    (hslit : ∀ t ∈ Icc a b,
      (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ s₀) ⟨t, (1 : ℝ)⟩).2 ≠ 0) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    DifferentiableAt ℝ
      (fun s ↦ (Manifold.pathELength 𝓘(ℝ, E) (Γ s) a b).toReal) s₀ := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let G : W × ℝ → TangentBundle 𝓘(ℝ, E) M := fun q ↦
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩
  let O := (B ×ˢ I) ∩ G ⁻¹' {z | z.2 ≠ 0}
  have hO : IsOpen O := hG.continuousOn.isOpen_inter_preimage (hB.prod hI)
    F.isOpen_slitTangent
  have henergy : ContDiffOn ℝ 1 (F.energy ∘ G) O := by
    apply ContMDiffOn.contDiffOn
    exact (hF.contMDiffOn_energy.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)).comp
      (hG.of_le (by norm_num) |>.mono inter_subset_left) (fun _ hq ↦ hq.2)
  have hpos (q : W × ℝ) (hq : q ∈ O) : 0 < 2 * F.energy (G q) :=
    mul_pos (by norm_num) (F.fiberEnergy_pos (G q).1 hq.2)
  have hf : ContDiffOn ℝ 1 (fun q ↦ (F.toFun (G q) : ℝ)) O := by
    have h := (contDiffOn_const.mul henergy).sqrt (fun q hq ↦ (hpos q hq).ne')
    apply h.congr
    intro q _
    change (F.toFun (G q) : ℝ) = Real.sqrt (2 * ((F.toFun (G q) : ℝ) ^ 2 / 2))
    rw [show 2 * ((F.toFun (G q) : ℝ) ^ 2 / 2) = (F.toFun (G q) : ℝ) ^ 2 by ring,
      Real.sqrt_sq (NNReal.coe_nonneg _)]
  have hd := hasFDerivAt_intervalIntegral_of_contDiffOn hO hf hab
    (fun t ht ↦ ⟨⟨hs₀, hsegment ht⟩, hslit t ht⟩)
  have heq : (fun s ↦ (pathELength 𝓘(ℝ, E) (Γ s) a b).toReal) =ᶠ[𝓝 s₀]
      (fun s ↦ ∫ t in a..b, (F.toFun (G (s, t)) : ℝ)) := by
    filter_upwards [hB.mem_nhds hs₀] with s hs
    apply F.pathELength_toReal_eq_integral_speed hab
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    apply NNReal.continuous_coe.comp_continuousOn
    apply F.continuous_toFun.comp_continuousOn
    exact hG.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun t ht ↦ ⟨hs, hsegment ht⟩)
  exact (hd.congr_of_eventuallyEq heq).differentiableAt

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
set_option backward.isDefEq.respectTransparency false in
/-- Pulling the true chart length differential back by the actual chart differential
recovers the original fiber length differential at the same tangent vector. -/
theorem chartLength_fderiv_comp_mfderiv (old : M) {x : M}
    (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (v : TangentSpace 𝓘(ℝ, E) x)
    (hz : (extChartAt 𝓘(ℝ, E) old x,
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) x v) ∈
        chartEnergyDomain old) :
    (fiberLegendre (fun z ↦ (F.chartLength old z : ℝ))
      (extChartAt 𝓘(ℝ, E) old x,
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) x v)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) x) =
        fderiv ℝ (fun w : TangentSpace 𝓘(ℝ, E) x ↦ (F.toFun ⟨x, w⟩ : ℝ)) v := by
  let : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := ‹NormedSpace ℝ E›
  let A : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) x
  let g : E → ℝ := fun w ↦ (F.chartLength old (extChartAt 𝓘(ℝ, E) old x, w) : ℝ)
  have hd : DifferentiableAt ℝ g (A v) :=
    (hF.contDiffAt_chartFiberLength old hz).differentiableAt (by simp)
  have heq : g ∘ A = fun w : TangentSpace 𝓘(ℝ, E) x ↦ (F.toFun ⟨x, w⟩ : ℝ) := by
    funext w
    exact congrArg NNReal.toReal (F.chartLength_mfderiv_extChartAt old hx w)
  have h := (hd.hasFDerivAt.comp v A.hasFDerivAt).fderiv
  rw [heq] at h
  exact h.symm

variable [FiniteDimensional ℝ E]

/-- The full Frechet derivative of original path length is the actual endpoint
length momentum difference, acting on the parameter derivatives in one legal chart. -/
theorem hasFDerivAt_family_pathELength_endpoint (old : M) {Γ : W → ℝ → M}
    {B : Set W} {I : Set ℝ} (hB : IsOpen B) (hI : IsOpen I)
    (hconn : IsPreconnected I)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ I))
    {s₀ : W} {a b : ℝ} (hs₀ : s₀ ∈ B) (hab : a ≤ b) (hsegment : Icc a b ⊆ I)
    (hEL : F.IsEulerLagrangeOn (Γ s₀) I)
    (hmap : MapsTo (Γ s₀) I (extChartAt 𝓘(ℝ, E) old).source) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    let σ : W × ℝ → E := fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)
    let z : ℝ → E × E := fun t ↦ (σ (s₀, t), deriv (fun r ↦ σ (s₀, r)) t)
    HasFDerivAt (fun s ↦ (pathELength 𝓘(ℝ, E) (Γ s) a b).toReal)
      ((fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) (z b)).comp
          (fderiv ℝ (fun s ↦ σ (s, b)) s₀) -
        (fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) (z a)).comp
          (fderiv ℝ (fun s ↦ σ (s, a)) s₀)) s₀ := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let σ : W × ℝ → E := fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)
  let z : ℝ → E × E := fun t ↦ (σ (s₀, t), deriv (fun r ↦ σ (s₀, r)) t)
  let len : W → ℝ := fun s ↦ (pathELength 𝓘(ℝ, E) (Γ s) a b).toReal
  have hd : DifferentiableAt ℝ len s₀ :=
    hF.differentiableAt_family_pathELength hB hI hG hs₀ hab hsegment (by
      intro t ht hzero
      have hp := F.speed_pos_of_isEulerLagrangeAt (hEL t (hsegment ht))
      have hz : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ s₀) ⟨t, (1 : ℝ)⟩ =
          ⟨Γ s₀ t, 0⟩ := TotalSpace.ext rfl (heq_of_eq hzero)
      rw [hz, F.map_zero] at hp
      exact (lt_irrefl 0 hp))
  have hσ (t : ℝ) (ht : t ∈ I) : DifferentiableAt ℝ (fun s ↦ σ (s, t)) s₀ := by
    have hp := (contMDiffOn_positionFamily_of_tangentFamily hG).contMDiffAt
      ((hB.prod hI).mem_nhds (show (s₀, t) ∈ B ×ˢ I from ⟨hs₀, ht⟩))
    have hs := hp.comp s₀ ((contDiffAt_id.prodMk contDiffAt_const).contMDiffAt)
    have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2 (extChartAt 𝓘(ℝ, E) old)
        (Γ s₀ t) := contMDiffAt_extChartAt' (by
      simpa only [extChartAt_source] using hmap ht)
    exact ((hc.comp s₀ hs).contDiffAt).differentiableAt (by norm_num)
  convert hd.hasFDerivAt using 1
  ext u
  let ℓ : ℝ → W := fun r ↦ s₀ + r • u
  let Γu : ℝ → ℝ → M := fun r ↦ Γ (ℓ r)
  have hℓ : ContDiff ℝ 2 ℓ := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hℓd : HasDerivAt ℓ u 0 := by
    simpa only [ℓ, id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add s₀
  have hℓ0 : ℓ 0 = s₀ := by simp [ℓ]
  have hBu : IsOpen (ℓ ⁻¹' B) := hB.preimage hℓ.continuous
  have hGu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γu q.1) ⟨q.2, (1 : ℝ)⟩)
      ((ℓ ⁻¹' B) ×ˢ I) := by
    have hpre : ContDiff ℝ 2 (fun q : ℝ × ℝ ↦ (ℓ q.1, q.2)) :=
      (hℓ.comp contDiff_fst).prodMk contDiff_snd
    exact hG.comp hpre.contMDiff.contMDiffOn (fun q hq ↦ ⟨hq.1, hq.2⟩)
  have h0 : (0 : ℝ) ∈ ℓ ⁻¹' B := by simpa only [mem_preimage, hℓ0] using hs₀
  have hEu : F.IsEulerLagrangeOn (Γu 0) I := by simpa only [Γu, hℓ0] using hEL
  have hmu : MapsTo (Γu 0) I (extChartAt 𝓘(ℝ, E) old).source := by
    simpa only [Γu, hℓ0] using hmap
  have hscalar := hF.hasDerivAt_family_pathELength_endpoint old hBu hI hconn hGu
    h0 hab hsegment hEu hmu
  have hdu := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hℓd hℓ0.symm
  have he (t : ℝ) (ht : t ∈ I) :
      fderiv ℝ (fun r ↦ extChartAt 𝓘(ℝ, E) old (Γu r t)) 0 1 =
        fderiv ℝ (fun s ↦ σ (s, t)) s₀ u := by
    rw [fderiv_apply_one_eq_deriv]
    exact ((hσ t ht).hasFDerivAt.comp_hasDerivAt_of_eq 0 hℓd hℓ0.symm).deriv
  have hphase (t : ℝ) :
      variationPhase (fun q : ℝ × ℝ ↦ extChartAt 𝓘(ℝ, E) old (Γu q.1 q.2))
        (0, t) = z t := by
    simp only [variationPhase, variationVelocity, Γu, hℓ0, z, σ]
  have hu := hscalar.unique hdu
  dsimp only at hu
  rw [hphase b, hphase a, he b (hsegment (right_mem_Icc.mpr hab)),
    he a (hsegment (left_mem_Icc.mpr hab))] at hu
  exact hu

set_option backward.isDefEq.respectTransparency false in
/-- Intrinsic endpoint first variation: the original fiber length momenta act on
actual manifold parameter differentials of the same family. Frechet differentiability
is proved from the jointly C2 total tangent family, not supplied as a hypothesis. -/
theorem hasFDerivAt_family_pathELength_mfderiv (old : M) {Γ : W → ℝ → M}
    {B : Set W} {I : Set ℝ} (hB : IsOpen B) (hI : IsOpen I)
    (hconn : IsPreconnected I)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ I))
    {s₀ : W} {a b : ℝ} (hs₀ : s₀ ∈ B) (hab : a ≤ b) (hsegment : Icc a b ⊆ I)
    (hEL : F.IsEulerLagrangeOn (Γ s₀) I)
    (hmap : MapsTo (Γ s₀) I (extChartAt 𝓘(ℝ, E) old).source) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    let p : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (Γ s₀ t) →L[ℝ] ℝ := fun t ↦
      fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Γ s₀ t) ↦ (F.toFun ⟨Γ s₀ t, v⟩ : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ s₀) t 1)
    HasFDerivAt (fun s ↦ (pathELength 𝓘(ℝ, E) (Γ s) a b).toReal)
      ((p b).comp (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) (fun s ↦ Γ s b) s₀) -
        (p a).comp (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) (fun s ↦ Γ s a) s₀)) s₀ := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let σ : W × ℝ → E := fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ q.1 q.2)
  let z : ℝ → E × E := fun t ↦ (σ (s₀, t), deriv (fun r ↦ σ (s₀, r)) t)
  let A (t : ℝ) := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Γ s₀ t)
  let p : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (Γ s₀ t) →L[ℝ] ℝ := fun t ↦
    fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Γ s₀ t) ↦ (F.toFun ⟨Γ s₀ t, v⟩ : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ s₀) t 1)
  have hposition := contMDiffOn_positionFamily_of_tangentFamily hG
  obtain ⟨_, hphase, _⟩ := hF.chartEulerLagrange_of_isEulerLagrangeOn hEL old hmap
  have he (t : ℝ) (ht : t ∈ I) :
      (fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) (z t)).comp
        (fderiv ℝ (fun s ↦ σ (s, t)) s₀) =
      (p t).comp (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) (fun s ↦ Γ s t) s₀) := by
    have hjoint := hposition.contMDiffAt
      ((hB.prod hI).mem_nhds (show (s₀, t) ∈ B ×ˢ I from ⟨hs₀, ht⟩))
    have hparam : MDifferentiableAt 𝓘(ℝ, W) 𝓘(ℝ, E) (fun s ↦ Γ s t) s₀ :=
      (hjoint.comp s₀ ((contDiffAt_id.prodMk contDiffAt_const).contMDiffAt)).mdifferentiableAt
        (by norm_num)
    have htime : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ s₀) t :=
      (hjoint.comp t ((contDiffAt_const.prodMk contDiffAt_id).contMDiffAt)).mdifferentiableAt
        (by norm_num)
    have hc : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old)
        (Γ s₀ t) := mdifferentiableAt_extChartAt (by
      simpa only [extChartAt_source] using hmap ht)
    have hvel : deriv (fun r ↦ σ (s₀, r)) t =
        A t (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ s₀) t 1) := by
      have h := mfderiv_comp_apply t hc htime (1 : ℝ)
      simp only [mfderiv_eq_fderiv] at h
      exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ)).symm.trans h
    have hpar : fderiv ℝ (fun s ↦ σ (s, t)) s₀ =
        (A t).comp (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) (fun s ↦ Γ s t) s₀) := by
      have h := mfderiv_comp s₀ hc hparam
      rw [mfderiv_eq_fderiv] at h
      exact h
    have hz : (σ (s₀, t), A t (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ s₀) t 1)) ∈
        chartEnergyDomain old := by
      rw [← hvel]
      exact hphase t ht
    have hp := hF.chartLength_fderiv_comp_mfderiv old (hmap ht)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ s₀) t 1) hz
    change (fiberLegendre (fun z ↦ (F.chartLength old z : ℝ))
      (σ (s₀, t), deriv (fun r ↦ σ (s₀, r)) t)).comp _ = _
    rw [hvel, hpar]
    ext u
    exact congrArg (fun D ↦ D
      (mfderiv 𝓘(ℝ, W) 𝓘(ℝ, E) (fun s ↦ Γ s t) s₀ u)) hp
  have h := hF.hasFDerivAt_family_pathELength_endpoint old hB hI hconn hG hs₀ hab
    hsegment hEL hmap
  dsimp only at h
  rw [he b (hsegment (right_mem_Icc.mpr hab)),
    he a (hsegment (left_mem_Icc.mpr hab))] at h
  exact h

end IsSmoothStronglyConvex
end ContinuousFinslerNorm
end OTSelector.Geometry

end
end
