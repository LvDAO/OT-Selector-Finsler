import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Flow.LocalVariational
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.PotentialNormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.C2Variation
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.Hamiltonian.NormalVariation
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.Jacobi.VariationalFlow
import OTSelector.Geometry.Finsler.Variation.Lagrangian
import OTSelector.Geometry.Symplectic.PotentialConormal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialNormalFlow.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialNormalFlow`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.PotentialNormalFlow

* **Conditions:** A genuine smooth immersed potential-level germ whose actual differential matches the central Finsler momentum.
* **Objects:** One normalized local conormal flow with full phase rank, isotropy, the actual variational equation and momentum normality.
* **Proof detail:** Normalize df on one inverse branch, use the exact level identity for initial normality/isotropy, and propagate both by the same Hamiltonian dynamics.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=253): Section 8.4, pp. 242–243, equations (8.53)–(8.58): canonical coordinate changes and preservation of the symplectic two-form.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Normalized potential conormal flows on actual level sets

The original Finsler data choose one genuine Legendre branch and one flow. On that same
branch the varying actual potential differential is positively normalized to constant
original energy. The actual immersed level-set seed has zero canonical pairing and
normal initial directions. Its same-flow derivative retains full phase rank, the actual
variational equation, zero pairing, and momentum-kernel normality on the closed time
interval. No normalized family or normality property is assumed.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

private theorem momentum_eq_zero_of_constantEnergy_seed (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {z : E × E} {w₀ : W} {seed : W → E × (E →L[ℝ] ℝ)}
    (hseed : seed w₀ = parametricLegendre (F.chartEnergy x₀) z)
    (hnormal : ∀ u : W, (parametricLegendre (F.chartEnergy x₀) z).2
      (fderiv ℝ seed w₀ u).1 = 0)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀))
    (hsource : e.source ⊆ chartEnergyDomain x₀) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {r : ℝ≥0} {t₀ T : ℝ} (hT : 0 < T)
    (hflow : LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField (F.chartEnergy x₀) e)
      t₀ (parametricLegendre (F.chartEnergy x₀) z) r (t₀ - T) (t₀ + T) Φ)
    (hmap : MapsTo Φ
      (closedBall (parametricLegendre (F.chartEnergy x₀) z) r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target)
    (hnear : ∀ᶠ w in 𝓝 w₀,
      seed w ∈ closedBall (parametricLegendre (F.chartEnergy x₀) z) r ∧
      F.chartEnergy x₀ (e.symm (seed w)) = F.chartEnergy x₀ z)
    (hdiff : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      DifferentiableAt ℝ (fun w ↦ Φ (seed w, t)) w₀)
    (hvar : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ∀ u : W,
      HasDerivWithinAt (fun s ↦ fderiv ℝ (fun w ↦ Φ (seed w, s)) w₀ u)
        (fderiv ℝ (localHamiltonianVectorField (F.chartEnergy x₀) e)
          (Φ (parametricLegendre (F.chartEnergy x₀) z, t))
          (fderiv ℝ (fun w ↦ Φ (seed w, t)) w₀ u))
        (Icc (t₀ - T) (t₀ + T)) t) :
    ∀ t ∈ Icc (t₀ - T) (t₀ + T), ∀ u : W,
      (Φ (parametricLegendre (F.chartEnergy x₀) z, t)).2
        (fderiv ℝ (fun w ↦ Φ (seed w, t)) w₀ u).1 = 0 := by
  let L := F.chartEnergy x₀
  let p₀ := parametricLegendre L z
  change seed w₀ = p₀ at hseed
  let Z := fun t ↦ fderiv ℝ (fun w ↦ Φ (seed w, t)) w₀
  let γ := fun t ↦ Φ (p₀, t)
  let I := Icc (t₀ - T) (t₀ + T)
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_chartEnergy x₀).mono hsource
  have hp₀ : p₀ ∈ closedBall p₀ r := mem_closedBall_self r.coe_nonneg
  have htarg (t : ℝ) (ht : t ∈ I) : γ t ∈ e.target := hmap ⟨hp₀, ht⟩
  have hγ (t : ℝ) (ht : t ∈ I) :
      HasDerivWithinAt γ (localHamiltonianVectorField L e (γ t)) I t :=
    hflow.hasDerivWithinAt p₀ hp₀ t ht
  have henergy (t : ℝ) (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
      (fun w ↦ L (e.symm (Φ (seed w, t)))) =ᶠ[𝓝 w₀] (fun _ ↦ L z) := by
    filter_upwards [hnear] with w hw
    have h := hF.chartEnergy_hamiltonianPositionVariation_eq_initial x₀ he hsource hG
      (ι := fun _ : ℝ ↦ seed w) (s := 0) hflow hmap hT hw.1 ht
    rw [variationPhase_hamiltonianPositionVariation he hflow hmap hw.1 ht] at h
    exact h.trans hw.2
  have henergyD (t : ℝ) (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) (u : W) :
      fderiv ℝ L (e.symm (γ t)) (fderiv ℝ e.symm (γ t) (Z t u)) = 0 := by
    have ht' : t ∈ I := Ioo_subset_Icc_self ht
    have hdG := ((hG.contDiffAt (e.open_target.mem_nhds (htarg t ht'))).differentiableAt
      (by simp)).hasFDerivAt
    have hdL := ((hL.contDiffAt
      (e.open_source.mem_nhds (e.map_target (htarg t ht')))).differentiableAt
      (by simp)).hasFDerivAt
    change HasFDerivAt e.symm (fderiv ℝ e.symm (Φ (p₀, t))) (Φ (p₀, t)) at hdG
    change HasFDerivAt L (fderiv ℝ L (e.symm (Φ (p₀, t)))) (e.symm (Φ (p₀, t))) at hdL
    rw [← hseed] at hdG hdL
    have hd := hdL.comp w₀ (hdG.comp w₀ (hdiff t ht').hasFDerivAt)
    have hc : HasFDerivAt (fun w ↦ L (e.symm (Φ (seed w, t)))) 0 w₀ :=
      (hasFDerivAt_const (𝕜 := ℝ) (L z) w₀).congr_of_eventuallyEq (henergy t ht)
    have heq := congrArg (fun D : W →L[ℝ] ℝ ↦ D u) (hd.unique hc)
    simpa only [hseed, ContinuousLinearMap.comp_apply, _root_.zero_apply,
      γ, Z, L] using heq
  intro t ht u
  let P : ℝ → ℝ := fun s ↦ (γ s).2 (Z s u).1
  have hdW (s : ℝ) (hs : s ∈ I) :
      HasDerivWithinAt P
        (baseEnergyDifferential L (e.symm (γ s)) (Z s u).1 +
          (γ s).2 (fderiv ℝ e.symm (γ s) (Z s u)).2) I s := by
    have hP : HasDerivWithinAt (fun v ↦ (γ v).2)
        (baseEnergyDifferential L (e.symm (γ s))) I s := (hγ s hs).snd
    have hJ : HasDerivWithinAt (fun v ↦ (Z v u).1)
        (fderiv ℝ (localHamiltonianVectorField L e) (γ s) (Z s u)).1 I s := (hvar s hs u).fst
    rw [localHamiltonianVectorField_fderiv_fst hL hG (htarg s hs)] at hJ
    exact hP.clm_apply hJ
  have hzeroD (s : ℝ) (hs : s ∈ Ioo (t₀ - T) (t₀ + T)) : HasDerivAt P 0 s := by
    have hs' : s ∈ I := Ioo_subset_Icc_self hs
    have hGs := (hG.contDiffAt (e.open_target.mem_nhds (htarg s hs'))).differentiableAt (by simp)
    have hLs := (hL.contDiffAt
      (e.open_source.mem_nhds (e.map_target (htarg s hs')))).differentiableAt
      (by simp)
    have hfst : (fderiv ℝ e.symm (γ s) (Z s u)).1 = (Z s u).1 :=
      congrArg (fun D : (E × (E →L[ℝ] ℝ)) →L[ℝ] E ↦ D (Z s u))
        (parametricLegendre_inverse_derivative_fst he (htarg s hs') hGs.hasFDerivAt)
    have heq := henergyD s hs u
    rw [← Prod.eta (fderiv ℝ e.symm (γ s) (Z s u)), fderiv_energy_split hLs,
      hfst, (parametricLegendre_inverse_components he (htarg s hs')).2] at heq
    rw [← heq]
    exact (hdW s hs').hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hinit : (fun w ↦ Φ (seed w, t₀)) =ᶠ[𝓝 w₀] seed := by
    filter_upwards [hnear] with w hw
    exact hflow.apply_initial (seed w) hw.1
  have hJ0 : Z t₀ u = fderiv ℝ seed w₀ u := by
    change fderiv ℝ (fun w ↦ Φ (seed w, t₀)) w₀ u = _
    rw [hinit.fderiv_eq]
  have hW0 : P t₀ = 0 := by
    change (Φ (p₀, t₀)).2 (Z t₀ u).1 = 0
    rw [hflow.apply_initial p₀ hp₀, hJ0]
    exact hnormal u
  have hinner : EqOn P (fun _ ↦ 0) (Ioo (t₀ - T) (t₀ + T)) := by
    intro s hs
    exact (isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
      (fun v hv ↦ (hzeroD v hv).differentiableAt.differentiableWithinAt)
      (fun v hv ↦ (hzeroD v hv).deriv) hs
      (show t₀ ∈ Ioo (t₀ - T) (t₀ + T) by constructor <;> linarith)).trans hW0
  exact hinner.of_subset_closure (fun s hs ↦ (hdW s hs).continuousWithinAt)
    continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo (show t₀ - T ≠ t₀ + T by linarith)]) ht

/-- A genuine smooth potential level set admits positive constant-energy normalization
and one actual conormal Finsler flow. Its same-flow variation is normal at all closed
times, canonically isotropic, injective in phase space, and solves the actual linearized
equation. Central potential-momentum matching and the given level-set immersion remain
explicit; normalization and every transported property are conclusions. -/
theorem exists_chartHamiltonian_potentialNormalFlow [FiniteDimensional ℝ E]
    (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {f : E → ℝ} {σ : W → E} {Ω : Set E} {V : Set W} {w₀ : W} {c : ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hV : IsOpen V) (hw₀ : w₀ ∈ V) (hσ : ContDiffOn ℝ ∞ σ V) (hσΩ : MapsTo σ V Ω)
    (hlevel : (fun w ↦ f (σ w)) =ᶠ[𝓝 w₀] fun _ ↦ c)
    (himm : Function.Injective (fderiv ℝ σ w₀))
    {v₀ : E} (hz : (σ w₀, v₀) ∈ chartEnergyDomain x₀)
    (hmatch : fderiv ℝ f (σ w₀) = fiberLegendre (F.chartEnergy x₀) (σ w₀, v₀))
    (t₀ : ℝ) :
    let L := F.chartEnergy x₀
    let z := (σ w₀, v₀)
    let p₀ := parametricLegendre L z
    ∃ (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
      (U : Set W) (v : W → E) (a : W → ℝ) (r : ℝ≥0) (T : ℝ)
      (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)),
      let seed := potentialConormalState f σ a
      let Z := fun t ↦ fderiv ℝ (fun w ↦ Φ (seed w, t)) w₀
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ e.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      IsOpen U ∧ w₀ ∈ U ∧ U ⊆ V ∧
      ContDiffOn ℝ ∞ v U ∧ ContDiffOn ℝ ∞ a U ∧ v w₀ = v₀ ∧ a w₀ = 1 ∧
      (∀ w ∈ U, (σ w, v w) ∈ e.source ∧ 0 < a w ∧
        L (σ w, v w) = L z ∧
        fiberLegendre L (σ w, v w) = a w • fderiv ℝ f (σ w) ∧
        e.symm (seed w) = (σ w, v w)) ∧
      0 < r ∧ 0 < T ∧
      LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
        t₀ p₀ r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target ∧
      (∀ᶠ w in 𝓝 w₀, seed w ∈ closedBall p₀ r ∧ L (e.symm (seed w)) = L z) ∧
      Z t₀ = fderiv ℝ seed w₀ ∧
      ∀ t ∈ Icc (t₀ - T) (t₀ + T),
        DifferentiableAt ℝ (fun w ↦ Φ (seed w, t)) w₀ ∧
        Function.Injective (Z t) ∧
        (∀ u w : W, canonicalPhasePairing (Z t u) (Z t w) = 0) ∧
        (∀ u : W, HasDerivWithinAt (fun s ↦ Z s u)
          (fderiv ℝ (localHamiltonianVectorField L e) (Φ (p₀, t)) (Z t u))
          (Icc (t₀ - T) (t₀ + T)) t) ∧
        ∀ u : W, (Z t u).1 ∈ (fiberLegendre L (e.symm (Φ (p₀, t)))).ker := by
  let L := F.chartEnergy x₀
  let z := (σ w₀, v₀)
  let p₀ := parametricLegendre L z
  obtain ⟨e, he, hzs, hzt, hsub, hG, _, hX, _⟩ :=
    hF.exists_smooth_chartHamiltonian x₀ hz
  obtain ⟨r, T, hr, hT, Φ, hflow, hmap, hdiff, hinit, hraw⟩ :=
    LocalFlow.exists_differentiableFlow_in_open e.open_target hX hzt t₀
  have hq : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ f (σ w)) V :=
    (hf.fderiv_of_isOpen hΩ (by simp : ∞ + 1 ≤ (∞ : ℕ∞ω))).comp hσ hσΩ
  obtain ⟨U, v, a, hU, hwU, hUV, hv, ha, hv₀, ha₀, hdata⟩ :=
    hF.exists_constantEnergy_covectorData_on_branch x₀ hV hw₀ hσ hq he hzs hsub hG hmatch
  let seed := potentialConormalState f σ a
  let Z := fun t ↦ fderiv ℝ (fun w ↦ Φ (seed w, t)) w₀
  let I := Icc (t₀ - T) (t₀ + T)
  have hf₂ : ContDiffAt ℝ 2 f (σ w₀) :=
    (hf.contDiffAt (hΩ.mem_nhds (hσΩ hw₀))).of_le (by simp : 2 ≤ ∞)
  have hσd : DifferentiableAt ℝ σ w₀ :=
    (hσ.contDiffAt (hV.mem_nhds hw₀)).differentiableAt (by simp)
  have had : DifferentiableAt ℝ a w₀ :=
    (ha.contDiffAt (hU.mem_nhds hwU)).differentiableAt (by simp)
  have hdseed := hasFDerivAt_potentialConormalState hf₂ hσd had
  have hseed : seed w₀ = p₀ := by
    change (σ w₀, a w₀ • fderiv ℝ f (σ w₀)) =
      (σ w₀, fiberLegendre (F.chartEnergy x₀) (σ w₀, v₀))
    rw [ha₀, one_smul, hmatch]
  have hseedprop := potentialConormalState_fderiv_properties hf₂ hσd had hlevel himm
  have hnormal (u : W) : p₀.2 (fderiv ℝ seed w₀ u).1 = 0 := by
    rw [hdseed.fderiv]
    change fiberLegendre L z (fderiv ℝ σ w₀ u) = 0
    have hn := potentialConormalState_momentum_eq_zero
      (a := a) (hf₂.differentiableAt (by norm_num)) hσd hlevel u
    simpa only [potentialConormalState, ha₀, one_smul, hmatch,
      p₀, parametricLegendre, z, L] using hn
  have hnear : ∀ᶠ w in 𝓝 w₀, seed w ∈ closedBall p₀ r ∧ L (e.symm (seed w)) = L z := by
    have hn := hdseed.continuousAt.preimage_mem_nhds
      (closedBall_mem_nhds (seed w₀) (show (0 : ℝ) < r from hr))
    change ∀ᶠ w in 𝓝 w₀, seed w ∈ closedBall (seed w₀) r at hn
    rw [hseed] at hn
    filter_upwards [hU.mem_nhds hwU, hn] with w hw hb
    refine ⟨hb, ?_⟩
    change L (e.symm (σ w, a w • fderiv ℝ f (σ w))) = L z
    rw [(hdata w hw).2.2.2.2]
    exact (hdata w hw).2.2.1
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_chartEnergy x₀).mono hsub
  have htarg (t : ℝ) (ht : t ∈ I) : Φ (p₀, t) ∈ e.target :=
    hmap ⟨mem_closedBall_self r.coe_nonneg, ht⟩
  have hinitAt : fderiv ℝ (fun q ↦ Φ (q, t₀)) p₀ = ContinuousLinearMap.id ℝ _ := hinit
  have hpair (t : ℝ) (ht : t ∈ I) (u w : E × (E →L[ℝ] ℝ)) :
      canonicalPhasePairing (fderiv ℝ (fun q ↦ Φ (q, t)) p₀ u)
        (fderiv ℝ (fun q ↦ Φ (q, t)) p₀ w) = canonicalPhasePairing u w := by
    have hb (δ : E × (E →L[ℝ] ℝ)) (s : ℝ) (hs : s ∈ I) :=
      hasDerivWithinAt_hamiltonianFlowVariation_blocks he hL hG (htarg s hs) (hraw δ s hs)
    have h := hamiltonian_pairing_eq_on_Icc
      (t₀ := t₀) (by constructor <;> linarith : t₀ ∈ Ioo (t₀ - T) (t₀ + T))
      (fun s hs ↦ (hb u s hs).1) (fun s hs ↦ (hb u s hs).2)
      (fun s hs ↦ (hb w s hs).1) (fun s hs ↦ (hb w s hs).2)
      (fun s hs ↦ localHamiltonianBlockA_symm he hL hG (htarg s hs))
      (fun s hs ↦ localHamiltonianBlockC_symm he hL hG (htarg s hs)) t ht
    simpa only [canonicalPhasePairing, flowPositionVariation, flowMomentumVariation,
      hinitAt, ContinuousLinearMap.id_apply] using h
  have hchain (t : ℝ) (ht : t ∈ I) :
      Z t = (fderiv ℝ (fun q ↦ Φ (q, t)) p₀).comp (fderiv ℝ seed w₀) := by
    have hd : DifferentiableAt ℝ (fun q ↦ Φ (q, t)) (seed w₀) := hseed.symm ▸ hdiff t ht
    exact (hd.hasFDerivAt.comp w₀ hdseed.differentiableAt.hasFDerivAt).fderiv.trans
      (by rw [hseed])
  have hprop : ∀ t ∈ I,
      DifferentiableAt ℝ (fun w ↦ Φ (seed w, t)) w₀ ∧
      Function.Injective (Z t) ∧
      (∀ u w : W, canonicalPhasePairing (Z t u) (Z t w) = 0) ∧
      ∀ u : W, HasDerivWithinAt (fun s ↦ Z s u)
        (fderiv ℝ (localHamiltonianVectorField L e) (Φ (p₀, t)) (Z t u)) I t := by
    intro t ht
    have hd : DifferentiableAt ℝ (fun q ↦ Φ (q, t)) (seed w₀) := hseed.symm ▸ hdiff t ht
    refine ⟨hd.comp w₀ hdseed.differentiableAt, ?_, ?_, ?_⟩
    · rw [hchain t ht]
      exact (injective_of_canonicalPhasePairing_preserved _ (hpair t ht)).comp hseedprop.1
    · intro u w
      rw [hchain t ht]
      exact (hpair t ht _ _).trans (hseedprop.2 u w)
    · intro u
      rw [hchain t ht]
      exact (hraw (fderiv ℝ seed w₀ u) t ht).congr_of_mem
        (fun s hs ↦ by rw [hchain s hs]; rfl) ht
  have hn := hF.momentum_eq_zero_of_constantEnergy_seed x₀ hseed hnormal he hsub hG
    hT hflow hmap hnear (fun t ht ↦ (hprop t ht).1)
    (fun t ht ↦ (hprop t ht).2.2.2)
  refine ⟨e, U, v, a, r, T, Φ, he, hzs, hsub, hG, hU, hwU, hUV, hv, ha, hv₀, ha₀,
    hdata, hr, hT, hflow, hmap, hnear, ?_, ?_⟩
  · change Z t₀ = fderiv ℝ seed w₀
    rw [hchain t₀ (by constructor <;> linarith), hinitAt]
    rfl
  · intro t ht
    obtain ⟨hd, hinj, hp, hvar⟩ := hprop t ht
    refine ⟨hd, hinj, hp, hvar, ?_⟩
    intro u
    change fiberLegendre L (e.symm (Φ (p₀, t))) (Z t u).1 = 0
    rw [(parametricLegendre_inverse_components he (htarg t ht)).2]
    exact hn t ht u

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
