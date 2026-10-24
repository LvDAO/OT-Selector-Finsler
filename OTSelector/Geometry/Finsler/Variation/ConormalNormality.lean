import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
import OTSelector.Analysis.ODE.Hamiltonian.RectangularCoordinates
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.C2Variation
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.Hamiltonian.NormalVariation
import OTSelector.Geometry.Finsler.Jacobi.Conormal
import OTSelector.Geometry.Finsler.Variation.Conormal
import OTSelector.Geometry.Finsler.Variation.Lagrangian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerConormalNormality.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerConormalNormality`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Variation.ConormalNormality

* **Conditions:** A constant-energy affine conormal seed carried by the specified genuine local Finsler Hamiltonian flow and actual variational equation.
* **Objects:** Momentum normality of the actual position variation at every time of the closed local interval.
* **Proof detail:** Differentiate the seed energy identity and the momentum–position pairing, show the latter has zero time derivative, and use its zero initial value and endpoint continuity.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).

Source relation (derived): Normality is derived for this constructed affine seed; no arbitrary rough potential level is substituted.
-/

/-!
# Normality of actual conormal Finsler flow variations

Constant original energy of the same initial family propagates under its actual flow.
Differentiating this equality in the initial parameter, and using the actual linearized
field equation, makes the momentum-position-variation pairing stationary. Its initial
value is zero by the affine conormal seed. Continuity includes both closed time endpoints.
No joint C2 family, independently selected flow, or normality premise is used.
The affine initial hypersurface and its scaled fixed covectors describe this constructed
family; no arbitrary transport-potential level set or its second-order initial data is identified.
-/

open Set Filter Metric Manifold Matrix Module
open scoped Topology ContDiff NNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The actual same-flow conormal derivative is annihilated by the central momentum.
The regularity and variational inputs here are supplied by the conormal Jacobi constructor. -/
theorem conormalFlowDerivative_momentum_eq_zero (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {z : E × E}
    {a : (fiberLegendre (F.chartEnergy x₀) z).ker → ℝ} (ha0 : a 0 = 1)
    (ha : DifferentiableAt ℝ a 0)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀))
    (hsource : e.source ⊆ chartEnergyDomain x₀) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {r : ℝ≥0} {t₀ T : ℝ} (hT : 0 < T)
    (hflow : LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField (F.chartEnergy x₀) e)
      t₀ (parametricLegendre (F.chartEnergy x₀) z) r (t₀ - T) (t₀ + T) Φ)
    (hmap : MapsTo Φ
      (closedBall (parametricLegendre (F.chartEnergy x₀) z) r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target)
    (hnear : ∀ᶠ w in 𝓝 (0 : (fiberLegendre (F.chartEnergy x₀) z).ker),
      conormalInitialState (fiberLegendre (F.chartEnergy x₀) z) z.1 a w ∈
        closedBall (parametricLegendre (F.chartEnergy x₀) z) r ∧
      F.chartEnergy x₀ (e.symm (conormalInitialState (fiberLegendre (F.chartEnergy x₀) z) z.1 a w)) =
        F.chartEnergy x₀ z)
    (hdiff : ∀ t ∈ Icc (t₀ - T) (t₀ + T), DifferentiableAt ℝ
      (fun w ↦ Φ (conormalInitialState (fiberLegendre (F.chartEnergy x₀) z) z.1 a w, t)) 0)
    (hvar : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ∀ u,
      HasDerivWithinAt
        (fun s ↦ conormalFlowDerivative Φ (fiberLegendre (F.chartEnergy x₀) z) z.1 a s u)
        (fderiv ℝ (localHamiltonianVectorField (F.chartEnergy x₀) e)
          (Φ (parametricLegendre (F.chartEnergy x₀) z, t))
          (conormalFlowDerivative Φ (fiberLegendre (F.chartEnergy x₀) z) z.1 a t u))
        (Icc (t₀ - T) (t₀ + T)) t) :
    ∀ t ∈ Icc (t₀ - T) (t₀ + T), ∀ u,
      (Φ (parametricLegendre (F.chartEnergy x₀) z, t)).2
        (conormalFlowDerivative Φ (fiberLegendre (F.chartEnergy x₀) z) z.1 a t u).1 = 0 := by
  let L := F.chartEnergy x₀
  let p := fiberLegendre L z
  let p₀ := parametricLegendre L z
  let seed := conormalInitialState p z.1 a
  let Z := conormalFlowDerivative Φ p z.1 a
  let γ := fun t ↦ Φ (p₀, t)
  let I := Icc (t₀ - T) (t₀ + T)
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_chartEnergy x₀).mono hsource
  have hseed0 : seed 0 = p₀ := by
    simp only [seed, conormalInitialState, ZeroMemClass.coe_zero, add_zero, ha0, one_smul]
    rfl
  have hp₀ : p₀ ∈ closedBall p₀ r := mem_closedBall_self r.coe_nonneg
  have htarg (t : ℝ) (ht : t ∈ I) : γ t ∈ e.target := hmap ⟨hp₀, ht⟩
  have hγ (t : ℝ) (ht : t ∈ I) :
      HasDerivWithinAt γ (localHamiltonianVectorField L e (γ t)) I t :=
    hflow.hasDerivWithinAt p₀ hp₀ t ht
  have henergy (t : ℝ) (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) :
      (fun w ↦ L (e.symm (Φ (seed w, t)))) =ᶠ[𝓝 (0 : p.ker)] (fun _ ↦ L z) := by
    filter_upwards [hnear] with w hw
    have h := hF.chartEnergy_hamiltonianPositionVariation_eq_initial x₀ he hsource hG
      (ι := fun _ : ℝ ↦ seed w) (s := 0) hflow hmap hT hw.1 ht
    rw [variationPhase_hamiltonianPositionVariation he hflow hmap hw.1 ht] at h
    exact h.trans hw.2
  have henergyD (t : ℝ) (ht : t ∈ Ioo (t₀ - T) (t₀ + T)) (u : p.ker) :
      fderiv ℝ L (e.symm (γ t)) (fderiv ℝ e.symm (γ t) (Z t u)) = 0 := by
    have ht' : t ∈ I := Ioo_subset_Icc_self ht
    have hdG := ((hG.contDiffAt (e.open_target.mem_nhds (htarg t ht'))).differentiableAt
      (by simp)).hasFDerivAt
    have hdL := ((hL.contDiffAt (e.open_source.mem_nhds (e.map_target (htarg t ht')))).differentiableAt
      (by simp)).hasFDerivAt
    change HasFDerivAt e.symm (fderiv ℝ e.symm (Φ (p₀, t))) (Φ (p₀, t)) at hdG
    change HasFDerivAt L (fderiv ℝ L (e.symm (Φ (p₀, t)))) (e.symm (Φ (p₀, t))) at hdL
    rw [← hseed0] at hdG hdL
    have hd := hdL.comp 0 (hdG.comp 0 (hdiff t ht').hasFDerivAt)
    have hc : HasFDerivAt (fun w ↦ L (e.symm (Φ (seed w, t)))) 0 (0 : p.ker) :=
      (hasFDerivAt_const (𝕜 := ℝ) (L z) (0 : p.ker)).congr_of_eventuallyEq (henergy t ht)
    have heq := congrArg (fun D : p.ker →L[ℝ] ℝ ↦ D u) (hd.unique hc)
    simpa only [hseed0, ContinuousLinearMap.comp_apply, _root_.zero_apply,
      γ, Z, conormalFlowDerivative, p, L] using heq
  intro t ht u
  let W : ℝ → ℝ := fun s ↦ (γ s).2 (Z s u).1
  have hdW (s : ℝ) (hs : s ∈ I) :
      HasDerivWithinAt W
        (baseEnergyDifferential L (e.symm (γ s)) (Z s u).1 +
          (γ s).2 (fderiv ℝ e.symm (γ s) (Z s u)).2) I s := by
    have hP : HasDerivWithinAt (fun v ↦ (γ v).2)
        (baseEnergyDifferential L (e.symm (γ s))) I s := (hγ s hs).snd
    have hJ : HasDerivWithinAt (fun v ↦ (Z v u).1)
        (fderiv ℝ (localHamiltonianVectorField L e) (γ s) (Z s u)).1 I s := (hvar s hs u).fst
    rw [localHamiltonianVectorField_fderiv_fst hL hG (htarg s hs)] at hJ
    exact hP.clm_apply hJ
  have hzeroD (s : ℝ) (hs : s ∈ Ioo (t₀ - T) (t₀ + T)) : HasDerivAt W 0 s := by
    have hs' : s ∈ I := Ioo_subset_Icc_self hs
    have hGs := (hG.contDiffAt (e.open_target.mem_nhds (htarg s hs'))).differentiableAt (by simp)
    have hLs := (hL.contDiffAt (e.open_source.mem_nhds (e.map_target (htarg s hs')))).differentiableAt
      (by simp)
    have hfst : (fderiv ℝ e.symm (γ s) (Z s u)).1 = (Z s u).1 :=
      congrArg (fun D : (E × (E →L[ℝ] ℝ)) →L[ℝ] E ↦ D (Z s u))
        (parametricLegendre_inverse_derivative_fst he (htarg s hs') hGs.hasFDerivAt)
    have heq := henergyD s hs u
    rw [← Prod.eta (fderiv ℝ e.symm (γ s) (Z s u)), fderiv_energy_split hLs,
      hfst, (parametricLegendre_inverse_components he (htarg s hs')).2] at heq
    rw [← heq]
    exact (hdW s hs').hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hinit : (fun w ↦ Φ (seed w, t₀)) =ᶠ[𝓝 (0 : p.ker)] seed := by
    filter_upwards [hnear] with w hw
    exact hflow.apply_initial (seed w) hw.1
  have hJ0 : (Z t₀ u).1 = (u : E) := by
    change (fderiv ℝ (fun w ↦ Φ (seed w, t₀)) 0 u).1 = _
    rw [hinit.fderiv_eq, (hasFDerivAt_conormalInitialState p z.1 ha).fderiv]
    rfl
  have hW0 : W t₀ = 0 := by
    change (Φ (p₀, t₀)).2 (Z t₀ u).1 = 0
    rw [hflow.apply_initial p₀ hp₀, hJ0]
    exact u.property
  have hinner : EqOn W (fun _ ↦ 0) (Ioo (t₀ - T) (t₀ + T)) := by
    intro s hs
    exact (isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo _ _).isPreconnected
      (fun v hv ↦ (hzeroD v hv).differentiableAt.differentiableWithinAt)
      (fun v hv ↦ (hzeroD v hv).deriv) hs
      (show t₀ ∈ Ioo (t₀ - T) (t₀ + T) by constructor <;> linarith)).trans hW0
  exact hinner.of_subset_closure (fun s hs ↦ (hdW s hs).continuousWithinAt)
    continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo (show t₀ - T ≠ t₀ + T by linarith)]) ht

variable [FiniteDimensional ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The same actual conormal Jacobi witness has normal position variations at every
closed-interval time, with all its original flow, energy, rank and matrix properties retained. -/
theorem exists_chartHamiltonian_conormalNormality (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) (t₀ : ℝ)
    (bE : Basis ι ℝ E) (bK : Basis κ ℝ (fiberLegendre (F.chartEnergy x₀) z).ker) :
    Fintype.card κ + 1 = Fintype.card ι ∧
    let L := F.chartEnergy x₀
    let p := fiberLegendre L z
    let p₀ := parametricLegendre L z
    ∃ (a : p.ker → ℝ)
      (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
      (r : ℝ≥0) (T : ℝ) (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)),
      let seed := conormalInitialState p z.1 a
      let Z := conormalFlowDerivative Φ p z.1 a
      let J := fun s ↦ vectorFamilyRectMatrix bE (fun j ↦ (Z s (bK j)).1)
      let P := fun s ↦ covectorFamilyRectMatrix bE (fun j ↦ (Z s (bK j)).2)
      let A := fun s ↦ hamiltonianMatrixA bE (localHamiltonianBlockA L e (Φ (p₀, s)))
      let B := fun s ↦ hamiltonianMatrixB bE (localHamiltonianBlockB L e (Φ (p₀, s)))
      let C := fun s ↦ hamiltonianMatrixC bE (localHamiltonianBlockC L e (Φ (p₀, s)))
      a 0 = 1 ∧ ContDiffAt ℝ ∞ a 0 ∧
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ e.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ 0 < r ∧ 0 < T ∧
      LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
        t₀ p₀ r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target ∧
      (∀ᶠ w in 𝓝 (0 : p.ker), seed w ∈ closedBall p₀ r ∧
        L (e.symm (seed w)) = L z ∧ 0 < a w ∧
        ∃ v : E, (z.1 + (w : E), v) ∈ chartEnergyDomain x₀ ∧
          L (z.1 + (w : E), v) = L z ∧
          fiberLegendre L (z.1 + (w : E), v) = a w • p) ∧
      ∀ t ∈ Icc (t₀ - T) (t₀ + T),
        DifferentiableAt ℝ (fun w ↦ Φ (seed w, t)) 0 ∧
        Function.Injective (Z t) ∧
        (∀ u : p.ker, HasDerivWithinAt (fun s ↦ Z s u)
          (fderiv ℝ (localHamiltonianVectorField L e) (Φ (p₀, t)) (Z t u))
          (Icc (t₀ - T) (t₀ + T)) t) ∧
        HasDerivWithinAt J (B t * J t + C t * P t) (Icc (t₀ - T) (t₀ + T)) t ∧
        HasDerivWithinAt P (-A t * J t - (B t)ᵀ * P t) (Icc (t₀ - T) (t₀ + T)) t ∧
        (J t)ᵀ * P t - (P t)ᵀ * J t = 0 ∧ (A t)ᵀ = A t ∧ (C t)ᵀ = C t ∧
        ∀ u : p.ker, (Z t u).1 ∈ (fiberLegendre L (e.symm (Φ (p₀, t)))).ker := by
  obtain ⟨hdim, a, e, r, T, Φ, ha0, ha, he, hzs, hsub, hG, hr, hT, hflow, hmap,
    hnear, hprop⟩ := hF.exists_chartHamiltonian_conormalJacobi x₀ hz t₀ bE bK
  have hn := hF.conormalFlowDerivative_momentum_eq_zero x₀ ha0
    (ha.differentiableAt (by simp)) he hsub hG hT hflow hmap
    (hnear.mono (fun _ hw ↦ ⟨hw.1, hw.2.1⟩))
    (fun t ht ↦ (hprop t ht).1) (fun t ht ↦ (hprop t ht).2.2.1)
  refine ⟨hdim, a, e, r, T, Φ, ha0, ha, he, hzs, hsub, hG, hr, hT, hflow, hmap, hnear, ?_⟩
  intro t ht
  obtain ⟨hd, hinj, hvar, hJ, hP, hW, hA, hC⟩ := hprop t ht
  refine ⟨hd, hinj, hvar, hJ, hP, hW, hA, hC, ?_⟩
  intro u
  change fiberLegendre (F.chartEnergy x₀)
    (e.symm (Φ (parametricLegendre (F.chartEnergy x₀) z, t))) _ = 0
  rw [(parametricLegendre_inverse_components he
    (hmap ⟨mem_closedBall_self r.coe_nonneg, ht⟩)).2]
  exact hn t ht u

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
