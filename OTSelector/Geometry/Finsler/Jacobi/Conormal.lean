import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
import OTSelector.Analysis.ODE.Hamiltonian.RectangularCoordinates
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.Jacobi.VariationalFlow
import OTSelector.Geometry.Finsler.Variation.Conormal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerConormalJacobi.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerConormalJacobi`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Jacobi.Conormal

* **Conditions:** The same actual conormal flow witness, its variational equation and bases of the ambient space and momentum kernel.
* **Objects:** Rectangular d-by-(d−1) position/momentum Jacobi matrices, zero Wronskian and injective full phase derivative.
* **Proof detail:** Identify the actual derivative of the seeded flow by the chain rule, take its matrix coordinates and propagate pairing through the linearized Hamiltonian blocks.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=253): Section 8.4, pp. 242–243, equations (8.53)–(8.58): canonical coordinate changes and preservation of the symplectic two-form.

Source relation (derived): These are ambient rectangular equations; passing to a square transverse system or distance Hessian is separate.
-/

/-!
# Actual rectangular Jacobi equations of conormal Finsler variations

The same conormal-flow witness supplies the actual initial-state variational ODE.
Its initial identity and canonical pairing recover ambient differentiability, so the
chain rule identifies the derivative of the actual composed conormal family. Taking
any basis of the actual momentum kernel gives rectangular Jacobi matrices with zero
Wronskian and an injective full phase derivative. These are ambient d-by-q equations,
not a reduced q-by-q system or an identification with a distance Hessian.
-/

open Set Filter Metric Manifold Matrix Module
open scoped Topology ContDiff NNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual derivative in the conormal initial position of the composed phase flow. -/
def conormalFlowDerivative
    (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ))
    (p : E →L[ℝ] ℝ) (x : E) (a : p.ker → ℝ) (t : ℝ) :
    p.ker →L[ℝ] (E × (E →L[ℝ] ℝ)) :=
  fderiv ℝ (fun w ↦ Φ (conormalInitialState p x a w, t)) 0

private theorem differentiableAt_flow_of_variational_equation
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {p₀ : E × (E →L[ℝ] ℝ)} {r : ℝ≥0} {t₀ T : ℝ} (hr : 0 < r) (hT : 0 < T)
    (hflow : LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
      t₀ p₀ r (t₀ - T) (t₀ + T) Φ)
    (hmap : MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target)
    (hraw : ∀ δ t, t ∈ Icc (t₀ - T) (t₀ + T) →
      HasDerivWithinAt (fun s ↦ fderiv ℝ (fun q ↦ Φ (q, s)) p₀ δ)
        (fderiv ℝ (localHamiltonianVectorField L e) (Φ (p₀, t))
          (fderiv ℝ (fun q ↦ Φ (q, t)) p₀ δ)) (Icc (t₀ - T) (t₀ + T)) t) :
    ∀ t ∈ Icc (t₀ - T) (t₀ + T), DifferentiableAt ℝ (fun q ↦ Φ (q, t)) p₀ := by
  have hinitEq : (fun q ↦ Φ (q, t₀)) =ᶠ[𝓝 p₀] id := by
    filter_upwards [closedBall_mem_nhds p₀ (show (0 : ℝ) < r from hr)] with q hq
    exact hflow.apply_initial q hq
  have hinit : fderiv ℝ (fun q ↦ Φ (q, t₀)) p₀ = ContinuousLinearMap.id ℝ _ := by
    rw [hinitEq.fderiv_eq]
    exact fderiv_id
  have htarg (t : ℝ) (ht : t ∈ Icc (t₀ - T) (t₀ + T)) : Φ (p₀, t) ∈ e.target :=
    hmap ⟨mem_closedBall_self r.coe_nonneg, ht⟩
  have hb (δ : E × (E →L[ℝ] ℝ)) (t : ℝ) (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :=
    hasDerivWithinAt_hamiltonianFlowVariation_blocks he hL hG (htarg t ht) (hraw δ t ht)
  intro t ht
  apply differentiableAt_of_fderiv_injective
  apply injective_of_canonicalPhasePairing_preserved
  intro u v
  have h := hamiltonian_pairing_eq_on_Icc
    (t₀ := t₀) (by constructor <;> linarith : t₀ ∈ Ioo (t₀ - T) (t₀ + T))
    (fun s hs ↦ (hb u s hs).1) (fun s hs ↦ (hb u s hs).2)
    (fun s hs ↦ (hb v s hs).1) (fun s hs ↦ (hb v s hs).2)
    (fun s hs ↦ localHamiltonianBlockA_symm he hL hG (htarg s hs))
    (fun s hs ↦ localHamiltonianBlockC_symm he hL hG (htarg s hs)) t ht
  simpa only [canonicalPhasePairing, flowPositionVariation, flowMomentumVariation,
    hinit, ContinuousLinearMap.id_apply] using h

private theorem conormalFlowDerivative_eq_comp
    {Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)}
    {p : E →L[ℝ] ℝ} {x : E} {a : p.ker → ℝ} {p₀ : E × (E →L[ℝ] ℝ)} {t : ℝ}
    (ha : DifferentiableAt ℝ a 0) (hinit : conormalInitialState p x a 0 = p₀)
    (hΦ : DifferentiableAt ℝ (fun q ↦ Φ (q, t)) p₀) :
    conormalFlowDerivative Φ p x a t =
      (fderiv ℝ (fun q ↦ Φ (q, t)) p₀).comp
        (fderiv ℝ (conormalInitialState p x a) 0) := by
  have hi := (hasFDerivAt_conormalInitialState p x ha).differentiableAt
  have hd : DifferentiableAt ℝ (fun q ↦ Φ (q, t)) (conormalInitialState p x a 0) :=
    hinit.symm ▸ hΦ
  exact (hd.hasFDerivAt.comp 0 hi.hasFDerivAt).fderiv.trans (by rw [hinit])

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M ι κ : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E] [Fintype ι] [Fintype κ]
  {F : ContinuousFinslerNorm E M}

/-- Original Finsler data and arbitrary ambient/kernel bases construct actual rectangular
Jacobi matrices of a single conormal flow, with zero Wronskian and full phase rank. -/
theorem exists_chartHamiltonian_conormalJacobi (hF : F.IsSmoothStronglyConvex)
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
        (J t)ᵀ * P t - (P t)ᵀ * J t = 0 ∧ (A t)ᵀ = A t ∧ (C t)ᵀ = C t := by
  constructor
  · simpa only [Module.finrank_eq_card_basis bK, Module.finrank_eq_card_basis bE] using
      hF.finrank_chartMomentum_ker x₀ hz
  dsimp only
  let L := F.chartEnergy x₀
  let p := fiberLegendre L z
  let p₀ := parametricLegendre L z
  obtain ⟨a, e, r, T, Φ, ha0, ha, he, hzs, hsub, hG, hr, hT, hflow, hmap, hnear,
    hraw, hprop⟩ := hF.exists_chartHamiltonian_conormalVariation x₀ hz t₀
  let seed := conormalInitialState p z.1 a
  let Z := conormalFlowDerivative Φ p z.1 a
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_chartEnergy x₀).mono hsub
  have hdΦ := differentiableAt_flow_of_variational_equation he hL hG hr hT hflow hmap hraw
  have hseed : seed 0 = p₀ := by
    simp only [seed, conormalInitialState, ZeroMemClass.coe_zero, add_zero, ha0, one_smul]
    rfl
  have hchain (s : ℝ) (hs : s ∈ Icc (t₀ - T) (t₀ + T)) :
      Z s = (fderiv ℝ (fun q ↦ Φ (q, s)) p₀).comp (fderiv ℝ seed 0) :=
    conormalFlowDerivative_eq_comp (ha.differentiableAt (by simp)) hseed (hdΦ s hs)
  have hdZ (t : ℝ) (ht : t ∈ Icc (t₀ - T) (t₀ + T)) (u : p.ker) :
      HasDerivWithinAt (fun s ↦ Z s u)
        (fderiv ℝ (localHamiltonianVectorField L e) (Φ (p₀, t)) (Z t u))
        (Icc (t₀ - T) (t₀ + T)) t := by
    have heq (s : ℝ) (hs : s ∈ Icc (t₀ - T) (t₀ + T)) :
        Z s u = fderiv ℝ (fun q ↦ Φ (q, s)) p₀ (fderiv ℝ seed 0 u) := by
      rw [hchain s hs, ContinuousLinearMap.comp_apply]
    rw [heq t ht]
    exact (hraw (fderiv ℝ seed 0 u) t ht).congr_of_mem heq ht
  refine ⟨a, e, r, T, Φ, ha0, ha, he, hzs, hsub, hG, hr, hT, hflow, hmap, hnear, ?_⟩
  intro t ht
  have htarg : Φ (p₀, t) ∈ e.target := hmap ⟨mem_closedBall_self r.coe_nonneg, ht⟩
  have hblock (u : p.ker) :
      HasDerivWithinAt (fun s ↦ Z s u)
        (localHamiltonianBlockB L e (Φ (p₀, t)) (Z t u).1 +
            localHamiltonianBlockC L e (Φ (p₀, t)) (Z t u).2,
          -localHamiltonianBlockA L e (Φ (p₀, t)) (Z t u).1 -
            (Z t u).2.comp (localHamiltonianBlockB L e (Φ (p₀, t))))
        (Icc (t₀ - T) (t₀ + T)) t := by
    convert hdZ t ht u using 1
    exact (localHamiltonianVectorField_linearized_blocks he hL hG htarg _ _).symm
  have hmatrix := hasDerivWithinAt_hamiltonian_rectangular_matrices bE
    (J := fun j s ↦ (Z s (bK j)).1) (P := fun j s ↦ (Z s (bK j)).2)
    (A := localHamiltonianBlockA L e (Φ (p₀, t)))
    (B := localHamiltonianBlockB L e (Φ (p₀, t)))
    (C := localHamiltonianBlockC L e (Φ (p₀, t)))
    (I := Icc (t₀ - T) (t₀ + T)) (t := t)
    (fun j ↦ (hblock (bK j)).fst) (fun j ↦ (hblock (bK j)).snd)
  refine ⟨(hprop t ht).1, (hprop t ht).2.1, hdZ t ht, hmatrix.1, hmatrix.2, ?_,
    hamiltonianMatrixA_transpose bE (localHamiltonianBlockA_symm he hL hG htarg),
    hamiltonianMatrixC_transpose bE (localHamiltonianBlockC_symm he hL hG htarg)⟩
  ext i j
  rw [rectangular_wronskian_apply]
  exact (hprop t ht).2.2 (bK i) (bK j)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
