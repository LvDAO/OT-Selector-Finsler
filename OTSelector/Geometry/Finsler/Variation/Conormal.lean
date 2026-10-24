import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Coordinates.NormalData
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.Jacobi.VariationalFlow
import OTSelector.Geometry.Finsler.LegendreInjectivity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerConormalVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerConormalVariation`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Variation.Conormal

* **Conditions:** Actual smooth strongly convex Finsler data and nonzero phase; the generic seed uses a differentiable scalar and a fixed covector kernel.
* **Objects:** An affine conormal initial state and its injective isotropic derivative, propagated by the actual local phase flow.
* **Proof detail:** Differentiate the affine seed, use kernel annihilation for zero canonical pairing, then compose with the invertible symplectic flow derivative.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=253): Section 8.4, pp. 242–243, equations (8.53)–(8.58): canonical coordinate changes and preservation of the symplectic two-form.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Conormal seeds and phase pairing are constructed locally; reduced distance Hessians and arbitrary potential-level second jets are not identified.
-/

/-!
# Actual conormal initial-state variations

Constant-energy normal data provide initial covectors that are scalar multiples of
the actual central momentum. Restricting initial positions to its kernel gives an
injective, zero-pairing initial derivative. The chain rule and the actual Finsler
flow pairing theorem propagate both properties to the actual initial-state derivative
of the composed flow. No zero Wronskian or initial rank is imposed as a geometric
hypothesis. Distance Hessians and the reduced transverse system are not identified here.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Initial phase with affine positions in the momentum kernel and scaled covectors. -/
def conormalInitialState (p : E →L[ℝ] ℝ) (x : E) (a : p.ker → ℝ)
    (w : p.ker) : E × (E →L[ℝ] ℝ) := (x + (w : E), a w • p)

/-- Differentiating the actual conormal initial phase leaves the base inclusion unchanged. -/
theorem hasFDerivAt_conormalInitialState (p : E →L[ℝ] ℝ) (x : E)
    {a : p.ker → ℝ} {w : p.ker} (ha : DifferentiableAt ℝ a w) :
    HasFDerivAt (conormalInitialState p x a)
      (p.ker.subtypeL.prod ((fderiv ℝ a w).smulRight p)) w :=
  (p.ker.subtypeL.hasFDerivAt.const_add x).prodMk (ha.hasFDerivAt.smul_const p)

/-- The actual derivative of a conormal seed is injective and has zero canonical pairing. -/
theorem conormalInitialState_fderiv_properties (p : E →L[ℝ] ℝ) (x : E)
    {a : p.ker → ℝ} {w : p.ker} (ha : DifferentiableAt ℝ a w) :
    Function.Injective (fderiv ℝ (conormalInitialState p x a) w) ∧
      ∀ u v : p.ker,
        canonicalPhasePairing (fderiv ℝ (conormalInitialState p x a) w u)
          (fderiv ℝ (conormalInitialState p x a) w v) = 0 := by
  rw [(hasFDerivAt_conormalInitialState p x ha).fderiv]
  constructor
  · intro u v huv
    exact Subtype.ext (congrArg Prod.fst huv)
  · intro u v
    have hu : p (u : E) = 0 := u.property
    have hv : p (v : E) = 0 := v.property
    simp [canonicalPhasePairing, hu, hv]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  {F : ContinuousFinslerNorm E M}

/-- The kernel of an actual nonzero Finsler momentum has codimension one. -/
theorem finrank_chartMomentum_ker (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) :
    Module.finrank ℝ (fiberLegendre (F.chartEnergy x₀) z).ker + 1 =
      Module.finrank ℝ E := by
  apply Module.Dual.finrank_ker_add_one_of_ne_zero
  intro hzero
  have hval := congrArg (fun q : E →ₗ[ℝ] ℝ ↦ q z.2) hzero
  have hpos : 0 < fiberLegendre (F.chartEnergy x₀) z z.2 := by
    rw [hF.chartEnergy_euler x₀ hz]
    exact mul_pos (by norm_num) (F.chartEnergy_pos x₀ hz)
  exact (ne_of_gt hpos) hval

/-- Original Finsler data construct actual conormal variations with zero pairing and
full phase rank throughout a local closed time interval. The initial constant energy,
nonzero velocity and momentum scaling are derived rather than assumed. -/
theorem exists_chartHamiltonian_conormalVariation (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {z : E × E} (hz : z ∈ chartEnergyDomain x₀) (t₀ : ℝ) :
    let L := F.chartEnergy x₀
    let p := fiberLegendre L z
    let p₀ := parametricLegendre L z
    ∃ (a : p.ker → ℝ)
      (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)))
      (r : ℝ≥0) (T : ℝ) (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ)),
      let ι := conormalInitialState p z.1 a
      a 0 = 1 ∧ ContDiffAt ℝ ∞ a 0 ∧
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ e.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧ 0 < r ∧ 0 < T ∧
      LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
        t₀ p₀ r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target ∧
      (∀ᶠ w in 𝓝 (0 : p.ker), ι w ∈ closedBall p₀ r ∧
        L (e.symm (ι w)) = L z ∧ 0 < a w ∧
        ∃ v : E, (z.1 + (w : E), v) ∈ chartEnergyDomain x₀ ∧
          L (z.1 + (w : E), v) = L z ∧
          fiberLegendre L (z.1 + (w : E), v) = a w • p) ∧
      (∀ (δ : E × (E →L[ℝ] ℝ)) (t : ℝ), t ∈ Icc (t₀ - T) (t₀ + T) →
        HasDerivWithinAt (fun s ↦ fderiv ℝ (fun q ↦ Φ (q, s)) p₀ δ)
          (fderiv ℝ (localHamiltonianVectorField L e) (Φ (p₀, t))
            (fderiv ℝ (fun q ↦ Φ (q, t)) p₀ δ)) (Icc (t₀ - T) (t₀ + T)) t) ∧
      ∀ t ∈ Icc (t₀ - T) (t₀ + T),
        DifferentiableAt ℝ (fun w ↦ Φ (ι w, t)) 0 ∧
        Function.Injective (fderiv ℝ (fun w ↦ Φ (ι w, t)) 0) ∧
        ∀ u v : p.ker,
          canonicalPhasePairing (fderiv ℝ (fun w ↦ Φ (ι w, t)) 0 u)
            (fderiv ℝ (fun w ↦ Φ (ι w, t)) 0 v) = 0 := by
  let L := F.chartEnergy x₀
  let p := fiberLegendre L z
  let p₀ := parametricLegendre L z
  obtain ⟨U, v, a₀, hU, hzU, _, ha₀, _, ha₀z, _, hnormal⟩ :=
    hF.exists_constantEnergy_normalData x₀ hz
  obtain ⟨e, r, T, Φ, he, hzs, hsub, hG, hr, hT, hflow, hmap,
    hdiff, hinit, _, hvar, hblocks⟩ := hF.exists_chartHamiltonian_variationalFlow x₀ hz t₀
  have hraw (δ : E × (E →L[ℝ] ℝ)) (t : ℝ) (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
      HasDerivWithinAt (fun s ↦ fderiv ℝ (fun q ↦ Φ (q, s)) p₀ δ)
        (fderiv ℝ (localHamiltonianVectorField L e) (Φ (p₀, t))
          (fderiv ℝ (fun q ↦ Φ (q, t)) p₀ δ)) (Icc (t₀ - T) (t₀ + T)) t := by
    have htarg : Φ (p₀, t) ∈ e.target := hmap ⟨mem_closedBall_self r.coe_nonneg, ht⟩
    rw [localHamiltonianVectorField_linearized_blocks he
      ((hF.contDiffOn_chartEnergy x₀).mono hsub) hG htarg]
    exact (hvar δ t ht).1.prodMk (hvar δ t ht).2
  have hpair : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ∀ u v : E × (E →L[ℝ] ℝ),
      canonicalPhasePairing (fderiv ℝ (fun q ↦ Φ (q, t)) p₀ u)
        (fderiv ℝ (fun q ↦ Φ (q, t)) p₀ v) = canonicalPhasePairing u v := by
    intro t ht u v
    have h := hamiltonian_pairing_eq_on_Icc
      (t₀ := t₀) (by constructor <;> linarith : t₀ ∈ Ioo (t₀ - T) (t₀ + T))
      (fun s hs ↦ (hvar u s hs).1) (fun s hs ↦ (hvar u s hs).2)
      (fun s hs ↦ (hvar v s hs).1) (fun s hs ↦ (hvar v s hs).2)
      (fun s hs ↦ (hblocks s hs).2.1) (fun s hs ↦ (hblocks s hs).2.2.1) t ht
    simpa only [canonicalPhasePairing, flowPositionVariation, flowMomentumVariation,
      hinit, ContinuousLinearMap.id_apply] using h
  let β : p.ker → E := fun w ↦ z.1 + (w : E)
  let a : p.ker → ℝ := a₀ ∘ β
  let ι := conormalInitialState p z.1 a
  have hβ : ContDiff ℝ ∞ β := contDiff_const.add p.ker.subtypeL.contDiff
  have hβ₀ : β 0 = z.1 := by simp [β]
  have ha : ContDiffAt ℝ ∞ a 0 := by
    have hAt : ContDiffAt ℝ ∞ a₀ (β 0) := by
      rw [hβ₀]
      exact ha₀.contDiffAt (hU.mem_nhds hzU)
    exact hAt.comp 0 hβ.contDiffAt
  have haz : a 0 = 1 := by simpa only [a, Function.comp_apply, hβ₀] using ha₀z
  have hi : DifferentiableAt ℝ ι 0 :=
    (hasFDerivAt_conormalInitialState p z.1 (ha.differentiableAt (by simp))).differentiableAt
  have hi₀ : ι 0 = p₀ := by
    simp only [ι, conormalInitialState, ZeroMemClass.coe_zero, add_zero, haz, one_smul]
    rfl
  have hiprop := conormalInitialState_fderiv_properties p z.1
    (ha.differentiableAt (by simp))
  have hnearU : ∀ᶠ w in 𝓝 (0 : p.ker), β w ∈ U :=
    hβ.continuous.continuousAt.preimage_mem_nhds (by rw [hβ₀]; exact hU.mem_nhds hzU)
  have hnearBall : ∀ᶠ w in 𝓝 (0 : p.ker), ι w ∈ closedBall p₀ r := by
    apply Filter.Eventually.mono (hi.continuousAt.preimage_mem_nhds
      (by rw [hi₀]; exact Metric.ball_mem_nhds _ hr))
    intro w hw
    exact ball_subset_closedBall hw
  refine ⟨a, e, r, T, Φ, haz, ha, he, hzs, hsub, hG, hr, hT, hflow, hmap, ?_, hraw, ?_⟩
  · filter_upwards [hnearU, hnearBall] with w hw hb
    have hn := hnormal (β w) hw
    have htarget : ι w ∈ e.target := by
      have h : Φ (ι w, t₀) ∈ e.target :=
        hmap ⟨hb, (by constructor <;> linarith : t₀ ∈ Icc (t₀ - T) (t₀ + T))⟩
      rwa [hflow.apply_initial _ hb] at h
    have hinverse : e.symm (ι w) = (β w, v (β w)) := by
      apply hF.injOn_parametricLegendre_chartEnergy x₀
        (hsub (e.map_target htarget)) hn.1
      calc
        parametricLegendre L (e.symm (ι w)) = ι w := by
          rw [← he]
          exact e.right_inv htarget
        _ = parametricLegendre L (β w, v (β w)) := by
          apply Prod.ext
          · rfl
          · exact hn.2.2.2.symm
    refine ⟨hb, ?_, hn.2.1, v (β w), hn.1, hn.2.2.1, hn.2.2.2⟩
    rw [hinverse]
    exact hn.2.2.1
  · intro t ht
    have hd : DifferentiableAt ℝ (fun q ↦ Φ (q, t)) (ι 0) := by
      rw [hi₀]
      exact hdiff t ht
    have hchain : fderiv ℝ (fun w ↦ Φ (ι w, t)) 0 =
        (fderiv ℝ (fun q ↦ Φ (q, t)) p₀).comp (fderiv ℝ ι 0) := by
      rw [← hi₀]
      exact (hd.hasFDerivAt.comp 0 hi.hasFDerivAt).fderiv
    refine ⟨hd.comp 0 hi, ?_, ?_⟩
    · rw [hchain]
      exact (injective_of_canonicalPhasePairing_preserved _ (hpair t ht)).comp hiprop.1
    · intro u w
      rw [hchain]
      exact (hpair t ht _ _).trans (hiprop.2 u w)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
