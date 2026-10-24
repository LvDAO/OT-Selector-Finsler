import OTSelector.Analysis.Calculus.GraphVelocityPhase
import OTSelector.Analysis.Convex.Legendre.Graph
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteChartBox
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.GraphMomentum
import OTSelector.Geometry.Finsler.GraphPhaseStructure
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Graph
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.RegraphedJacobi
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Manifold.CurveGraphRegularDomain

/-!
# Geometry.Finsler.CompleteRegraphedJacobi

* **Conditions:** A given complete C2 intrinsic family with common energy, phase rank, isotropy, Gauss normality and a positive longitudinal velocity in a legal product chart.
* **Objects:** An actual reduced graph Jacobi chart of that same complete family.
* **Proof detail:** Construct a genuine local Hamiltonian box, regraph the actual family and transfer its proved phase structure into the reduced variational blocks.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=253): Section 8.4, pp. 242–243, equations (8.53)–(8.58): canonical coordinate changes and preservation of the symplectic two-form.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCompleteRegraphedJacobi.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCompleteRegraphedJacobi`; the selected original proof blocks follow. -/
section

/-!
# Reduced Jacobi structure of the same complete intrinsic family

At an arbitrary time in a legal graph chart, construct a true Hamiltonian box for the
given complete family and reparameterize that very family. Its common original energy,
actual phase rank, canonical pairing and Gauss normality transfer to the actual reduced
Jacobi system. The local clock positivity here is a coordinate-domain input; selecting
adapted coordinates from a general nonzero velocity is handled separately.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {W V M : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ W] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [ChartedSpace (ℝ × V) M] [IsManifold 𝓘(ℝ, ℝ × V) ∞ M]
  {F : ContinuousFinslerNorm (ℝ × V) M}

/-- The actual graph inverse and original Legendre branch carry the reduced Jacobi system
and central phase structure. This package is constructed from the intrinsic family below. -/
def HasGraphJacobiChart (F : ContinuousFinslerNorm (ℝ × V) M)
    (Γ : W → ℝ → M) (B : Set W) (w₀ : W) (old : M) (t₀ : ℝ) : Prop :=
    let γ := fun q : W × ℝ ↦ extChartAt 𝓘(ℝ, ℝ × V) old (Γ q.1 q.2)
    let q₀ := curveGraphCoordinateMap γ (w₀, t₀)
    let L := F.chartGraphLagrangian old
    ∃ (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ))
      (g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)))
      (D : Set (W × ℝ)),
      (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ ∧
      (w₀, t₀) ∈ e.source ∧ e.source ⊆ B ×ˢ univ ∧
      (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
      g.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) old).target ×ˢ univ ∧
      ContDiffOn ℝ ∞ g.symm g.target ∧ IsOpen D ∧ q₀ ∈ D ∧ D ⊆ e.target ∧
      ContDiffOn ℝ 2 (F.chartGraphPhase old γ e) D ∧
      (∀ q ∈ D,
        let P := F.chartGraphPhase old γ e
        let A := GraphHamiltonian.blockA L g q.2 (P q)
        let B' := GraphHamiltonian.blockB L g q.2 (P q)
        let C := GraphHamiltonian.blockC L g q.2 (P q)
        graphVelocityPhase (fun p ↦ (curveGraphPosition γ e p).2) q ∈ g.source ∧
        HasDerivAt (fun s ↦ P (q.1, s)) (GraphHamiltonian.field L g q.2 (P q)) q.2 ∧
        (∀ ξ : W,
          let Z := fun s ↦ fderiv ℝ (fun w ↦ P (w, s)) q.1 ξ
          HasDerivAt (fun s ↦ (Z s).1) (B' (Z q.2).1 + C (Z q.2).2) q.2 ∧
          HasDerivAt (fun s ↦ (Z s).2) (-A (Z q.2).1 - (Z q.2).2.comp B') q.2) ∧
        (∀ u v, A u v = A v u) ∧
        (∀ p r : V →L[ℝ] ℝ, r (C p) = p (C r)) ∧
        C = ContinuousLinearMap.inverse
          (GraphLegendre.verticalHessian L (g.symm ((q.2, (P q).1), (P q).2))) ∧
        ∀ p : V →L[ℝ] ℝ, p ≠ 0 → 0 < p (C p)) ∧
      ∀ q ∈ D, q.1 = w₀ →
        let R := fderiv ℝ (fun w ↦ F.chartGraphPhase old γ e (w, q.2)) q.1
        Function.Injective R ∧ ∀ ξ η : W, canonicalPhasePairing (R ξ) (R η) = 0

namespace IsSmoothStronglyConvex

private theorem chartEnergy_actualPhase (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (old : M)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source) :
    F.chartEnergy old ((extChartAt 𝓘(ℝ, ℝ × V) old ∘ c) t,
      deriv (extChartAt 𝓘(ℝ, ℝ × V) old ∘ c) t) =
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × V) c ⟨t, (1 : ℝ)⟩) := by
  unfold ContinuousFinslerNorm.chartEnergy
  rw [← (hF.chartTangent_of_isEulerLagrangeAt hc old hx).1, (extChartAt _ _).left_inv]
  simpa only [FiberBundle.chartedSpace_chartAt, mfld_simps] using hx

/-- The same complete intrinsic normal family has genuine reduced Jacobi equations,
positive inverse block, central full reduced phase rank and zero pairing near any time. -/
theorem exists_completeFamily_chartGraphStructure (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, ℝ × V).prod 𝓘(ℝ, ℝ × V)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × V) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {C₀ : ℝ} (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × V) (Γ w) ⟨t, (1 : ℝ)⟩) = C₀)
    {w₀ : W} (hw : w₀ ∈ B)
    (hrank : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source →
      Function.Injective (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀))
    (hpair : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source →
      ∀ ξ η : W, canonicalPhasePairing
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ ξ)
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ η) = 0)
    (hnormal : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source →
      ∀ ξ : W, (F.chartMomentumFamily old Γ (w₀, t)).2
        (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, ℝ × V) old (Γ w t)) w₀ ξ) = 0)
    (old : M) (t₀ : ℝ) (hx : Γ w₀ t₀ ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source)
    (hpositive : 0 < (deriv (extChartAt 𝓘(ℝ, ℝ × V) old ∘ Γ w₀) t₀).1) :
    F.HasGraphJacobiChart Γ B w₀ old t₀ := by
  let Ψ := F.chartMomentumFamily old Γ
  let γ := fun q : W × ℝ ↦ extChartAt 𝓘(ℝ, ℝ × V) old (Γ q.1 q.2)
  let q₀ := curveGraphCoordinateMap γ (w₀, t₀)
  obtain ⟨ℓ, r, hℓ, hsub, hℓi, hr, hBr, hchart, hΨ, hmap, hlocal⟩ :=
    hF.exists_chartMomentumFamily_box hB hEL hG hw old t₀ hx
  have ht₀ : t₀ ∈ Ioo (t₀ - r) (t₀ + r) := by constructor <;> linarith
  have hw₀ : w₀ ∈ ball w₀ r := mem_ball_self hr
  have hz₀ : (w₀, t₀) ∈ ball w₀ r ×ˢ Ioo (t₀ - r) (t₀ + r) := ⟨hw₀, ht₀⟩
  have hODE (w : W) (hw' : w ∈ ball w₀ r) (t : ℝ)
      (ht : t ∈ Ioo (t₀ - r) (t₀ + r)) := (hlocal (w, t) ⟨hw', ht⟩).1
  have hγ : ContDiffOn ℝ 2 γ (ball w₀ r ×ˢ Ioo (t₀ - r) (t₀ + r)) := hΨ.fst
  have hγd := (hγ.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds hz₀)).differentiableAt
    (by norm_num)
  have hd := hγd.hasFDerivAt.comp_hasDerivAt t₀
    ((hasDerivAt_const t₀ w₀).prodMk (hasDerivAt_id t₀))
  have hvelocity : fderiv ℝ γ (w₀, t₀) (0, 1) =
      deriv (extChartAt 𝓘(ℝ, ℝ × V) old ∘ Γ w₀) t₀ := hd.deriv.symm
  have hpos₀ : 0 < (fderiv ℝ γ (w₀, t₀) (0, 1)).1 := by rwa [hvelocity]
  obtain ⟨e, g, D, he, hzes, hesub, hg, hgsub, hgi, hD, hqD, hDt, hPC2, hJacobi⟩ :=
    hF.exists_chartRegraphedJacobi old hℓ hsub hℓi isOpen_ball isOpen_Ioo
      isPreconnected_Ioo hΨ hmap hODE hz₀ hpos₀
  change (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ at he
  have heq₀ : e.symm q₀ = (w₀, t₀) := by
    change e.symm (curveGraphCoordinateMap γ (w₀, t₀)) = (w₀, t₀)
    rw [← he]
    exact e.left_inv hzes
  have hpos₁ : 0 < (fderiv ℝ γ (e.symm q₀) (0, 1)).1 := by rwa [heq₀]
  let Q := D ∩ {q | 0 < (fderiv ℝ γ (e.symm q) (0, 1)).1}
  obtain ⟨hQ, hqQ, hQD, hpos, hi⟩ := curveGraph_regular_domain he
    (isOpen_ball.prod isOpen_Ioo) hesub hγ hD hDt hqD hpos₁
  have heC (w : W) (hw' : w ∈ ball w₀ r) :
      F.chartEnergy old (ℓ.symm (Ψ (w, t₀))) = C₀ := by
    have hpw : Ψ (w, t₀) ∈ ℓ.target := hmap ⟨hw', ht₀⟩
    rw [hamiltonian_inverse_eq_position_deriv hℓ hpw (hODE w hw' t₀ ht₀)]
    exact (hF.chartEnergy_actualPhase (hEL w (hBr hw') t₀ (mem_univ _)) old
      (hchart (w, t₀) ⟨hw', ht₀⟩)).trans (henergy w (hBr hw') t₀)
  have heInitial (w : W) (hw' : w ∈ ball w₀ r) :
      F.chartEnergy old (ℓ.symm (Ψ (w, t₀))) =
        F.chartEnergy old (ℓ.symm (Ψ (w₀, t₀))) := (heC w hw').trans (heC w₀ hw₀).symm
  refine ⟨e, g, Q, he, hzes, ?_, hg, hgsub, hgi, hQ, hqQ, hQD.trans hDt,
    hPC2.mono hQD, (fun q hq ↦ hJacobi q (hQD hq)), ?_⟩
  · intro q hq
    exact ⟨hBr (hesub hq).1, mem_univ _⟩
  · intro q hq hlabel
    let z := e.symm q
    have hz : z ∈ ball w₀ r ×ˢ Ioo (t₀ - r) (t₀ + r) :=
      hesub (e.map_target (hDt (hQD hq)))
    have hzl : z.1 = w₀ := (curveGraph_inverse_components he (hDt (hQD hq))).1.trans hlabel
    have hx' : Γ w₀ z.2 ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source := by
      simpa only [hzl] using hchart z hz
    apply hF.chartGraphPhase_rank_pairing old hℓ hsub hℓi isOpen_ball isOpen_Ioo
      isPreconnected_Ioo hΨ hmap hODE ht₀ heInitial he hesub hQ (hQD.trans hDt) hi hpos hq
    · change Function.Injective (fderiv ℝ (fun w ↦ Ψ (w, z.2)) z.1)
      rw [hzl]
      exact hrank old z.2 hx'
    · change ∀ ξ η : W, canonicalPhasePairing
        (fderiv ℝ (fun w ↦ Ψ (w, z.2)) z.1 ξ)
        (fderiv ℝ (fun w ↦ Ψ (w, z.2)) z.1 η) = 0
      rw [hzl]
      exact hpair old z.2 hx'
    · intro ξ
      change (Ψ z).2 (fderiv ℝ (fun w ↦ Ψ (w, z.2)) z.1 ξ).1 = 0
      have hin : DifferentiableAt ℝ (fun w : W ↦ (w, z.2)) z.1 :=
        differentiableAt_id.prodMk (differentiableAt_const z.2)
      have hfull : DifferentiableAt ℝ Ψ z :=
        (hΨ.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds hz)).differentiableAt
          (by norm_num)
      have hds : DifferentiableAt ℝ (fun w ↦ Ψ (w, z.2)) z.1 := by
        apply DifferentiableAt.comp z.1 (g := Ψ)
        · exact hfull
        · exact hin
      have hfirst := congrArg (fun A ↦ A ξ) hds.hasFDerivAt.fst.fderiv
      change fderiv ℝ (fun w ↦ (Ψ (w, z.2)).1) z.1 ξ =
        (fderiv ℝ (fun w ↦ Ψ (w, z.2)) z.1 ξ).1 at hfirst
      rw [← hfirst]
      change (Ψ (z.1, z.2)).2
        (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, ℝ × V) old (Γ w z.2)) z.1 ξ) = 0
      rw [hzl]
      exact hnormal old z.2 hx' ξ

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
