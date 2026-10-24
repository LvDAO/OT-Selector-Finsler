import OTSelector.Analysis.Calculus.GraphVelocityPhase
import OTSelector.Analysis.Convex.Legendre.Graph
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Hamiltonian.GraphDynamics
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.GraphMomentum
import OTSelector.Geometry.Finsler.GraphPhaseStructure
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.C2Variation
import OTSelector.Geometry.Finsler.Hamiltonian.Graph
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.PotentialGraphJacobi
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Manifold.CurveGraphRegularDomain
import OTSelector.Geometry.Symplectic.PotentialConormal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialGraphStructure.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialGraphStructure`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.PotentialGraphStructure

* **Conditions:** Smooth normalized potential-normal data and its actual graph and Legendre constructions.
* **Objects:** A smaller graph neighborhood where the same central graph parameter derivative is injective and isotropic.
* **Proof detail:** Derive common energy and normality from the original seed/flow and apply the actual graph-phase rank transfer after shrinking.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=253): Section 8.4, pp. 242–243, equations (8.53)–(8.58): canonical coordinate changes and preservation of the symplectic two-form.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Actual graph phase rank and isotropy of the same potential normal family

The normalized potential normal family retains its original Legendre branch, seed,
flow, graph inverse and graph Legendre branch. A smaller open graph neighborhood
adds injectivity and zero canonical pairing of the actual graph parameter derivative
along the central label. Common energy and speed follow from the original flow;
the new rank and pairing are conclusions, not additional family hypotheses.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ W] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M] {F : ContinuousFinslerNorm (ℝ × V) M}

/-- The same genuine potential normal family has its actual reduced Jacobi system,
with injective isotropic graph parameter derivative along its central label. -/
theorem exists_potentialNormal_graphStructure (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {f : (ℝ × V) → ℝ} {σ : W → ℝ × V} {Ω : Set (ℝ × V)}
    {B₀ : Set W} {w₀ : W} {c : ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hB₀ : IsOpen B₀) (hw₀ : w₀ ∈ B₀)
    (hσ : ContDiffOn ℝ ∞ σ B₀) (hσΩ : MapsTo σ B₀ Ω)
    (hlevel : (fun w ↦ f (σ w)) =ᶠ[𝓝 w₀] fun _ ↦ c)
    (himm : Function.Injective (fderiv ℝ σ w₀))
    {v₀ : ℝ × V} (hz : (σ w₀, v₀) ∈ chartEnergyDomain x₀)
    (hmatch : fderiv ℝ f (σ w₀) = fiberLegendre (F.chartEnergy x₀) (σ w₀, v₀))
    (hpositive : 0 < v₀.1) (t₀ : ℝ) :
    let L₀ := F.chartEnergy x₀
    let z₀ := (σ w₀, v₀)
    let p₀ := parametricLegendre L₀ z₀
    ∃ (ℓ : OpenPartialHomeomorph ((ℝ × V) × (ℝ × V))
        ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)))
      (B : Set W) (v : W → ℝ × V) (a : W → ℝ) (r : ℝ≥0) (T : ℝ)
      (Φ : ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)) × ℝ →
        (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)),
      let seed := potentialConormalState f σ a
      let Ψ := fun q : W × ℝ ↦ Φ (seed q.1, q.2)
      let γ := fun q ↦ (Ψ q).1
      let Z₀ := fun t ↦ fderiv ℝ (fun w ↦ Ψ (w, t)) w₀
      let q₀ := curveGraphCoordinateMap γ (w₀, t₀)
      let L := F.chartGraphLagrangian x₀
      (ℓ : ((ℝ × V) × (ℝ × V)) → ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))) =
        parametricLegendre L₀ ∧
      z₀ ∈ ℓ.source ∧ ℓ.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ ℓ.symm ℓ.target ∧ IsOpen B ∧ w₀ ∈ B ∧ B ⊆ B₀ ∧
      ContDiffOn ℝ ∞ v B ∧ ContDiffOn ℝ ∞ a B ∧ v w₀ = v₀ ∧ a w₀ = 1 ∧
      ContDiffOn ℝ ∞ seed B ∧ seed w₀ = p₀ ∧
      (∀ w ∈ B, (σ w, v w) ∈ ℓ.source ∧ 0 < a w ∧
        L₀ (σ w, v w) = L₀ z₀ ∧
        fiberLegendre L₀ (σ w, v w) = a w • fderiv ℝ f (σ w) ∧
        ℓ.symm (seed w) = (σ w, v w) ∧ seed w ∈ closedBall p₀ r) ∧
      0 < r ∧ 0 < T ∧
      LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L₀ ℓ)
        t₀ p₀ r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) ℓ.target ∧
      ContDiffOn ℝ 2 Ψ (B ×ˢ Ioo (t₀ - T) (t₀ + T)) ∧
      Z₀ t₀ = fderiv ℝ seed w₀ ∧
      (∀ t ∈ Icc (t₀ - T) (t₀ + T),
        DifferentiableAt ℝ (fun w ↦ Ψ (w, t)) w₀ ∧ Function.Injective (Z₀ t) ∧
        (∀ u w : W, canonicalPhasePairing (Z₀ t u) (Z₀ t w) = 0) ∧
        (∀ u : W, HasDerivWithinAt (fun s ↦ Z₀ s u)
          (fderiv ℝ (localHamiltonianVectorField L₀ ℓ) (Φ (p₀, t)) (Z₀ t u))
          (Icc (t₀ - T) (t₀ + T)) t) ∧
        ∀ u : W, (Z₀ t u).1 ∈ (fiberLegendre L₀ (ℓ.symm (Φ (p₀, t)))).ker) ∧
      ∃ (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ))
        (g : OpenPartialHomeomorph ((ℝ × V) × V) ((ℝ × V) × (V →L[ℝ] ℝ)))
        (D : Set (W × ℝ)),
        (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ ∧
        (w₀, t₀) ∈ e.source ∧ e.source ⊆ B ×ˢ Ioo (t₀ - T) (t₀ + T) ∧
        (g : ((ℝ × V) × V) → ((ℝ × V) × (V →L[ℝ] ℝ))) = parametricLegendre L ∧
        g.source ⊆ (extChartAt 𝓘(ℝ, ℝ × V) x₀).target ×ˢ univ ∧
        ContDiffOn ℝ ∞ g.symm g.target ∧ IsOpen D ∧ q₀ ∈ D ∧ D ⊆ e.target ∧
        ContDiffOn ℝ 2 (F.chartGraphPhase x₀ γ e) D ∧
        (∀ q ∈ D,
          let P := F.chartGraphPhase x₀ γ e
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
          ∀ p : V →L[ℝ] ℝ, p ≠ 0 → 0 < p (C p) ) ∧
        ∃ Q : Set (W × ℝ), IsOpen Q ∧ q₀ ∈ Q ∧ Q ⊆ D ∧
          ∀ q ∈ Q, q.1 = w₀ →
            let P := F.chartGraphPhase x₀ γ e
            let R := fderiv ℝ (fun w ↦ P (w, q.2)) q.1
            Function.Injective R ∧ ∀ u w : W, canonicalPhasePairing (R u) (R w) = 0 := by
  let L₀ := F.chartEnergy x₀
  let z₀ := (σ w₀, v₀)
  let p₀ := parametricLegendre L₀ z₀
  obtain ⟨ℓ, B, v, a, r, T, Φ, hℓ, hzs, hsub, hℓi, hB, hwB, hBB₀,
    hv, ha, hv₀, ha₀, hseed, hseed₀, hdata, hr, hT, hflow, hmap,
    hΨ, hinit, hvar, e, g, D, he, hzes, hesub, hg, hgsub, hgi,
    hD, hqD, hDsub, hPC2, hgraph⟩ :=
    hF.exists_potentialNormal_graphJacobi
      x₀ hΩ hf hB₀ hw₀ hσ hσΩ hlevel himm hz hmatch hpositive t₀
  let seed := potentialConormalState f σ a
  let Ψ := fun q : W × ℝ ↦ Φ (seed q.1, q.2)
  let γ := fun q : W × ℝ ↦ (Ψ q).1
  let q₀ := curveGraphCoordinateMap γ (w₀, t₀)
  change seed w₀ = p₀ at hseed₀
  have hmem : MapsTo seed B (closedBall p₀ r) := fun w hw ↦ (hdata w hw).2.2.2.2.2
  have hΨmap : MapsTo Ψ (B ×ˢ Ioo (t₀ - T) (t₀ + T)) ℓ.target :=
    fun q hq ↦ hmap ⟨hmem hq.1, Ioo_subset_Icc_self hq.2⟩
  have hODE : ∀ w ∈ B, ∀ t ∈ Ioo (t₀ - T) (t₀ + T),
      HasDerivAt (fun s ↦ Ψ (w, s))
        (localHamiltonianVectorField L₀ ℓ (Ψ (w, t))) t :=
    fun w hw t ht ↦ hasDerivAt_hamiltonianFlow_slice hflow (hmem hw) ht
  have ht₀ : t₀ ∈ Ioo (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  have henergy : ∀ w ∈ B, F.chartEnergy x₀ (ℓ.symm (Ψ (w, t₀))) =
      F.chartEnergy x₀ z₀ := by
    intro w hw
    change L₀ (ℓ.symm (Φ (seed w, t₀))) = L₀ z₀
    rw [hflow.apply_initial (seed w) (hmem hw), (hdata w hw).2.2.2.2.1]
    exact (hdata w hw).2.2.1
  have hcenter : Ψ (w₀, t₀) = p₀ := by
    change Φ (seed w₀, t₀) = p₀
    rw [hseed₀]
    exact hflow.apply_initial p₀ (mem_closedBall_self r.coe_nonneg)
  have hinv : ℓ.symm p₀ = z₀ := by
    rw [show p₀ = ℓ z₀ by rw [hℓ]]
    exact ℓ.left_inv hzs
  have hvelocity : fderiv ℝ γ (w₀, t₀) (0, 1) = v₀ := by
    have hγ₂ : ContDiffAt ℝ 2 γ (w₀, t₀) :=
      hΨ.fst.contDiffAt ((hB.prod isOpen_Ioo).mem_nhds
        (show (w₀, t₀) ∈ B ×ˢ Ioo (t₀ - T) (t₀ + T) from ⟨hwB, ht₀⟩))
    have hγa := hγ₂.differentiableAt (by norm_num)
    have hd := hγa.hasFDerivAt.comp_hasDerivAt t₀
      ((hasDerivAt_const t₀ w₀).prodMk (hasDerivAt_id t₀))
    have heq := hd.unique (hasDerivAt_hamiltonian_position (hODE w₀ hwB t₀ ht₀))
    simpa only [hcenter, hinv] using heq
  have heq₀ : e.symm q₀ = (w₀, t₀) := by
    change e.symm (curveGraphCoordinateMap γ (w₀, t₀)) = (w₀, t₀)
    rw [← he]
    exact e.left_inv hzes
  have hpositive' : 0 < (fderiv ℝ γ (e.symm q₀) (0, 1)).1 := by
    rw [heq₀, hvelocity]
    exact hpositive
  let Q := D ∩ {q | 0 < (fderiv ℝ γ (e.symm q) (0, 1)).1}
  obtain ⟨hQ, hqQ, hQD, hpos, hi⟩ := curveGraph_regular_domain he
    (hB.prod isOpen_Ioo) hesub hΨ.fst hD hDsub hqD hpositive'
  refine ⟨ℓ, B, v, a, r, T, Φ, hℓ, hzs, hsub, hℓi, hB, hwB, hBB₀,
    hv, ha, hv₀, ha₀, hseed, hseed₀, hdata, hr, hT, hflow, hmap,
    hΨ, hinit, hvar, e, g, D, he, hzes, hesub, hg, hgsub, hgi,
    hD, hqD, hDsub, hPC2, hgraph, Q, hQ, hqQ, hQD, ?_⟩
  intro q hq hlabel
  let z := e.symm q
  have hqt : q ∈ e.target := hDsub (hQD hq)
  have hzm : z ∈ B ×ˢ Ioo (t₀ - T) (t₀ + T) := hesub (e.map_target hqt)
  have hzlabel : z.1 = w₀ := (curveGraph_inverse_components he hqt).1.trans hlabel
  have hzcc : z.2 ∈ Icc (t₀ - T) (t₀ + T) := Ioo_subset_Icc_self hzm.2
  obtain ⟨_, hinj, hpair, _, hnormal⟩ := hvar z.2 hzcc
  have hphase : Ψ z = Φ (p₀, z.2) := by
    change Φ (seed z.1, z.2) = Φ (p₀, z.2)
    rw [hzlabel, hseed₀]
  have hnorm (u : W) : (Ψ z).2
      (fderiv ℝ (fun w ↦ Ψ (w, z.2)) z.1 u).1 = 0 := by
    have hu := hnormal u
    change fiberLegendre L₀ (ℓ.symm (Φ (p₀, z.2)))
      (fderiv ℝ (fun w ↦ Ψ (w, z.2)) w₀ u).1 = 0 at hu
    rw [← hphase, (parametricLegendre_inverse_components hℓ (hΨmap hzm)).2] at hu
    simpa only [hzlabel] using hu
  apply hF.chartGraphPhase_rank_pairing x₀ hℓ hsub hℓi hB isOpen_Ioo
    isPreconnected_Ioo hΨ hΨmap hODE ht₀ henergy he hesub hQ
    (hQD.trans hDsub) hi hpos hq
  · change Function.Injective (fderiv ℝ (fun w ↦ Ψ (w, z.2)) z.1)
    rw [hzlabel]
    exact hinj
  · change ∀ u v : W, canonicalPhasePairing
      (fderiv ℝ (fun w ↦ Ψ (w, z.2)) z.1 u)
      (fderiv ℝ (fun w ↦ Ψ (w, z.2)) z.1 v) = 0
    rw [hzlabel]
    exact hpair
  · exact hnorm

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
