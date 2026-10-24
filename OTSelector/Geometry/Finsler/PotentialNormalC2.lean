import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Flow.SameFlowC2
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.PotentialNormalFlow
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Symplectic.PotentialConormal
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialNormalC2.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialNormalC2`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.PotentialNormalC2

* **Conditions:** Smooth immersed potential-level data with the prescribed actual central momentum in finite-dimensional Finsler geometry.
* **Objects:** Joint C2 regularity of the same normalized conormal phase family on a smaller parameter/time box, retaining rank, isotropy and normality.
* **Proof detail:** Shrink the existing flow box, apply joint smooth dependence and compose with its smooth normalized seed; restrict all previously proved identities to the smaller box.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Joint C2 regularity of the actual potential normal family

The existing normalized potential conormal flow is restricted, keeping its Legendre
branch, normalization, seed and flow function. The same flow is jointly C2 on an open
neighborhood of a smaller closed box, and its actual seeded phase is jointly C2.
The true variational equation, phase injectivity, zero pairing and momentum normality
remain valid on the smaller closed time interval.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The same normalized potential conormal flow has a genuine jointly C2 phase family.
Only the initial neighborhood and time interval shrink; all transported conclusions
refer to the same seed and flow as the constant-energy normalization. -/
theorem exists_chartHamiltonian_potentialNormalC2Flow [FiniteDimensional ℝ E]
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
      (Φ : (E × (E →L[ℝ] ℝ)) × ℝ → E × (E →L[ℝ] ℝ))
      (D : Set ((E × (E →L[ℝ] ℝ)) × ℝ)),
      let seed := potentialConormalState f σ a
      let Ψ := fun q : W × ℝ ↦ Φ (seed q.1, q.2)
      let Z := fun t ↦ fderiv ℝ (fun w ↦ Ψ (w, t)) w₀
      (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ e.source ⊆ chartEnergyDomain x₀ ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      IsOpen U ∧ w₀ ∈ U ∧ U ⊆ V ∧
      ContDiffOn ℝ ∞ v U ∧ ContDiffOn ℝ ∞ a U ∧ v w₀ = v₀ ∧ a w₀ = 1 ∧
      ContDiffOn ℝ ∞ seed U ∧ seed w₀ = p₀ ∧
      (∀ w ∈ U, (σ w, v w) ∈ e.source ∧ 0 < a w ∧
        L (σ w, v w) = L z ∧
        fiberLegendre L (σ w, v w) = a w • fderiv ℝ f (σ w) ∧
        e.symm (seed w) = (σ w, v w) ∧ seed w ∈ closedBall p₀ r) ∧
      0 < r ∧ 0 < T ∧
      LocalFlow.IsLocalFlow (fun _ ↦ localHamiltonianVectorField L e)
        t₀ p₀ r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T)) e.target ∧
      IsOpen D ∧ closedBall p₀ r ×ˢ Icc (t₀ - T) (t₀ + T) ⊆ D ∧
      ContDiffOn ℝ 2 Φ D ∧ ContDiffOn ℝ 2 Ψ (U ×ˢ Ioo (t₀ - T) (t₀ + T)) ∧
      Z t₀ = fderiv ℝ seed w₀ ∧
      ∀ t ∈ Icc (t₀ - T) (t₀ + T),
        DifferentiableAt ℝ (fun w ↦ Ψ (w, t)) w₀ ∧
        Function.Injective (Z t) ∧
        (∀ u w : W, canonicalPhasePairing (Z t u) (Z t w) = 0) ∧
        (∀ u : W, HasDerivWithinAt (fun s ↦ Z s u)
          (fderiv ℝ (localHamiltonianVectorField L e) (Φ (p₀, t)) (Z t u))
          (Icc (t₀ - T) (t₀ + T)) t) ∧
        ∀ u : W, (Z t u).1 ∈ (fiberLegendre L (e.symm (Φ (p₀, t)))).ker := by
  let L := F.chartEnergy x₀
  let z := (σ w₀, v₀)
  let p₀ := parametricLegendre L z
  obtain ⟨e, U, v, a, r, T, Φ, he, hzs, hsub, hG, hU, hwU, hUV,
    hv, ha, hv₀, ha₀, hdata, hr, hT, hflow, _, _, hinit, hvar⟩ :=
    hF.exists_chartHamiltonian_potentialNormalFlow
      x₀ hΩ hf hV hw₀ hσ hσΩ hlevel himm hz hmatch t₀
  let seed := potentialConormalState f σ a
  have hseed₀ : seed w₀ = p₀ := by
    change (σ w₀, a w₀ • fderiv ℝ f (σ w₀)) =
      (σ w₀, fiberLegendre (F.chartEnergy x₀) (σ w₀, v₀))
    rw [ha₀, one_smul, hmatch]
  have hq : ContDiffOn ℝ ∞ (fun w ↦ fderiv ℝ f (σ w)) V :=
    (hf.fderiv_of_isOpen hΩ (by simp : ∞ + 1 ≤ (∞ : ℕ∞ω))).comp hσ hσΩ
  have hs : ContDiffOn ℝ ∞ seed U := (hσ.mono hUV).prodMk (ha.smul (hq.mono hUV))
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_chartEnergy x₀).mono hsub
  have hp : p₀ ∈ e.target := by
    rw [show p₀ = e z by rw [he]]
    exact e.map_source hzs
  obtain ⟨r', T', D, hr', _, hT', hTle, hD, hbox, hflow', hmap', hC2⟩ :=
    hflow.exists_contDiffOn_C2_in_open hr hT e.open_target hp
      (contDiffOn_localHamiltonianVectorField hL hG)
  let U' := U ∩ seed ⁻¹' ball p₀ (r' : ℝ)
  have hU' : IsOpen U' := hs.continuousOn.isOpen_inter_preimage hU isOpen_ball
  have hwU' : w₀ ∈ U' := by
    refine ⟨hwU, ?_⟩
    change seed w₀ ∈ ball p₀ (r' : ℝ)
    rw [hseed₀]
    exact mem_ball_self hr'
  have hseedmem (w : W) (hw : w ∈ U') : seed w ∈ closedBall p₀ r' :=
    ball_subset_closedBall hw.2
  have hΨ : ContDiffOn ℝ 2 (fun q : W × ℝ ↦ Φ (seed q.1, q.2))
      (U' ×ˢ Ioo (t₀ - T') (t₀ + T')) := by
    have hseedfst : ContDiffOn ℝ 2 (fun q : W × ℝ ↦ seed q.1)
        (U' ×ˢ Ioo (t₀ - T') (t₀ + T')) :=
      ((hs.mono inter_subset_left).of_le (by simp : 2 ≤ ∞)).comp contDiffOn_fst
        (fun _ hq ↦ hq.1)
    exact hC2.comp (hseedfst.prodMk contDiffOn_snd)
      (fun q hq ↦ hbox ⟨hseedmem q.1 hq.1, Ioo_subset_Icc_self hq.2⟩)
  have htime : Icc (t₀ - T') (t₀ + T') ⊆ Icc (t₀ - T) (t₀ + T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨e, U', v, a, r', T', Φ, D, he, hzs, hsub, hG, hU', hwU',
    inter_subset_left.trans hUV, hv.mono inter_subset_left, ha.mono inter_subset_left,
    hv₀, ha₀, hs.mono inter_subset_left, hseed₀, ?_, hr', hT', hflow', hmap',
    hD, hbox, hC2, hΨ, hinit, ?_⟩
  · intro w hw
    obtain ⟨hwv, hwa, hwE, hwp, hwe⟩ := hdata w hw.1
    exact ⟨hwv, hwa, hwE, hwp, hwe, hseedmem w hw⟩
  · intro t ht
    obtain ⟨hd, hinj, hpair, hraw, hnormal⟩ := hvar t (htime ht)
    exact ⟨hd, hinj, hpair, fun u ↦ (hraw u).mono htime, hnormal⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
