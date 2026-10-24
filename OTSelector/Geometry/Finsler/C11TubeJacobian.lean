import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11PotentialTube
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Manifold.ManifoldFlowTimePotential
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian

/-!
# Geometry.Finsler.C11TubeJacobian

* **Conditions:** The selected actual smooth tube family and its dimension-matched time/kernel parameter space.
* **Objects:** A positive actual chart Jacobian and exact Haar change of variables with the full linear normalization in the reference measure.
* **Proof detail:** Choose the linear normalization once for the retained family, use invertibility of the true tube derivative and apply manifold-chart area change of variables.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26): Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22): Theorem 263A, pp. 22–24: linear change of variables and absolute determinant.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).

Source relation (derived): The tube inverse time is not identified with the original potential away from the center.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11TubeJacobian.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11TubeJacobian`; the selected original proof blocks follow. -/
section

/-!
# Actual Jacobians of the selected Finsler tubes

The retained dimension identity supplies a linear normalization of the time-level
parameters. One retained family is chosen before the compact time set. Every
resulting smooth calibrated tube has a positive chart Jacobian and the exact Haar
change-of-variables formula, with the normalization kept in the parameter measure.
This does not identify its inverse time with the original potential off the center.
-/

open Set MeasureTheory Manifold Bundle
open scoped ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [MeasurableSpace E] [BorelSpace E]
  {F : ContinuousFinslerNorm E M} (m : Measure E) [m.IsAddHaarMeasure]

/-- The already constructed family has actual positive coordinate Jacobians and an
exact change-of-variables formula on every legal output-chart overlap. -/
theorem exists_C11_tube_jacobian {old : M} {u : M → ℝ} {G : E → ℝ}
    {A : E → ℝ → M} {δ : ℝ} {x : E}
    (hx : F.HasC11SmoothTubeFamilyAt old u G A δ x) :
    ∃ (ℓ : (ℝ × (fderiv ℝ G x).ker) ≃L[ℝ] E)
        (Γ : (fderiv ℝ G x).ker → ℝ → M),
      A x = Γ 0 ∧ ∀ J : Set ℝ, IsCompact J → J ⊆ Ioo (-δ) δ →
      ∃ (T : Set ℝ) (V : Set (fderiv ℝ G x).ker)
          (e : OpenPartialHomeomorph (ℝ × (fderiv ℝ G x).ker) M),
        IsOpen T ∧ IsOpen V ∧ J ⊆ T ∧ (0 : (fderiv ℝ G x).ker) ∈ V ∧
        e.source = T ×ˢ V ∧
        (e : ℝ × (fderiv ℝ G x).ker → M) = (fun q ↦ Γ q.2 q.1) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × (fderiv ℝ G x).ker) 𝓘(ℝ, E) ∞ e e.source ∧
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × (fderiv ℝ G x).ker) ∞ e.symm e.target ∧
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (manifoldFlowTimePotential e 1 0) e.target ∧
        (∀ y ∈ e.target, ∀ z : TangentSpace 𝓘(ℝ, E) y,
          @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential e 1 0) y z)
            (F.toFun ⟨y, z⟩ : ℝ)) ∧
        (∀ q ∈ e.source, manifoldFlowTimePotential e 1 0 (Γ q.2 q.1) = q.1) ∧
        ∀ chart : M,
          ContinuousOn (manifoldTubeJacobian e ℓ chart)
            (e.source ∩ e ⁻¹' (chartAt E chart).source) ∧
          (∀ q ∈ e.source ∩ e ⁻¹' (chartAt E chart).source,
            0 < manifoldTubeJacobian e ℓ chart q) ∧
          (∀ K : Set (ℝ × (fderiv ℝ G x).ker), IsCompact K →
            K ⊆ e.source ∩ e ⁻¹' (chartAt E chart).source →
            ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
              ∀ q ∈ K, a ≤ manifoldTubeJacobian e ℓ chart q ∧
                manifoldTubeJacobian e ℓ chart q ≤ b) ∧
          ∀ s : Set (ℝ × (fderiv ℝ G x).ker), MeasurableSet s →
            s ⊆ e.source ∩ e ⁻¹' (chartAt E chart).source → ∀ g : E → ℝ≥0∞,
            (∫⁻ z in (chartAt E chart) '' (e '' s), g z ∂m) =
              ∫⁻ q in s, ENNReal.ofReal (manifoldTubeJacobian e ℓ chart q) *
                g ((chartAt E chart) (e q)) ∂(tubeParameterMeasure ℓ m) := by
  obtain ⟨_, hdim, P, _, _, _, _, B, σ, Γ, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hcenter, _, _, htube⟩ := hx
  have hdim' : Module.finrank ℝ (ℝ × (fderiv ℝ G x).ker) = Module.finrank ℝ E := by
    simpa [Module.finrank_prod, add_comm] using hdim
  let ℓ : (ℝ × (fderiv ℝ G x).ker) ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hdim'
  refine ⟨ℓ, Γ, hcenter, ?_⟩
  intro J hJ hJδ
  obtain ⟨T, V, e, hT, hV, hJT, h0V, _, he, hsource, _, hY, hi, hΦ, hcal, hclock⟩ :=
    htube J hJ hJδ
  refine ⟨T, V, e, hT, hV, hJT, h0V, hsource, he, hY, hi, hΦ, hcal,
    fun q hq ↦ (hclock q hq).1, ?_⟩
  intro chart
  have hY1 := hY.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  have hi1 := hi.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp)
  exact ⟨continuousOn_manifoldTubeJacobian e ℓ chart hY1,
    fun q hq ↦ manifoldTubeJacobian_pos e ℓ chart hY1 hi1 hq,
    fun K hK hKD ↦ exists_manifoldTubeJacobian_bounds e ℓ chart hY1 hi1 hK hKD,
    fun s hs hsD g ↦ lintegral_image_manifoldTubeJacobian m e ℓ chart hY1 hs hsD g⟩

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
