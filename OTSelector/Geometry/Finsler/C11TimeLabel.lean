import OTSelector.Geometry.CalibratedLevelCylinder
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11LevelCoordinates
import OTSelector.Geometry.Finsler.C11VolumeTranslation
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
import OTSelector.MeasureTheory.HaarLipschitzDistortion
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11TimeLabel

* **Conditions:** The actual original contact-core level section and its complete covector-generated curves.
* **Objects:** A jointly Lipschitz injective calibrated time–label map with exact normalized Haar area formula.
* **Proof detail:** Use actual potential clock to recover time, short-time fixed-label injectivity to recover labels, then apply the ordinary derivative area theorem.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26): Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11TimeLabel.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11TimeLabel`; the selected original proof blocks follow. -/
section

/-!
# Original calibrated time-label coordinates and exact volume

The original C1,1 potential extension supplies a level section. Its actual initial
covectors generate complete original geodesics, whose short coordinate readout is
jointly Lipschitz. The original potential recovers time on the measured seed cylinder;
fixed-time injectivity then recovers the label. Exact change of variables uses the
ordinary derivative of this same map, with its parameter Haar normalization retained.
-/

open Set Metric Manifold MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- A compact calibrated contact core supplies actual time-level coordinates, injective
on the measured seed cylinder, with exact original volume for every measurable subpiece.
Neither saturation of the core nor injectivity off that cylinder is required. -/
theorem exists_C11_calibrated_timeLabel (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [m.IsAddHaarMeasure]
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instTimeLabelLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instTimeLabelPartners : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ)
    {x₀ : E} (hx₀ : x₀ ∈ K) :
    let _instTimeLabelResult : MetricSpace M := F.metricSpace
    let W := (fderiv ℝ G x₀).ker
    ∃ (r τ a : ℝ) (Γ : E → ℝ → M) (σ : W → E)
      (ℓ : (ℝ × W) ≃L[ℝ] E) (C : ℝ≥0),
      0 < r ∧ 0 < τ ∧ 0 < a ∧ τ ≤ δ / 2 ∧ σ 0 = x₀ ∧
      ContDiffOn ℝ 1 σ (ball 0 a) ∧ HasFDerivAt σ W.subtypeL 0 ∧
      MapsTo σ (ball 0 a) (ball x₀ r) ∧ InjOn σ (ball 0 a) ∧
      (∀ w ∈ ball 0 a, G (σ w) = G x₀) ∧
      (∀ w ∈ ball 0 a,
        Γ (σ w) 0 = (extChartAt 𝓘(ℝ, E) old).symm (σ w) ∧
        F.IsEulerLagrangeOn (Γ (σ w)) univ ∧
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (Γ (σ w)) ∧
        F.chartMomentumFamily old Γ (σ w, 0) = (σ w, fderiv ℝ G (σ w))) ∧
      let U := Ioo (-τ) τ ×ˢ ball (0 : W) a
      let D := Ioo (-τ) τ ×ˢ (ball (0 : W) a ∩ σ ⁻¹' K)
      let X := fun q : ℝ × W ↦ extChartAt 𝓘(ℝ, E) old (Γ (σ q.2) q.1)
      IsOpen U ∧ MeasurableSet D ∧ D ⊆ U ∧ LipschitzOnWith C X U ∧ InjOn X D ∧
      (∀ q ∈ U, Γ (σ q.2) q.1 ∈ (extChartAt 𝓘(ℝ, E) old).source) ∧
      (∀ q ∈ D, u ((extChartAt 𝓘(ℝ, E) old).symm (X q)) =
        u ((extChartAt 𝓘(ℝ, E) old).symm x₀) + q.1) ∧
      ∀ s : Set (ℝ × W), MeasurableSet s → s ⊆ D → ∀ g : E → ℝ≥0∞,
        (∫⁻ y in X '' s, g y ∂m) =
          ∫⁻ q in s, ENNReal.ofReal (parameterizedJacobian X ℓ q) * g (X q)
            ∂(tubeParameterMeasure ℓ m) := by
  let _instTimeLabelMetric : MetricSpace M := F.metricSpace
  obtain ⟨r, τ, Γ, hr, hτ, hτδ, hball, hinit, hcont, ⟨C₀, hjoint⟩, hflow, hcore⟩ :=
    hF.exists_C11_calibrated_volume_translation_lipschitz hcomplete old m hKt hu hG
      hLip hmatch hδ hpartners hx₀
  obtain ⟨hp, e, hxe, hsource, he, hei, hex, hfirst, hfirstK, hsection, hdim,
      hB, h0B, hσ, hσ0, himage⟩ :=
    hF.exists_original_levelCoordinates_of_calibrated_core hcomplete old hKt hu hG
      hval hmatch hδ hpartners hx₀
  let W := (fderiv ℝ G x₀).ker
  let σ : W → E := fun w ↦ e.symm (G x₀, w)
  let B : Set W := {w | (G x₀, w) ∈ e.target}
  let ψ : E → ℝ := u ∘ (extChartAt 𝓘(ℝ, E) old).symm
  let T : ℝ × E → E := fun q ↦ extChartAt 𝓘(ℝ, E) old (Γ q.2 q.1)
  have hσinj : InjOn σ B := by
    intro v hv w hw h
    exact congrArg Prod.snd (e.symm.injOn hv hw h)
  have hGlevel : ∀ w ∈ B, G (σ w) = G x₀ := by
    intro w hw
    simpa only [hfirst] using congrArg Prod.fst (e.right_inv hw)
  have hlevel : ∀ w ∈ B, σ w ∈ K → ψ (σ w) = ψ x₀ := by
    intro w hw hwK
    exact (hval hwK).symm.trans ((hGlevel w hw).trans (hval hx₀))
  have hfixed : ∀ t ∈ Icc (-τ) τ,
      InjOn (fun x ↦ T (t, x)) (closedBall x₀ r) := by
    intro t ht
    exact injOn_iff_injective.mpr
      (antilipschitzWith_of_half_lipschitz_displacement (hflow t ht).2.1).injective
  have hclock : ∀ t ∈ Icc (-τ) τ, ∀ x ∈ K ∩ closedBall x₀ r,
      ψ (T (t, x)) = ψ x + t := by
    intro t ht x hx
    have htδ : t ∈ Icc (-δ) δ := by
      constructor <;> linarith [ht.1, ht.2]
    change u ((extChartAt 𝓘(ℝ, E) old).symm
      (extChartAt 𝓘(ℝ, E) old (Γ x t))) = _
    rw [(extChartAt 𝓘(ℝ, E) old).left_inv ((hflow t ht).1 hx.2)]
    exact ((hcore x hx).2.2.1 t htδ).1
  obtain ⟨a, C, ha, haB, hmap, hXlip, hXclock, hXinj, hD, hDU⟩ :=
    exists_calibrated_levelCylinder hB h0B hσ hσ0 hσinj hK.isClosed hr
      hjoint hfixed hclock hlevel
  have hdim' : Module.finrank ℝ (ℝ × W) = Module.finrank ℝ E := by
    simpa [Module.finrank_prod, add_comm] using hdim
  let ℓ : (ℝ × W) ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hdim'
  refine ⟨r, τ, a, Γ, σ, ℓ, C, hr, hτ, ha, hτδ, hσ0, hσ.mono haB, hsection,
    hmap, hσinj.mono haB, fun w hw ↦ hGlevel w (haB hw), ?_,
    isOpen_Ioo.prod isOpen_ball, hD, hDU, hXlip, hXinj, ?_, hXclock, ?_⟩
  · intro w hw
    exact hinit (σ w) (ball_subset_closedBall (hmap hw))
  · intro q hq
    exact (hflow q.1 ⟨hq.1.1.le, hq.1.2.le⟩).1
      (ball_subset_closedBall (hmap hq.2))
  · intro s hs hsD g
    exact lintegral_image_parameterizedJacobian m ℓ (isOpen_Ioo.prod isOpen_ball)
      hXlip (hXinj.mono hsD) hs (hsD.trans hDU) g

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
