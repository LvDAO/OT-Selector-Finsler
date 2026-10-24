import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11VolumeTranslation
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.MeasureTheory.FlowScalarAbsoluteContinuity
import OTSelector.MeasureTheory.LocalJointAbsoluteContinuity
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11ScalarAbsoluteContinuity

* **Conditions:** An actual compact C1,1 contact core, ordered measurable geometric labels and an original coordinate population absolutely continuous to Haar.
* **Objects:** Absolute continuity of its original label–potential law relative to its own label marginal times Lebesgue measure.
* **Proof detail:** Extend coordinate labels only from the legal target, use actual calibrated short translations and lower Haar image bounds, and apply the null-section Fubini criterion.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38): Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11ScalarAbsoluteContinuity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11ScalarAbsoluteContinuity`; the selected original proof blocks follow. -/
section

/-!
# Scalar absolute continuity on actual compact C1,1 contact cores

Actual short geodesic translations of a compact contact core give absolute continuity
of its original label-potential law, for every coordinate population absolutely continuous
with respect to Haar measure. Coordinate functions are extended measurably only from
the legal chart target, then the final law is identified with the original pullbacks.
-/

open Set Filter Metric Manifold MeasureTheory MeasureTheory.Measure Classical
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    [PreconnectedSpace M] in
private theorem measurable_chartPullback_patch (old : M) {f : M → Z}
    (hf : Measurable f) (z : Z) :
    Measurable (fun x : E ↦ if x ∈ (extChartAt 𝓘(ℝ, E) old).target
      then f ((extChartAt 𝓘(ℝ, E) old).symm x) else z) := by
  classical
  have hi : Measurable (fun x : (extChartAt 𝓘(ℝ, E) old).target ↦
      (extChartAt 𝓘(ℝ, E) old).symm x.val) :=
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_extChartAt_symm old)).measurable
  exact (hf.comp hi).dite measurable_const
    (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) old).measurableSet

/-- Original one-Lipschitz calibration and a genuine C1,1 contact core construct scalar
absolute continuity on the whole core. The label is only required to be measurable and
invariant on calibrated interior pairs. No flow or image-volume estimate is an input. -/
theorem map_label_potential_absolutelyContinuous_on_C11_core (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m ν : Measure E) [IsAddHaarMeasure m] (hν : ν ≪ m)
    {K : Set E} (hK : IsCompact K) (hKtarget : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instC11ScalarLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instC11ScalarPartners : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ b c : M,
        dist b ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u b = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) c = δ ∧
        u c - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ)
    {a : M → Z} (ha : Measurable a)
    (hinv : let _instC11ScalarInvariant : MetricSpace M := F.metricSpace
      ∀ x ∈ calibratedInterior u, ∀ y ∈ calibratedInterior u,
        |u y - u x| = dist x y → a y = a x) :
    (ν.restrict K).map (fun x ↦
      (a ((extChartAt 𝓘(ℝ, E) old).symm x), u ((extChartAt 𝓘(ℝ, E) old).symm x))) ≪
      ((ν.restrict K).map (a ∘ (extChartAt 𝓘(ℝ, E) old).symm)).prod volume := by
  classical
  let _instC11ScalarMetric : MetricSpace M := F.metricSpace
  let χ := extChartAt 𝓘(ℝ, E) old
  let ac : E → Z := fun x ↦ if x ∈ χ.target then a (χ.symm x) else a old
  let uc : E → ℝ := fun x ↦ if x ∈ χ.target then u (χ.symm x) else 0
  have hac : Measurable ac := measurable_chartPullback_patch old ha (a old)
  have huc : Measurable uc := measurable_chartPullback_patch old hu.continuous.measurable 0
  have hactual : ∀ x ∈ K, ac x = a (χ.symm x) ∧ uc x = u (χ.symm x) := by
    intro x hx
    have hxt : x ∈ χ.target := hKtarget hx
    simp [ac, uc, hxt]
  have hcore : ∀ x ∈ K, χ.symm x ∈ calibratedInterior u := by
    intro x hx
    obtain ⟨b, c, hbx, hb, hxc, hc⟩ := hpartners x hx
    exact ⟨⟨b, dist_pos.mp (hbx.symm ▸ hδ), hb.trans hbx.symm⟩,
      ⟨c, dist_pos.mp (hxc.symm ▸ hδ), hc.trans hxc.symm⟩⟩
  have hlocal : ∀ x₀ ∈ K, ∃ r : ℝ, 0 < r ∧
      ((ν.restrict (K ∩ closedBall x₀ r)).map (fun x ↦ (ac x, uc x))) ≪
        ((ν.restrict (K ∩ closedBall x₀ r)).map ac).prod volume := by
    intro x₀ hx₀
    obtain ⟨r, τ, Γ, hr, hτ, hτhalf, hball, hinit, hcont, hflow, hcal⟩ :=
      hF.exists_C11_calibrated_volume_translation hcomplete old m hKtarget hu
        hG hLip hmatch hδ hpartners hx₀
    have htime : Icc (-τ) τ ⊆ Icc (-δ) δ := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hIpos : volume (Icc (-τ) τ) ≠ 0 := by
      rw [Real.volume_Icc]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
    refine ⟨r, hr, ?_⟩
    apply OTSelector.Reconstruction.map_label_clock_absolutelyContinuous_of_half_lipschitz_flow
      m ν hν (hK.inter_right isClosed_closedBall) inter_subset_right isCompact_Icc
      hIpos hac huc (T := fun t x ↦ χ (Γ x t))
    · exact continuousOn_fst.prodMk
        (hcont.mono (fun q hq ↦ ⟨hq.1, hq.2.2⟩))
    · intro t ht
      exact (hflow t ht).2.1
    · intro t ht x hx
      have hs : Γ x t ∈ χ.source := (hflow t ht).1 hx.2
      have htgt : χ (Γ x t) ∈ χ.target := χ.mapsTo hs
      have hback : χ.symm (χ (Γ x t)) = Γ x t := χ.left_inv hs
      have hxt : x ∈ χ.target := hKtarget hx.1
      simp only [ac, ite_eq_left htgt, ite_eq_left hxt, hback]
      exact hinv _ (hcore x hx.1) _ ((hcal x hx).2.2.2 t ht).1
        ((hcal x hx).2.2.1 t (htime ht)).2
    · intro t ht x hx
      have hs : Γ x t ∈ χ.source := (hflow t ht).1 hx.2
      have htgt : χ (Γ x t) ∈ χ.target := χ.mapsTo hs
      have hback : χ.symm (χ (Γ x t)) = Γ x t := χ.left_inv hs
      have hxt : x ∈ χ.target := hKtarget hx.1
      simp only [uc, ite_eq_left htgt, ite_eq_left hxt, hback]
      exact ((hcal x hx).2.2.1 t (htime ht)).1
  have hresult := OTSelector.Reconstruction.map_label_clock_absolutelyContinuous_of_compact_local
    ν hac huc hK hlocal
  have hpair : (fun x ↦ (ac x, uc x)) =ᵐ[ν.restrict K]
      (fun x ↦ (a (χ.symm x), u (χ.symm x))) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact Prod.ext (hactual x hx).1 (hactual x hx).2
  have hlabel : ac =ᵐ[ν.restrict K] (a ∘ χ.symm) := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact (hactual x hx).1
  rw [Measure.map_congr hpair, Measure.map_congr hlabel] at hresult
  exact hresult

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
