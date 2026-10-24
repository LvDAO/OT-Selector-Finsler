import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FiniteTimeLipschitz
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Geometry.Finsler.C11TimeLabelLocalization

* **Conditions:** A C1 section of the original initial domain and its actual C1,1-momentum complete family.
* **Objects:** Local finite-time Lipschitz time–label chart readouts and one countable cover of the entire parameter domain.
* **Proof detail:** Compose the C1 section with the actual joint Lipschitz family readout near each point and extract a countable open cover.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=24): Sections 4A2G(e), pp. 15–16; 4A2N(b), p. 22; 4A2Q(h) and proof, pp. 24–25.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11TimeLabelLocalization.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11TimeLabelLocalization`; the selected original proof blocks follow. -/
section

/-!
# Local Lipschitz coordinates for original time–label maps

An actual C1 section of the original initial domain gives jointly Lipschitz
position readouts near every finite time and legal output chart. A countable
family of these constructed neighborhoods covers the entire time–label domain.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ W] in
/-- The actual time–label map obtained from a C1 section has a jointly Lipschitz
readout on a legal closed neighborhood of every finite time–label point. -/
theorem exists_lipschitz_timeLabel_chart_readout
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    {B : Set E} (hB : IsOpen B)
    (hBtarget : B ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {Γ : E → ℝ → M}
    (hEL : ∀ x ∈ B, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ B, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x)
    (hp : ∀ x ∈ B, F.chartMomentumFamily initial Γ (x, 0) = (x, fderiv ℝ G x))
    {V : Set W} (hV : IsOpen V) {σ : W → E} (hσ : ContDiffOn ℝ 1 σ V)
    (hσB : MapsTo σ V B) {q : ℝ × W} (hq : q ∈ univ ×ˢ V) (terminal : M)
    (hlegal : Γ (σ q.2) q.1 ∈ (extChartAt 𝓘(ℝ, E) terminal).source) :
    ∃ (r : ℝ) (C : ℝ≥0), 0 < r ∧ closedBall q r ⊆ univ ×ˢ V ∧
      MapsTo (fun p : ℝ × W ↦ Γ (σ p.2) p.1) (closedBall q r)
        (extChartAt 𝓘(ℝ, E) terminal).source ∧
      LipschitzOnWith C
        (fun p : ℝ × W ↦ extChartAt 𝓘(ℝ, E) terminal (Γ (σ p.2) p.1))
        (closedBall q r) := by
  obtain ⟨r₀, C₀, hr₀, _, hmap, hread⟩ :=
    hF.exists_joint_lipschitz_chart_readout_of_C11_initial_momentum hcomplete initial
      hG hLip hB hBtarget hEL hinit hp (hσB hq.2) terminal q.1 hlegal
  have hσAt : ContDiffAt ℝ 1 σ q.2 := hσ.contDiffAt (hV.mem_nhds hq.2)
  obtain ⟨Cσ, T, hT, hσLip⟩ := hσAt.exists_lipschitzOnWith
  have hparamAt : ContinuousAt (fun p : ℝ × W ↦ (σ p.2, p.1)) q := by
    have hs : ContinuousAt (fun p : ℝ × W ↦ σ p.2) q :=
      ContinuousAt.comp (x := q) (f := fun p : ℝ × W ↦ p.2)
        (g := σ) hσAt.continuousAt continuousAt_snd
    exact hs.prodMk continuousAt_fst
  have hnear : (univ ×ˢ (V ∩ T)) ∩
      (fun p : ℝ × W ↦ (σ p.2, p.1)) ⁻¹' ball (σ q.2, q.1) r₀ ∈ 𝓝 q :=
    inter_mem (prod_mem_nhds univ_mem (inter_mem (hV.mem_nhds hq.2) hT))
      (hparamAt.preimage_mem_nhds (ball_mem_nhds _ hr₀))
  obtain ⟨r, hr, hrsub⟩ := nhds_basis_closedBall.mem_iff.mp hnear
  have hparam {p : ℝ × W} (hp : p ∈ closedBall q r) :
      (σ p.2, p.1) ∈ closedBall (σ q.2, q.1) r₀ :=
    ball_subset_closedBall (hrsub hp).2
  have hσJoint := hσLip.comp LipschitzWith.prod_snd.lipschitzOnWith
    (show MapsTo Prod.snd (closedBall q r) T from fun _ hp ↦ (hrsub hp).1.2.2)
  have hcomp := hread.comp (hσJoint.prodMk LipschitzWith.prod_fst.lipschitzOnWith)
    (fun _ hp ↦ hparam hp)
  refine ⟨r, C₀ * max (Cσ * 1) 1, hr,
    fun _ hp ↦ ⟨mem_univ _, (hrsub hp).1.2.1⟩, fun _ hp ↦ hmap (hparam hp), ?_⟩
  simpa only [Function.comp_def] using hcomp

/-- The entire actual time–label domain has a countable exact open-ball cover.
Each selected ball retains a legal original output chart and a jointly Lipschitz
readout on its closed ball; the output chart is centered at the actual central image. -/
theorem exists_countable_lipschitz_timeLabel_chart_cover
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    {B : Set E} (hB : IsOpen B)
    (hBtarget : B ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {Γ : E → ℝ → M}
    (hEL : ∀ x ∈ B, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ B, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x)
    (hp : ∀ x ∈ B, F.chartMomentumFamily initial Γ (x, 0) = (x, fderiv ℝ G x))
    {V : Set W} (hV : IsOpen V) {σ : W → E} (hσ : ContDiffOn ℝ 1 σ V)
    (hσB : MapsTo σ V B) :
    ∃ S : Set (ℝ × W), S.Countable ∧ S ⊆ univ ×ˢ V ∧
      ∃ (r : ℝ × W → ℝ) (C : ℝ × W → ℝ≥0),
        (∀ q ∈ S, 0 < r q ∧ closedBall q (r q) ⊆ univ ×ˢ V ∧
          MapsTo (fun p : ℝ × W ↦ Γ (σ p.2) p.1) (closedBall q (r q))
            (extChartAt 𝓘(ℝ, E) (Γ (σ q.2) q.1)).source ∧
          LipschitzOnWith (C q)
            (fun p : ℝ × W ↦ extChartAt 𝓘(ℝ, E) (Γ (σ q.2) q.1) (Γ (σ p.2) p.1))
            (closedBall q (r q))) ∧
        (⋃ q ∈ S, ball q (r q)) = univ ×ˢ V := by
  classical
  have hlocal (q : ℝ × W) (hq : q ∈ univ ×ˢ V) :=
    hF.exists_lipschitz_timeLabel_chart_readout hcomplete initial hG hLip hB hBtarget
      hEL hinit hp hV hσ hσB hq (Γ (σ q.2) q.1)
      (mem_extChartAt_source (Γ (σ q.2) q.1))
  choose! r C hr hsub hmap hread using hlocal
  obtain ⟨S, hS, hSV, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof (univ ×ˢ V)).elim_nhds_subcover
      (fun q ↦ ball q (r q)) (fun q hq ↦ ball_mem_nhds q (hr q hq))
  refine ⟨S, hS, hSV, r, C, fun q hq ↦
    ⟨hr q (hSV q hq), hsub q (hSV q hq), hmap q (hSV q hq), hread q (hSV q hq)⟩,
    Subset.antisymm ?_ hcover⟩
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.mp hp
  exact hsub q (hSV q hq) (ball_subset_closedBall hpq)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
