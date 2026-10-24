import OTSelector.Analysis.Calculus.Whitney.MetricPotentialC11
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.EikonalJet
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.MeasureTheory.LusinCompactProperty

/-!
# Geometry.Finsler.MetricPotentialEikonal

* **Conditions:** An original absolutely continuous coordinate law, compact C1,1 contact extension and actual branch eikonal data.
* **Objects:** Almost-everywhere density-one/second-order jets and compact continuity cores with smooth normalized representatives.
* **Proof detail:** Apply density and Rademacher to the actual law, transfer contact derivatives within the core, construct normalized jets and apply Lusin/inner regularity to the remaining AE data.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110): Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=3): Definition 411B, pp. 3–4, and Lemma 412A(c), pp. 10–11.
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): Proof of proposition prop:rough-ray-quadratic, equation eq:rough-eikonal-jet at line 1228 and following normalized conormal construction.

Source relation (derived): Density-one and second-derivative conditions are derived almost everywhere rather than supplied as independent geometric assumptions.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.MetricPotentialEikonal.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.MetricPotentialEikonal`; the selected original proof blocks follow. -/
section

/-!
# Almost-everywhere actual eikonal jets of a contact-potential extension

Lebesgue density and Rademacher apply to the original absolutely continuous measure.
The actual C1,1 extension then gives smooth normalized representatives on the same
Finsler Hamiltonian branch, without a supplied density-one or second-derivative premise.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Lebesgue's density theorem for an original measure absolutely continuous with
respect to Haar measure. The contact set need not have interior. -/
theorem ae_density_one_of_absolutelyContinuous
    {μ ν : Measure E} [IsAddHaarMeasure μ] (hν : ν ≪ μ) (K : Set E) :
    ∀ᵐ x ∂ν.restrict K,
      Tendsto (fun r ↦ μ (K ∩ closedBall x r) / μ (closedBall x r))
        (𝓝[>] 0) (𝓝 1) := by
  exact (hν.restrict K).ae_le (Besicovitch.ae_tendsto_measure_inter_div μ K)

private theorem density_one_inter_open {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (μ : Measure E) {K V : Set E} {x : E}
    (hx : Tendsto (fun r ↦ μ (K ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hV : IsOpen V) (hxV : x ∈ V) :
    Tendsto (fun r ↦ μ ((K ∩ V) ∩ closedBall x r) / μ (closedBall x r))
      (𝓝[>] 0) (𝓝 1) := by
  apply hx.congr'
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  have hr : ∀ᶠ r : ℝ in 𝓝[>] 0, r < ε :=
    nhdsWithin_le_nhds (gt_mem_nhds hε)
  filter_upwards [hr] with r hr
  have hclosed : closedBall x r ⊆ V := by
    intro y hy
    apply hball
    exact (mem_closedBall.mp hy).trans_lt hr
  have heq : (K ∩ V) ∩ closedBall x r = K ∩ closedBall x r := by
    ext y
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hclosed h.2⟩, h.2⟩⟩
  rw [heq]


private theorem exists_jet_compact_core_of_ae
    {ν : Measure E} {K : Set E} (hK : MeasurableSet K) (hνK : ν K ≠ ⊤)
    {J : E → Prop} (hJ : ∀ᵐ x ∂ν.restrict K, J x) (G : E → ℝ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K' ⊆ K, IsCompact K' ∧ ν (K \ K') < ε ∧
      ContinuousOn (fderiv ℝ (fderiv ℝ G)) K' ∧ ∀ x ∈ K', J x := by
  exact exists_lusin_compact_core_with_ae_property hK hνK
    (measurable_fderiv ℝ (fderiv ℝ G)) hJ hε

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)

include hF

/-- The actual extension yields almost-everywhere normalized smooth second jets for
the original potential on its contact set, on the same genuine Hamiltonian branch.
Density-one and existence of the actual extension Hessian are conclusions. -/
theorem ae_chartHamiltonian_normalized_secondJet_of_C11 (old : M)
    {μ ν : Measure E} [IsAddHaarMeasure μ] (hν : ν ≪ μ)
    {K : Set E} (hK : MeasurableSet K) {u G : E → ℝ} {L : ℝ≥0}
    (hG : ContDiff ℝ 1 G) (hLip : LipschitzWith L (fderiv ℝ G))
    (hval : EqOn G u K) (hactual : ∀ x ∈ K, HasFDerivAt u (fderiv ℝ G x) x)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old)
    (heG : ContDiffOn ℝ ∞ e.symm e.target)
    (htarget : ∀ x ∈ K, (x, fderiv ℝ u x) ∈ e.target)
    (heikonal : ∀ x ∈ K,
      localHamiltonian (F.chartEnergy old) e (x, fderiv ℝ u x) = (1 / 2 : ℝ)) :
    ∀ᵐ x ∂ν.restrict K,
      Tendsto (fun r ↦ μ (K ∩ closedBall x r) / μ (closedBall x r))
        (𝓝[>] 0) (𝓝 1) ∧
      HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x ∧
      HasFDerivWithinAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ G) x) K x ∧
      (∀ v : E, fderiv ℝ (fderiv ℝ G) x v (e.symm (x, fderiv ℝ u x)).2 =
        baseEnergyDifferential (F.chartEnergy old) (e.symm (x, fderiv ℝ u x)) v) ∧
      ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P x = u x ∧
        HasFDerivAt P (fderiv ℝ u x) x ∧
        HasFDerivAt (fderiv ℝ P) (fderiv ℝ (fderiv ℝ G) x) x ∧
        HasFDerivAt (fun y ↦ localHamiltonian (F.chartEnergy old) e (y, fderiv ℝ P y))
          (0 : E →L[ℝ] ℝ) x ∧
        let n : E → E →L[ℝ] ℝ := fun y ↦
          (Real.sqrt (2 * localHamiltonian (F.chartEnergy old) e (y, fderiv ℝ P y)))⁻¹ •
            fderiv ℝ P y
        n x = fderiv ℝ u x ∧
          HasFDerivAt n (fderiv ℝ (fderiv ℝ G) x) x ∧ ContDiffAt ℝ ∞ n x := by
  have hmatch : EqOn (fderiv ℝ G) (fderiv ℝ u) K :=
    fun x hx ↦ (hactual x hx).fderiv.symm
  have henergy : ∀ x ∈ K,
      localHamiltonian (F.chartEnergy old) e (x, fderiv ℝ G x) = (1 / 2 : ℝ) := by
    intro x hx
    rw [hmatch hx]
    exact heikonal x hx
  have hd : ∀ᵐ x ∂ν.restrict K, DifferentiableAt ℝ (fderiv ℝ G) x :=
    ae_restrict_of_ae (hν.ae_le hLip.ae_differentiableAt)
  filter_upwards [ae_density_one_of_absolutelyContinuous hν K, hd,
    ae_restrict_mem hK] with x hx hsecond hxK
  have hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt G (fderiv ℝ G y) y :=
    Filter.Eventually.of_forall (fun y ↦ (hG.differentiable one_ne_zero y).hasFDerivAt)
  have hp : (x, fderiv ℝ G x) ∈ e.target := by
    rw [hmatch hxK]
    exact htarget x hxK
  obtain ⟨_, hdir⟩ := hF.chartHamiltonian_energyGraph_hasFDerivAt_zero_of_density_one
    μ old he hsub heG hx hxK hsecond.hasFDerivAt hp henergy
  obtain ⟨P, hP, hPx, hP₁, hP₂, _, _, hzero, hnx, hnD, hn⟩ :=
    hF.exists_smooth_chartHamiltonian_normalized_secondJet
      μ old he hsub heG hx hxK hfirst hsecond.hasFDerivAt hp henergy
  refine ⟨hx, hsecond.hasFDerivAt,
    hsecond.hasFDerivAt.hasFDerivWithinAt.congr' hmatch.symm hxK, ?_,
    P, hP, hPx.trans (hval hxK), hP₁.congr_fderiv (hmatch hxK), hP₂, hzero,
    hnx.trans (hmatch hxK), hnD, hn⟩
  simpa only [hmatch hxK] using hdir

/-- A smooth representative of the actual extension second jet, on a genuine local
Legendre branch, whose normalized covector has the original value and the same
first derivative. This predicate records the constructed result, not input data. -/
def HasNormalizedPotentialJet (old : M) (u G : E → ℝ) (x : E) : Prop :=
  ∃ e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)),
    (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old) ∧
    e.source ⊆ chartEnergyDomain old ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
    (x, fderiv ℝ u x) ∈ e.target ∧
    ∃ P : E → ℝ, ContDiff ℝ ∞ P ∧ P x = u x ∧
      HasFDerivAt P (fderiv ℝ u x) x ∧
      HasFDerivAt (fderiv ℝ P) (fderiv ℝ (fderiv ℝ G) x) x ∧
      HasFDerivAt (fun y ↦ localHamiltonian (F.chartEnergy old) e (y, fderiv ℝ P y))
        (0 : E →L[ℝ] ℝ) x ∧
      let n : E → E →L[ℝ] ℝ := fun y ↦
        (Real.sqrt (2 * localHamiltonian (F.chartEnergy old) e (y, fderiv ℝ P y)))⁻¹ •
          fderiv ℝ P y
      n x = fderiv ℝ u x ∧
        HasFDerivAt n (fderiv ℝ (fderiv ℝ G) x) x ∧ ContDiffAt ℝ ∞ n x

/-- Unit-energy Legendre data of the original covector constructs the legal local
branch automatically. Almost every original contact point then has a normalized
smooth representative of the same extension second jet. -/
theorem ae_normalizedPotentialJet_of_C11 (old : M)
    {μ ν : Measure E} [IsAddHaarMeasure μ] (hν : ν ≪ μ)
    {K : Set E} (hK : MeasurableSet K) {u G : E → ℝ} {L : ℝ≥0}
    (hG : ContDiff ℝ 1 G) (hLip : LipschitzWith L (fderiv ℝ G))
    (hval : EqOn G u K) (hactual : ∀ x ∈ K, HasFDerivAt u (fderiv ℝ G x) x)
    (hunit : ∀ x ∈ K, ∃ v : E, (x, v) ∈ chartEnergyDomain old ∧
      fiberLegendre (F.chartEnergy old) (x, v) = fderiv ℝ u x ∧
      F.chartEnergy old (x, v) = (1 / 2 : ℝ)) :
    ∀ᵐ x ∂ν.restrict K,
      Tendsto (fun r ↦ μ (K ∩ closedBall x r) / μ (closedBall x r))
        (𝓝[>] 0) (𝓝 1) ∧
      HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x ∧
      HasFDerivWithinAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ G) x) K x ∧
      HasNormalizedPotentialJet (F := F) old u G x := by
  have hmatch : EqOn (fderiv ℝ G) (fderiv ℝ u) K :=
    fun x hx ↦ (hactual x hx).fderiv.symm
  have hd : ∀ᵐ x ∂ν.restrict K, DifferentiableAt ℝ (fderiv ℝ G) x :=
    ae_restrict_of_ae (hν.ae_le hLip.ae_differentiableAt)
  filter_upwards [ae_density_one_of_absolutelyContinuous hν K, hd,
    ae_restrict_mem hK] with x hx hsecond hxK
  obtain ⟨v, hv, hvp, _⟩ := hunit x hxK
  obtain ⟨e, he, _, htarget, hsub, _, heG, _, _⟩ :=
    hF.exists_smooth_chartLegendre_local_inverse old hv
  have hp : (x, fderiv ℝ G x) ∈ e.target := by
    rw [hmatch hxK, ← hvp]
    exact htarget
  let V : Set E := (fun y ↦ (y, fderiv ℝ G y)) ⁻¹' e.target
  have hV : IsOpen V := e.open_target.preimage (continuous_id.prodMk hLip.continuous)
  have hxV : x ∈ V := hp
  have hxKV : x ∈ K ∩ V := ⟨hxK, hxV⟩
  have hdensity := density_one_inter_open μ hx hV hxV
  have henergy : ∀ y ∈ K ∩ V,
      localHamiltonian (F.chartEnergy old) e (y, fderiv ℝ G y) = (1 / 2 : ℝ) := by
    intro y hy
    obtain ⟨w, hw, hwp, hwe⟩ := hunit y hy.1
    have hyt : (y, fderiv ℝ G y) ∈ e.target := hy.2
    have hinverse : e.symm (y, fderiv ℝ G y) = (y, w) := by
      apply hF.injOn_parametricLegendre_chartEnergy old (hsub (e.map_target hyt)) hw
      calc
        parametricLegendre (F.chartEnergy old) (e.symm (y, fderiv ℝ G y)) =
            (y, fderiv ℝ G y) := by simpa only [he] using e.right_inv hyt
        _ = parametricLegendre (F.chartEnergy old) (y, w) := by
          simp only [parametricLegendre, hwp, hmatch hy.1]
    rw [hF.localHamiltonian_chartEnergy_eq old he hsub hyt, hinverse]
    exact hwe
  have hfirst : ∀ᶠ y in 𝓝 x, HasFDerivAt G (fderiv ℝ G y) y :=
    Filter.Eventually.of_forall (fun y ↦ (hG.differentiable one_ne_zero y).hasFDerivAt)
  obtain ⟨P, hP, hPx, hP₁, hP₂, _, _, hzero, hnx, hnD, hn⟩ :=
    hF.exists_smooth_chartHamiltonian_normalized_secondJet
      μ old he hsub heG hdensity hxKV hfirst hsecond.hasFDerivAt hp henergy
  refine ⟨hx, hsecond.hasFDerivAt,
    hsecond.hasFDerivAt.hasFDerivWithinAt.congr' hmatch.symm hxK,
    e, he, hsub, heG, ?_, P, hP, hPx.trans (hval hxK),
    hP₁.congr_fderiv (hmatch hxK), hP₂, hzero, hnx.trans (hmatch hxK), hnD, hn⟩
  rwa [← hmatch hxK]

/-- Genuine compact endpoint-distance data constructs the extension and almost
all its normalized original-potential jets. Every requested positive mass tolerance
also gives a compact core with continuous actual extension Hessian. Local Legendre
branches, density-one points and second derivatives are all constructed. -/
theorem exists_metric_potential_eikonal_cores (old : M)
    {μ ν : Measure E} [IsAddHaarMeasure μ] (hν : ν ≪ μ)
    {N : Type*} [PseudoMetricSpace N] {φ : N → ℝ}
    (hφ : LipschitzWith 1 φ) (Y : E → N)
    {K : Set E} (hK : IsCompact K) (hνK : ν K ≠ ⊤)
    {c : E} {R : ℝ} (hR : 0 < R) (hKball : K ⊆ closedBall c R) (a b : E → N)
    {A B : Set N} (hA : IsCompact A) (hB : IsCompact B)
    (haA : MapsTo a K A) (hbB : MapsTo b K B)
    (ha : ∀ x ∈ K, φ (Y x) - φ (a x) = dist (a x) (Y x))
    (hb : ∀ x ∈ K, φ (b x) - φ (Y x) = dist (Y x) (b x))
    (hleft : ∀ a ∈ A, ∀ z ∈ closedBall c (3 * R),
      ContDiffAt ℝ 2 (fun y ↦ dist a (Y y)) z)
    (hright : ∀ b ∈ B, ∀ z ∈ closedBall c (3 * R),
      ContDiffAt ℝ 2 (fun y ↦ dist (Y y) b) z)
    (hcontLeft : ContinuousOn
      (fun q : N × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ dist q.1 (Y y))) q.2)
      (A ×ˢ closedBall c (3 * R)))
    (hcontRight : ContinuousOn
      (fun q : N × E ↦ fderiv ℝ (fderiv ℝ (fun y ↦ dist (Y y) q.1)) q.2)
      (B ×ˢ closedBall c (3 * R)))
    (hunit : ∀ x ∈ K, ∃ v : E, (x, v) ∈ chartEnergyDomain old ∧
      fiberLegendre (F.chartEnergy old) (x, v) = fderiv ℝ (φ ∘ Y) x ∧
      F.chartEnergy old (x, v) = (1 / 2 : ℝ)) :
    ∃ (G : E → ℝ) (L : ℝ≥0), ContDiff ℝ 1 G ∧ HasCompactSupport G ∧
      ContDiffOn ℝ ∞ G Kᶜ ∧ LipschitzWith L (fderiv ℝ G) ∧
      EqOn G (φ ∘ Y) K ∧ EqOn (fderiv ℝ G) (fderiv ℝ (φ ∘ Y)) K ∧
      (∀ x ∈ K, HasFDerivAt (φ ∘ Y) (fderiv ℝ G x) x) ∧
      let J : E → Prop := fun x ↦
        Tendsto (fun r ↦ μ (K ∩ closedBall x r) / μ (closedBall x r))
          (𝓝[>] 0) (𝓝 1) ∧
        HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x ∧
        HasFDerivWithinAt (fderiv ℝ (φ ∘ Y)) (fderiv ℝ (fderiv ℝ G) x) K x ∧
        HasNormalizedPotentialJet (F := F) old (φ ∘ Y) G x
      (∀ᵐ x ∂ν.restrict K, J x) ∧
        ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ K' ⊆ K, IsCompact K' ∧ ν (K \ K') < ε ∧
          ContinuousOn (fderiv ℝ (fderiv ℝ G)) K' ∧ ∀ x ∈ K', J x := by
  obtain ⟨G, L, hG, hsupp, hOff, hLip, hval, hder, hactual⟩ :=
    exists_metric_potential_C11_of_compact_distance_hessians hφ Y hK hR hKball a b
      hA hB haA hbB ha hb hleft hright hcontLeft hcontRight
  have hfirst (x) (hx : x ∈ K) : HasFDerivAt (φ ∘ Y) (fderiv ℝ G x) x :=
    (hactual x hx).1
  have hAE := hF.ae_normalizedPotentialJet_of_C11 old hν hK.measurableSet
    hG hLip hval hfirst hunit
  refine ⟨G, L, hG, hsupp, hOff, hLip, hval, hder, hfirst, hAE, ?_⟩
  intro ε hε
  exact exists_jet_compact_core_of_ae hK.measurableSet hνK hAE G hε

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
