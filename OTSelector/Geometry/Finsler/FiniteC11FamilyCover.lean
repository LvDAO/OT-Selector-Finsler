import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FamilyCover
import OTSelector.Geometry.Finsler.CalibratedC11
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.CompactChartRefinement
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerFiniteC11FamilyCover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerFiniteC11FamilyCover`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.FiniteC11FamilyCover

* **Conditions:** A compact core with uniformly positive two-sided calibrated reach in complete smooth strongly convex Finsler geometry.
* **Objects:** An exact finite C1,1 coordinate-core cover and a refinement by actual complete families on open neighborhoods.
* **Proof detail:** Use the contact-extension construction in local charts, take a finite compact refinement and retain each normalized complete family with its original initial momentum.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.

Source relation (derived): A finite compact specialization of the countable contact/family package, with exact original core coverage.
-/

/-!
# Finite original C1,1 families on a uniformly calibrated compact core

Finite coordinate refinement and the existing original-distance C1,1 extension
producer give an exact finite cover. A second finite refinement retains actual
complete geodesic families on open neighborhoods of every compact piece.
-/

open Set Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
universe u v
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- A compact core with uniform two-sided original calibration has a finite exact
cover by compact coordinate cores carrying actual global C1,1 extensions. -/
theorem exists_finite_compact_calibrated_C11_cover (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {f : M → ℝ} (hf : let _instFiniteC11Lip : MetricSpace M := F.metricSpace
      LipschitzWith 1 f) {A : Set M} (hA : IsCompact A) {δ : ℝ} (hδ : 0 < δ)
    (hreach : let _instFiniteC11Reach : MetricSpace M := F.metricSpace
      ∀ y ∈ A, ∃ a b : M, dist a y = δ ∧ f y - f a = δ ∧
        dist y b = δ ∧ f b - f y = δ) :
    ∃ ι : Type (max u v), Finite ι ∧
      ∃ (old : ι → M) (K : ι → Set E) (G : ι → E → ℝ) (L : ι → ℝ≥0),
        (∀ i, IsCompact (K i) ∧ K i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ContDiff ℝ 1 (G i) ∧ HasCompactSupport (G i) ∧
          LipschitzWith (L i) (fderiv ℝ (G i)) ∧
          EqOn (G i) (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) (K i) ∧
          EqOn (fderiv ℝ (G i))
            (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)) (K i) ∧
          ∀ x ∈ K i, HasFDerivAt (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)
            (fderiv ℝ (G i) x) x) ∧
        (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i) = A := by
  classical
  let _instFiniteC11Metric : MetricSpace M := F.metricSpace
  obtain ⟨J, C, hC, hCcover⟩ := exists_finite_compact_chart_refinement (E := E) A hA
  have hfinite (j : {j // j ∈ J}) :=
    hF.exists_finite_calibrated_C11_cover hcomplete j.val
      (hC j.val j.property).1 (hC j.val j.property).2.1 hδ hf
      (fun x hx ↦ hreach ((extChartAt 𝓘(ℝ, E) j.val).symm x)
        ((hC j.val j.property).2.2 ⟨x, hx, rfl⟩))
  choose r hr T hTcover hT using hfinite
  have hext (j : {j // j ∈ J}) (k : {k // k ∈ T j}) := (hT j k.val k.property).2
  choose G L hG using hext
  let ι := Σ j : {j // j ∈ J}, {k // k ∈ T j}
  let old : ι → M := fun p ↦ p.1.val
  let K : ι → Set E := fun p ↦ C p.1.val ∩ closedBall p.2.val (r p.1 / 8)
  refine ⟨ι, inferInstance, old, K, (fun p ↦ G p.1 p.2), (fun p ↦ L p.1 p.2), ?_, ?_⟩
  · intro p
    obtain ⟨hG₁, hG₂, _, hG₃, hG₄, hG₅, hG₆⟩ := hG p.1 p.2
    exact ⟨(hT p.1 p.2.val p.2.property).1,
      fun x hx ↦ (hC p.1.val p.1.property).2.1 hx.1,
      hG₁, hG₂, hG₃, hG₄, hG₅, hG₆⟩
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨p, z, hz, rfl⟩ := mem_iUnion.mp hx
      exact (hC p.1.val p.1.property).2.2 ⟨z, hz.1, rfl⟩
    · intro x hx
      rw [← hCcover] at hx
      obtain ⟨j, hj, z, hz, hzx⟩ := mem_iUnion₂.mp hx
      let j' : {j // j ∈ J} := ⟨j, hj⟩
      obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp (hTcover j' hz)
      exact mem_iUnion.mpr ⟨⟨j', ⟨k, hk⟩⟩, z, ⟨hz, hzk⟩, hzx⟩

/-- The same compact original core admits finitely many C1,1 coordinate pieces
with complete actual geodesic families on open neighborhoods. All pieces retain
the same positive calibrated reach, and their union is exactly the original core. -/
theorem exists_finite_compact_C11_family_cover (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {f : M → ℝ} (hf : let _instFiniteFamilyLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 f) {A : Set M} (hA : IsCompact A) {δ : ℝ} (hδ : 0 < δ)
    (hreach : let _instFiniteFamilyReach : MetricSpace M := F.metricSpace
      ∀ y ∈ A, ∃ a b : M, dist a y = δ ∧ f y - f a = δ ∧
        dist y b = δ ∧ f b - f y = δ) :
    let _instFiniteFamilyMetric : MetricSpace M := F.metricSpace
    ∃ ι : Type (max u v), Finite ι ∧
      ∃ (old : ι → M) (K U : ι → Set E) (G : ι → E → ℝ) (L : ι → ℝ≥0)
          (Γ : ι → E → ℝ → M),
        (∀ i, IsCompact (K i) ∧ K i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ContDiff ℝ 1 (G i) ∧ HasCompactSupport (G i) ∧
          LipschitzWith (L i) (fderiv ℝ (G i)) ∧
          EqOn (G i) (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) (K i) ∧
          EqOn (fderiv ℝ (G i))
            (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)) (K i) ∧
          ∀ x ∈ K i, HasFDerivAt (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)
            (fderiv ℝ (G i) x) x) ∧
        (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i) = A ∧
        (∀ i, ∀ x ∈ K i, ∃ a b : M,
          dist a ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ ∧
          f ((extChartAt 𝓘(ℝ, E) (old i)).symm x) - f a = δ ∧
          dist ((extChartAt 𝓘(ℝ, E) (old i)).symm x) b = δ ∧
          f b - f ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ) ∧
        ∀ i, IsOpen (U i) ∧ K i ⊆ U i ∧
          U i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ∀ x ∈ U i, Γ i x 0 = (extChartAt 𝓘(ℝ, E) (old i)).symm x ∧
            F.IsEulerLagrangeOn (Γ i x) univ ∧
            ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (Γ i x) ∧
            F.chartMomentumFamily (old i) (Γ i) (x, 0) = (x, fderiv ℝ (G i) x) := by
  classical
  let _instFiniteFamilyMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, hfinite, old, K, G, L, hdata, hcover⟩ :=
    hF.exists_finite_compact_calibrated_C11_cover hcomplete hf hA hδ hreach
  let _instFiniteFamilyIndex : Finite ι := hfinite
  have hpartners (i : ι) (x : E) (hx : x ∈ K i) : ∃ a b : M,
      dist a ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ ∧
      f ((extChartAt 𝓘(ℝ, E) (old i)).symm x) - f a = δ ∧
      dist ((extChartAt 𝓘(ℝ, E) (old i)).symm x) b = δ ∧
      f b - f ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ := by
    apply hreach
    rw [← hcover]
    exact mem_iUnion.mpr ⟨i, x, hx, rfl⟩
  have hlocal (i : ι) (x : K i) :=
    hF.exists_C11_core_family_ball hcomplete (old i) (hdata i).2.1 hf
      (hdata i).2.2.1 (hdata i).2.2.2.2.1 (hdata i).2.2.2.2.2.2.1
      hδ (hpartners i) x.property
  choose r Γ hr hball hinit using hlocal
  have hfinite (i : ι) := (hdata i).1.elim_finite_subcover
    (fun x : K i ↦ ball (x : E) (r i x / 2)) (fun _ ↦ isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (half_pos (hr i ⟨z, hz⟩))⟩)
  choose J hJ using hfinite
  let κ := Σ i : ι, {x : K i // x ∈ J i}
  let C : κ → Set E := fun p ↦ K p.1 ∩ closedBall p.2.val.val (r p.1 p.2.val / 2)
  let U : κ → Set E := fun p ↦ ball p.2.val.val (r p.1 p.2.val)
  refine ⟨κ, inferInstance, (fun p ↦ old p.1), C, U, (fun p ↦ G p.1),
    (fun p ↦ L p.1), (fun p ↦ Γ p.1 p.2.val), ?_, ?_, ?_, ?_⟩
  · intro p
    obtain ⟨hK, htarget, hG, hsupp, hLip, hval, hder, hactual⟩ := hdata p.1
    exact ⟨hK.inter_right isClosed_closedBall, fun x hx ↦ htarget hx.1,
      hG, hsupp, hLip, hval.mono inter_subset_left, hder.mono inter_subset_left,
      fun x hx ↦ hactual x hx.1⟩
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨p, z, hz, rfl⟩ := mem_iUnion.mp hx
      rw [← hcover]
      exact mem_iUnion.mpr ⟨p.1, z, hz.1, rfl⟩
    · intro x hx
      rw [← hcover] at hx
      obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
      obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp (hJ i hz)
      exact mem_iUnion.mpr ⟨⟨i, ⟨j, hj⟩⟩, z, ⟨hz, ball_subset_closedBall hzj⟩, hzx⟩
  · exact fun p x hx ↦ hpartners p.1 x hx.1
  · intro p
    refine ⟨isOpen_ball, ?_, ?_, ?_⟩
    · exact fun x hx ↦ closedBall_subset_ball (half_lt_self (hr p.1 p.2.val)) hx.2
    · exact fun x hx ↦ hball p.1 p.2.val (ball_subset_closedBall hx)
    · exact fun x hx ↦ hinit p.1 p.2.val x (ball_subset_closedBall hx)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
