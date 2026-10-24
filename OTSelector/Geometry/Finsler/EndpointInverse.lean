import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Geometry.Finsler.EndpointInverse

* **Conditions:** An actual jointly C2 complete tangent family and invertibility of its true two-endpoint map differential.
* **Objects:** A genuine local endpoint inverse with derived legal chart domains and exact endpoint identities.
* **Proof detail:** Read initial/final positions of the same family, apply the inverse function theorem and shrink to the two actual chart domains.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.

Source relation (derived): Endpoint nonconjugacy is an explicit internal input; global minimizing status of nearby branches is not concluded here.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerEndpointInverse.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerEndpointInverse`; the selected original proof blocks follow. -/
section

/-!
# A local inverse of the actual complete-family endpoint map

The endpoint map records the initial coordinate position and the final position of the
same intrinsic family in a specified final chart. Joint regularity of its actual tangent
family gives C2 endpoint regularity. Invertibility of the actual endpoint differential
then constructs a local inverse, with both chart domains and C2 inverse regularity derived.

Completeness supplies one genuine Euler--Lagrange family to which the construction applies.
The endpoint differential's invertibility is an explicit internal nonconjugacy condition;
no nearby global minimizing property or endpoint distance identification is asserted.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The initial position and actual final chart position of an initial-state family. -/
def chartEndpointMap (terminal : M) (Γ : (E × E) → ℝ → M) (b : ℝ)
    (z : E × E) : E × E :=
  (z.1, extChartAt 𝓘(ℝ, E) terminal (Γ z b))

/-- Joint C2 regularity of the actual tangent family gives actual endpoint-map C2
regularity at every initial state with a legal final chart. -/
theorem contDiffAt_chartEndpointMap
    {Γ : (E × E) → ℝ → M} {B : Set (E × E)} (hB : IsOpen B)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (B ×ˢ univ)) {z : E × E} (hz : z ∈ B) (terminal : M) (b : ℝ)
    (hx : Γ z b ∈ (extChartAt 𝓘(ℝ, E) terminal).source) :
    ContDiffAt ℝ 2 (chartEndpointMap terminal Γ b) z := by
  have hp := (contMDiffOn_positionFamily_of_tangentFamily hG).contMDiffAt
    ((hB.prod isOpen_univ).mem_nhds (show (z, b) ∈ B ×ˢ univ from ⟨hz, mem_univ _⟩))
  have hs : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) 2 (fun w ↦ Γ w b) z :=
    hp.comp z ((contDiffAt_id.prodMk contDiffAt_const).contMDiffAt)
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2 (extChartAt 𝓘(ℝ, E) terminal) (Γ z b) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hx)
  exact contDiffAt_fst.prodMk (hc.comp z hs).contDiffAt

/-- Invertibility of the genuine endpoint differential constructs a C2 local inverse
of that very endpoint map, inside the original initial and final chart domains. -/
theorem exists_chartEndpointInverse [CompleteSpace E] (initial terminal : M)
    {Γ : (E × E) → ℝ → M} {B : Set (E × E)} (hB : IsOpen B)
    (hsub : B ⊆ ContinuousFinslerNorm.chartEnergyDomain initial)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (B ×ˢ univ)) {z : E × E} (hz : z ∈ B) (b : ℝ)
    (hx : Γ z b ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
    (hinv : (fderiv ℝ (chartEndpointMap terminal Γ b) z).IsInvertible) :
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      (e : E × E → E × E) = chartEndpointMap terminal Γ b ∧
      z ∈ e.source ∧ chartEndpointMap terminal Γ b z ∈ e.target ∧
      e.source ⊆ B ∧ e.source ⊆ ContinuousFinslerNorm.chartEnergyDomain initial ∧
      (∀ w ∈ e.source, Γ w b ∈ (extChartAt 𝓘(ℝ, E) terminal).source) ∧
      ContDiffOn ℝ 2 e e.source ∧ ContDiffOn ℝ 2 e.symm e.target ∧
      ∀ q ∈ e.target, (e.symm q).1 = q.1 ∧
        Γ (e.symm q) b = (extChartAt 𝓘(ℝ, E) terminal).symm q.2 := by
  let P := chartEndpointMap terminal Γ b
  have hP : ContDiffAt ℝ 2 P z := contDiffAt_chartEndpointMap hB hG hz terminal b hx
  obtain ⟨A, hA⟩ := hinv
  have hd : HasFDerivAt P A.toContinuousLinearMap z := by
    rw [hA]
    exact (hP.differentiableAt (by norm_num)).hasFDerivAt
  let e₀ := hP.toOpenPartialHomeomorph P hd (by norm_num)
  have hz₀ : z ∈ e₀.source := hP.mem_toOpenPartialHomeomorph_source hd (by norm_num)
  have hi : ContDiffAt ℝ 2 e₀.symm (P z) := hP.to_localInverse hd (by norm_num)
  have hp := (contMDiffOn_positionFamily_of_tangentFamily hG).contMDiffAt
    ((hB.prod isOpen_univ).mem_nhds (show (z, b) ∈ B ×ˢ univ from ⟨hz, mem_univ _⟩))
  have hs : ContMDiffAt 𝓘(ℝ, E × E) 𝓘(ℝ, E) 2 (fun w ↦ Γ w b) z :=
    hp.comp z ((contDiffAt_id.prodMk contDiffAt_const).contMDiffAt)
  have hc : ContinuousAt (fun w ↦ Γ w b) z := hs.continuousAt
  let N := (B ∩ {w | Γ w b ∈ (extChartAt 𝓘(ℝ, E) terminal).source}) ∩
    ({w | ContDiffAt ℝ 2 P w} ∩ P ⁻¹' {q | ContDiffAt ℝ 2 e₀.symm q})
  have hn : N ∈ 𝓝 z := inter_mem
    (inter_mem (hB.mem_nhds hz)
      (hc.preimage_mem_nhds ((isOpen_extChartAt_source terminal).mem_nhds hx)))
    (inter_mem (hP.eventually (by norm_num))
      (hP.continuousAt (hi.eventually (by norm_num))))
  let e := e₀.restr N
  have hze : z ∈ e.source := ⟨hz₀, mem_interior_iff_mem_nhds.mpr hn⟩
  have hnsub : e.source ⊆ N := fun _ hw ↦ interior_subset hw.2
  have he : (e : E × E → E × E) = P := rfl
  refine ⟨e, he, hze, e.map_source hze, fun _ hw ↦ (hnsub hw).1.1,
    fun _ hw ↦ hsub (hnsub hw).1.1, fun _ hw ↦ (hnsub hw).1.2, ?_, ?_, ?_⟩
  · intro w hw
    have hreg : ContDiffAt ℝ 2 P w := (hnsub hw).2.1
    exact hreg.contDiffWithinAt
  · intro q hq
    have h := (hnsub (e.map_target hq)).2.2
    change ContDiffAt ℝ 2 e₀.symm (P (e.symm q)) at h
    have hr : P (e.symm q) = q := e.right_inv hq
    rw [hr] at h
    exact h.contDiffWithinAt
  · intro q hq
    have hr : P (e.symm q) = q := e.right_inv hq
    refine ⟨?_, ?_⟩
    · change (P (e.symm q)).1 = q.1
      exact congrArg Prod.fst hr
    ·
      have hs := congrArg Prod.snd hr
      change extChartAt 𝓘(ℝ, E) terminal (Γ (e.symm q) b) = q.2 at hs
      rw [← hs, (extChartAt 𝓘(ℝ, E) terminal).left_inv (hnsub (e.map_target hq)).1.2]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Original metric completeness constructs one actual family with prescribed initial
state. Whenever its actual endpoint derivative is invertible, that same family admits
a C2 local endpoint inverse and realizes both coordinate endpoints of every target pair. -/
theorem exists_complete_endpointInverseFamily (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M) (a : ℝ) :
    ∃ Γ : (E × E) → ℝ → M,
      (∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ) ∧
      (∀ z ∈ chartEnergyDomain initial,
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
          (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
            (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) ∧
      ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
        (chartEnergyDomain initial ×ˢ univ) ∧
      ∀ (terminal : M) (b : ℝ) (z : E × E), z ∈ chartEnergyDomain initial →
        Γ z b ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
        (fderiv ℝ (chartEndpointMap terminal Γ b) z).IsInvertible →
        ∃ e : OpenPartialHomeomorph (E × E) (E × E),
          (e : E × E → E × E) = chartEndpointMap terminal Γ b ∧
          z ∈ e.source ∧ chartEndpointMap terminal Γ b z ∈ e.target ∧
          e.source ⊆ chartEnergyDomain initial ∧
          (∀ w ∈ e.source, Γ w b ∈ (extChartAt 𝓘(ℝ, E) terminal).source) ∧
          ContDiffOn ℝ 2 e e.source ∧ ContDiffOn ℝ 2 e.symm e.target ∧
          e.target ⊆ (extChartAt 𝓘(ℝ, E) initial).target ×ˢ
            (extChartAt 𝓘(ℝ, E) terminal).target ∧
          ∀ q ∈ e.target, (e.symm q).1 = q.1 ∧
            Γ (e.symm q) a = (extChartAt 𝓘(ℝ, E) initial).symm q.1 ∧
            Γ (e.symm q) b = (extChartAt 𝓘(ℝ, E) terminal).symm q.2 := by
  obtain ⟨Γ, hEL, hinit, hG⟩ := hF.exists_complete_tangentFamily_C2 hcomplete initial a
  refine ⟨Γ, hEL, hinit, hG, ?_⟩
  intro terminal b z hz hx hinv
  obtain ⟨e, he, hze, hzt, hsub, _, hmap, hf, hi, hend⟩ :=
    exists_chartEndpointInverse initial terminal (isOpen_chartEnergyDomain initial)
      Subset.rfl hG hz b hx hinv
  refine ⟨e, he, hze, hzt, hsub, hmap, hf, hi, ?_, ?_⟩
  · intro q hq
    have hzq := hsub (e.map_target hq)
    have hright : chartEndpointMap terminal Γ b (e.symm q) = q := by
      rw [← he]
      exact e.right_inv hq
    refine ⟨?_, ?_⟩
    · rw [← (hend q hq).1]
      exact hzq.1
    · have hlast := (extChartAt 𝓘(ℝ, E) terminal).map_source (hmap _ (e.map_target hq))
      have hr := congrArg Prod.snd hright
      change extChartAt 𝓘(ℝ, E) terminal (Γ (e.symm q) b) = q.2 at hr
      exact hr ▸ hlast
  · intro q hq
    have hzq := hsub (e.map_target hq)
    refine ⟨(hend q hq).1, ?_, (hend q hq).2⟩
    have hb := congrArg (fun v : TangentBundle 𝓘(ℝ, E) M ↦ v.1)
      (hinit (e.symm q) hzq)
    rw [tangentChart_symm_eq initial hzq.1 (e.symm q).2] at hb
    change Γ (e.symm q) a = (extChartAt 𝓘(ℝ, E) initial).symm (e.symm q).1 at hb
    rw [(hend q hq).1] at hb
    exact hb

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
