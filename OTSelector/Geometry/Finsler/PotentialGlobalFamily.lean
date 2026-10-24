import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MeasurableLegendre
import OTSelector.Geometry.Finsler.PotentialChartFamily
import OTSelector.Geometry.Finsler.PotentialInitialState
import OTSelector.Geometry.Finsler.PotentialMeasurablePhase

/-!
# Geometry.Finsler.PotentialGlobalFamily

* **Conditions:** Complete original Finsler geometry and its intrinsic nonzero potential-covector domain.
* **Objects:** A Borel regular potential domain and one jointly measurable actual global complete family glued across legal charts.
* **Proof detail:** Obtain a countable chart cover, identify local domains intrinsically and glue measurable chart families by first occurrence and overlap uniqueness.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=24): Sections 4A2G(e), pp. 15–16; 4A2N(b), p. 22; 4A2Q(h) and proof, pp. 24–25.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialGlobalFamily.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialGlobalFamily`; the selected original proof blocks follow. -/
section

/-!
# The intrinsic measurable potential domain and its complete curve family

The actual intrinsic differential and original fiber energy define the regular domain.
A countable legal chart cover is obtained from completeness of the original length metric.
The domain is Borel because it is the union of the actual good chart domains. Complete
Euler--Lagrange uniqueness identifies all chart constructions on overlaps, giving one
jointly measurable actual curve family with the original potential covector as initial data.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [BorelSpace M]

/-- The intrinsic domain where the actual potential differential has a nonzero energy state. -/
def potentialRegularDomain (F : ContinuousFinslerNorm E M) (u : M → ℝ) : Set M :=
  {x | MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x ∧
    ∃ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 ∧
      fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x}

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

omit [MeasurableSpace M] [BorelSpace M] in
/-- Each actual good chart domain is exactly the intrinsic domain inside that chart. -/
theorem potentialLegendreDomain_eq_source_inter_regular (hF : F.IsSmoothStronglyConvex)
    (old : M) (u : M → ℝ) :
    F.potentialLegendreDomain old u =
      (extChartAt 𝓘(ℝ, E) old).source ∩ F.potentialRegularDomain u := by
  ext x
  constructor
  · intro hx
    have hd := hF.mdifferentiableAt_of_mem_potentialLegendreDomain old u hx
    exact ⟨hx.1, hd, (hF.mem_chartLegendreRange_potential_iff_intrinsic old hx.1 hd).mp hx.2⟩
  · rintro ⟨hx, hd, hv⟩
    exact ⟨hx, (hF.mem_chartLegendreRange_potential_iff_intrinsic old hx hd).mpr hv⟩

variable [T2Space M] [PreconnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
/-- Completeness supplies a countable legal chart cover of the intrinsic potential domain. -/
theorem exists_countable_potentialLegendre_cover (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (u : M → ℝ) :
    ∃ C : Set M, C.Countable ∧
      F.potentialRegularDomain u = ⋃ old ∈ C, F.potentialLegendreDomain old u := by
  let _instPotentialRegularMetric : MetricSpace M := F.metricSpace
  let _instPotentialRegularProper : ProperSpace M := F.properSpace_of_complete hcomplete
  obtain ⟨C, hC, hcover⟩ := countable_cover_nhds
    (fun old : M ↦ (isOpen_extChartAt_source (I := 𝓘(ℝ, E)) old).mem_nhds
      (mem_extChartAt_source old))
  refine ⟨C, hC, ?_⟩
  ext x
  constructor
  · intro hx
    have hc : x ∈ ⋃ old ∈ C, (extChartAt 𝓘(ℝ, E) old).source := by
      rw [hcover]
      exact mem_univ x
    obtain ⟨old, ho, hxo⟩ := mem_iUnion₂.mp hc
    exact mem_iUnion₂.mpr ⟨old, ho,
      (hF.potentialLegendreDomain_eq_source_inter_regular old u).symm ▸ ⟨hxo, hx⟩⟩
  · intro hx
    obtain ⟨old, _, hxo⟩ := mem_iUnion₂.mp hx
    rw [hF.potentialLegendreDomain_eq_source_inter_regular old u] at hxo
    exact hxo.2

/-- The intrinsic actual potential domain is Borel, without any regularity assumption on u. -/
theorem measurableSet_potentialRegularDomain (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (u : M → ℝ) :
    MeasurableSet (F.potentialRegularDomain u) := by
  obtain ⟨C, hC, heq⟩ := hF.exists_countable_potentialLegendre_cover hcomplete u
  rw [heq]
  exact MeasurableSet.biUnion hC (fun old _ ↦ hF.measurableSet_potentialLegendreDomain old u)


end IsSmoothStronglyConvex

private theorem exists_jointlyMeasurable_glue
    {ι M R N : Type*} [Countable ι]
    [MeasurableSpace M] [MeasurableSpace R] [MeasurableSpace N]
    (S : Set M) (U : ι → Set M) (hU : ∀ i, MeasurableSet (U i))
    (hcover : S ⊆ ⋃ i, U i)
    (G : ∀ i, U i → R → N)
    (hG : ∀ i, Measurable (Function.uncurry (G i)))
    (hcompat : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j) r,
      G i ⟨x, hi⟩ r = G j ⟨x, hj⟩ r) :
    ∃ g : S → R → N, Measurable (Function.uncurry g) ∧
      ∀ i (x : S) (hx : (x : M) ∈ U i) r, g x r = G i ⟨x, hx⟩ r := by
  let V : ι → Set (M × R) := fun i ↦ U i ×ˢ univ
  let T : Set (M × R) := S ×ˢ univ
  let F : ∀ i, V i → N := fun i z ↦ G i ⟨z.1.1, z.2.1⟩ z.1.2
  have hF : ∀ i, Measurable (F i) := by
    intro i
    exact (hG i).comp
      (measurable_subtype_coe.fst.subtype_mk.prodMk measurable_subtype_coe.snd)
  have hFT : ∀ i j z (hi : z ∈ V i) (hj : z ∈ V j),
      F i ⟨z, hi⟩ = F j ⟨z, hj⟩ := by
    intro i j z hi hj
    exact hcompat i j z.1 hi.1 hj.1 z.2
  have hT : T ⊆ ⋃ i, V i := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hz.1)
    exact mem_iUnion.mpr ⟨i, hi, mem_univ z.2⟩
  let f : T → N := iUnionLift V F hFT T hT
  have hf : Measurable f :=
    measurable_iUnionLift hFT hT (fun i ↦ (hU i).prod MeasurableSet.univ) hF
  let q : S × R → T := fun z ↦ ⟨(z.1.1, z.2), z.1.2, mem_univ z.2⟩
  have hq : Measurable q :=
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd).subtype_mk
  refine ⟨fun x r ↦ f (q (x, r)), hf.comp hq, ?_⟩
  intro i x hx r
  exact iUnionLift_of_mem (q (x, r)) (show (q (x, r) : M × R) ∈ V i from
    ⟨hx, mem_univ r⟩)


namespace IsSmoothStronglyConvex

variable [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The original potential determines a jointly measurable complete curve family on its
intrinsic regular domain, with the original point and actual differential as initial data. -/
theorem exists_measurable_potential_global_family (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (u : M → ℝ) :
    ∃ G : F.potentialRegularDomain u → ℝ → M,
      (∀ x, F.IsEulerLagrangeOn (G x) univ) ∧ Measurable (Function.uncurry G) ∧
      ∀ x, G x 0 = x.val ∧ ∃ v : TangentSpace 𝓘(ℝ, E) x.val, v ≠ 0 ∧
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (G x) ⟨0, (1 : ℝ)⟩ = ⟨x.val, v⟩ ∧
        fderiv ℝ (F.fiberEnergy x.val) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x.val := by
  obtain ⟨C, hC, heq⟩ := hF.exists_countable_potentialLegendre_cover hcomplete u
  let _instPotentialGlobalChartCountable : Countable C := hC.to_subtype
  choose G hEL hm hi using fun old : M ↦
    hF.exists_measurable_potential_chart_family hcomplete old u
  let U : C → Set M := fun old ↦ F.potentialLegendreDomain old.val u
  have hcover : F.potentialRegularDomain u ⊆ ⋃ old : C, U old := by
    intro x hx
    rw [heq] at hx
    obtain ⟨old, ho, hxo⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨⟨old, ho⟩, hxo⟩
  have hcompat : ∀ i j : C, ∀ x (hi : x ∈ U i) (hj : x ∈ U j) t,
      G i.val ⟨x, hi⟩ t = G j.val ⟨x, hj⟩ t := by
    intro i j x hxi hxj t
    obtain ⟨_, v, hv, hvi, hpv⟩ := hi i.val ⟨x, hxi⟩
    obtain ⟨_, w, hw, hwi, hpw⟩ := hi j.val ⟨x, hxj⟩
    have hc := hF.eq_of_complete_initial_fiberEnergy_covectors
      (hEL i.val ⟨x, hxi⟩) (hEL j.val ⟨x, hxj⟩) x hv hw hvi hwi (hpv.trans hpw.symm)
    exact congrFun hc t
  obtain ⟨g, hgm, hge⟩ := exists_jointlyMeasurable_glue (F.potentialRegularDomain u) U
    (fun old ↦ hF.measurableSet_potentialLegendreDomain old.val u) hcover
    (fun old ↦ G old.val) (fun old ↦ hm old.val) hcompat
  have heach : ∀ x : F.potentialRegularDomain u,
      ∃ old : C, ∃ hx : x.val ∈ U old, g x = G old.val ⟨x.val, hx⟩ := by
    intro x
    obtain ⟨old, hx⟩ := mem_iUnion.mp (hcover x.property)
    exact ⟨old, hx, funext (hge old x hx)⟩
  refine ⟨g, ?_, hgm, ?_⟩
  · intro x
    obtain ⟨old, hx, hxe⟩ := heach x
    rw [hxe]
    exact hEL old.val ⟨x.val, hx⟩
  · intro x
    obtain ⟨old, hx, hxe⟩ := heach x
    rw [hxe]
    exact hi old.val ⟨x.val, hx⟩

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
