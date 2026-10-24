import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import OTSelector.MeasureTheory.CompactFiniteQuantization
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiCompactGrid.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiCompactGrid`; the selected original proof blocks follow. -/
section

/-!
Conditions: A nonempty compact subset of a measurable normed space and a positive grid tolerance.

Objects: A measurable finite-index quantizer with every node in the original compact carrier and an explicit quadratic diameter bound.

Proof detail: Take a finite ball cover, choose a deterministic first admissible node on its measurable cells and use the compact diameter inequality.

Sources: Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110); D. H. Fremlin, Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces (https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106).
Relation: Compact total-boundedness/finite-cell construction; no probabilistic selection or replacement carrier is introduced.
-/

/-! Actual finite-index grids whose every node lies in the original compact
carrier, with the genuine original density-cell laws and quadratic geometry. -/
open Set MeasureTheory Metric
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1400000

/-- Every nonempty compact normed carrier admits a measurable finite-index
grid using only original carrier nodes, including its fallback node. -/
theorem exists_compact_measurable_finiteIndex_grid
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {K : Set E} (hK : IsCompact K) (hKne : K.Nonempty) {h : ℝ} (hh : 0<h) :
    ∃s:Finset E,s.Nonempty ∧ (↑s:Set E)⊆K ∧
      ∃T:E→s,Measurable T ∧ ∀z∈K,‖(T z:E)-z‖≤h := by
  classical
  obtain ⟨z₀,hz₀⟩:=hKne
  obtain ⟨Q,hQ,hfin,hnodes,hnear⟩:=exists_compact_measurable_finiteRange_grid hK z₀ hh
  let s:=hfin.toFinset
  let T:E→s:=fun z↦⟨Q z,hfin.mem_toFinset.mpr ⟨z,rfl⟩⟩
  refine ⟨s,⟨Q z₀,hfin.mem_toFinset.mpr ⟨z₀,rfl⟩⟩,?_,T,?_,?_⟩
  · intro z hz
    have hz':=hnodes (hfin.mem_toFinset.mp hz)
    exact hz'.elim (fun heq↦heq ▸ hz₀) id
  · exact hQ.subtype_mk
  · intro z hz
    simpa only [dist_eq_norm] using (hnear z hz).le

/-- Carrier diameter bounds every branch distance and every quadratic node
cost of a grid that stays in the original compact carrier. -/
theorem compact_grid_quadratic_geometry
    {E : Type*} [NormedAddCommGroup E] {K : Set E} (hK : IsCompact K)
    {I : Type*} (x : I→E) (hx : ∀i,x i∈K) :
    (∀z∈K,∀i,‖z-x i‖≤Metric.diam K) ∧
      (∀i j,‖x j-x i‖^2/2≤(Metric.diam K)^2/2) := by
  have hbranch : ∀z∈K,∀i,‖z-x i‖≤Metric.diam K := by
    intro z hz i
    simpa only [dist_eq_norm] using Metric.dist_le_diam_of_mem hK.isBounded hz (hx i)
  refine ⟨hbranch,fun i j↦?_⟩
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hbranch (x j) (hx j) i) 2)
    (by norm_num)

end OTSelector.Reconstruction

end
end
