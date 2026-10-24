import OTSelector.Reconstruction.OriginalIIDBipartiteMacroScene
import OTSelector.Probability.CommonIteratedWeakSubsequence

/-! The actual original two iid input clouds and macroscopic labels retain
one common weak sample subsequence across all countably many root frames. -/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {M : Type*} [MeasurableSpace M]
local instance commonBipartiteMacroStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance commonBipartiteMacroConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance commonBipartiteMacroConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance commonBipartiteMacroConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance commonBipartiteMacroPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- A single sample subsequence gives compatible joint two-input/macro limits in all
frames even when the actual optimal-assignment cost varies with sample size. -/
theorem exists_originalIID_common_bipartite_macro_subsequence_varying_cost
    (axes : ℕ → Type*) [∀ j, Fintype (axes j)] (hq : ∀ j, 0 < Fintype.card (axes j))
    (base : ∀ j, (axes j → ℝ) × ℝ)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : ℕ → M → M → ℝ)
    (hcost : ∀ n, Measurable (Function.uncurry (cost n))) (k : ℕ → ℝ)
    (H : ℕ → Set M) (hH : ∀ j, MeasurableSet (H j))
    (coord : ∀ j, ℕ → M → (axes j → ℝ)) (hcoord : ∀ j n, Measurable (coord j n))
    (u : M → ℝ) (hu : Measurable u) :
    let S := fun j ↦ (axes j → ℝ) ×
      (CavityLocalScene ((axes j → ℝ) × ℝ) ((axes j → ℝ) × ℝ) × LocalConfiguration (base j))
    let laws := fun j n ↦ originalIIDBipartiteMacroLaw (base j) μ ν (hq j)
      (cost n) (hcost n) (k n) n (H j) (hH j) (coord j n) (hcoord j n) u hu
    ∃ Q : ∀ j, ProbabilityMeasure (S j × S j), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j, Tendsto (fun n ↦ laws j (φ n)) atTop (𝓝 (Q j)) := by
  intro S laws
  have htight (j : ℕ) : IsTightMeasureSet
      (range (fun v : ℕ × ℕ ↦ (laws j v.2 : Measure (S j × S j)))) := by
    have h := isTightMeasureSet_originalIIDBipartiteMacroLaw_varying_cost (base j) μ ν (hq j)
      cost hcost k (H j) (hH j) (coord j) (hcoord j) u hu
    convert h using 1
    ext ρ
    constructor
    · rintro ⟨⟨ℓ,n⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨(0,n), rfl⟩
  obtain ⟨Q, φ, hφ, hinner, _⟩ :=
    exists_common_iterated_probabilityMeasure_subseq_of_isTight
      (fun j (_ : ℕ) n ↦ laws j n) htight
  exact ⟨fun j ↦ Q j 0, φ 0, hφ 0, fun j ↦ hinner j 0⟩

/-- The actual jointly observed original finite plans, both original counted
inputs and original macro roots have compatible limits on one sample
subsequence in all countably many frames. No input/plan correlation is replaced. -/
theorem exists_originalIID_common_bipartite_macro_subsequence
    (axes : ℕ → Type*) [∀ j, Fintype (axes j)] (hq : ∀ j, 0 < Fintype.card (axes j))
    (base : ∀ j, (axes j → ℝ) × ℝ)
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost)) (k : ℕ → ℝ)
    (H : ℕ → Set M) (hH : ∀ j, MeasurableSet (H j))
    (coord : ∀ j, ℕ → M → (axes j → ℝ)) (hcoord : ∀ j n, Measurable (coord j n))
    (u : M → ℝ) (hu : Measurable u) :
    let S := fun j ↦ (axes j → ℝ) ×
      (CavityLocalScene ((axes j → ℝ) × ℝ) ((axes j → ℝ) × ℝ) × LocalConfiguration (base j))
    let laws := fun j n ↦ originalIIDBipartiteMacroLaw (base j) μ ν (hq j)
      cost hcost (k n) n (H j) (hH j) (coord j n) (hcoord j n) u hu
    ∃ Q : ∀ j, ProbabilityMeasure (S j × S j), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j, Tendsto (fun n ↦ laws j (φ n)) atTop (𝓝 (Q j)) := by
  exact exists_originalIID_common_bipartite_macro_subsequence_varying_cost axes hq base μ ν
    (fun _ ↦ cost) (fun _ ↦ hcost) k H hH coord hcoord u hu

end OTSelector.Reconstruction
