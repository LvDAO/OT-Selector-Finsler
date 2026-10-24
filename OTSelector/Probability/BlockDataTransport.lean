import OTSelector.Probability.PoissonRestriction

/-! Exact coordinate transport of the original finite observations. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Apply the actual point map to every used observation, preserving its count
and original enumeration. -/
def mapBlockData (f : X → Y) (d : BlockData X) : BlockData Y :=
  ⟨d.1, fun i ↦ f (d.2 i)⟩

theorem measurable_mapBlockData {f : X → Y} (hf : Measurable f) :
    Measurable (mapBlockData f) := by
  intro U hU
  change MeasurableSet[⨅ n : ℕ,
    (inferInstance : MeasurableSpace (Fin n → X)).map (Sigma.mk n)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  exact ((measurable_sigma_mk n).comp
    (measurable_pi_lambda _ fun i ↦ hf.comp (measurable_pi_apply i))) hU

/-- Transporting finite observations transports the point law and leaves the
original count distribution unchanged. -/
theorem blockDataLaw_mapPoints (ν : Measure X) [IsProbabilityMeasure ν]
    (ρ : Measure Y) [IsProbabilityMeasure ρ] {f : X → Y}
    (hf : Measurable f) (hlaw : ν.map f = ρ) (prob : ℕ → ℝ≥0∞) :
    (blockDataLaw ν prob).map (mapBlockData f) = blockDataLaw ρ prob := by
  let _inst : IsProbabilityMeasure (ν.map f) := hlaw.symm ▸ inferInstance
  have hpi (n : ℕ) : (Measure.pi (fun _ : Fin n ↦ ν)).map
      (fun x : Fin n → X ↦ fun i ↦ f (x i)) = Measure.pi (fun _ : Fin n ↦ ρ) := by
    rw [Measure.pi_map_pi (fun _ : Fin n ↦ hf.aemeasurable)]
    simp only [hlaw]
  rw [blockDataLaw, Measure.map_sum (measurable_mapBlockData hf).aemeasurable, blockDataLaw]
  congr 1
  funext n
  rw [Measure.map_smul]
  congr 1
  calc
    _ = (Measure.pi (fun _ : Fin n ↦ ν)).map
        (fun x ↦ (⟨n, fun i ↦ f (x i)⟩ : BlockData Y)) := by
      rw [Measure.map_map (measurable_mapBlockData hf) (measurable_sigma_mk n)]
      rfl
    _ = ((Measure.pi (fun _ : Fin n ↦ ν)).map
        (fun x : Fin n → X ↦ fun i ↦ f (x i))).map (Sigma.mk n) := by
      rw [Measure.map_map (measurable_sigma_mk n)
        (measurable_pi_lambda _ fun i ↦ hf.comp (measurable_pi_apply i))]
      rfl
    _ = _ := by rw [hpi]

omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- Restricting original observations and then changing coordinates is exactly
restriction in the new coordinates, using the preimage of the same shape. -/
theorem mapBlockData_restrictedPrefix (f : X → Y) (S : Set Y)
    (z : ℕ × (ℕ → X)) :
    mapBlockData f (restrictedPrefix (f ⁻¹' S) z) =
      restrictedPrefix S (z.1, fun i ↦ f (z.2 i)) := rfl


/-- Original normalized shape restrictions transport by preimage; the finite
count law remains literal, including zero-mass fallback shapes. -/
theorem blockDataLaw_restricted_mapPoints (ν : Measure X) [IsProbabilityMeasure ν]
    (ρ : Measure Y) [IsProbabilityMeasure ρ] {f : X → Y}
    (hf : Measurable f) (hlaw : ν.map f = ρ) {S : Set Y} (hS : MeasurableSet S)
    (prob : ℕ → ℝ≥0∞) :
    (blockDataLaw (restrictedPointLaw ν (f ⁻¹' S)) prob).map (mapBlockData f) =
      blockDataLaw (restrictedPointLaw ρ S) prob := by
  apply blockDataLaw_mapPoints _ _ hf _ prob
  rw [← restrictedPointLaw_map ν hf hS, hlaw]

/-- A coordinate map preserves the exact original shape count intensity. -/
theorem restrictionWeight_mapPoints (ν : Measure X) [IsProbabilityMeasure ν]
    (ρ : Measure Y) [IsProbabilityMeasure ρ] {f : X → Y}
    (hf : Measurable f) (hlaw : ν.map f = ρ) {S : Set Y} (hS : MeasurableSet S) :
    restrictionWeight ν (f ⁻¹' S) = restrictionWeight ρ S := by
  unfold restrictionWeight
  rw [← hlaw, Measure.map_apply hf hS]

end OTSelector.Probability
