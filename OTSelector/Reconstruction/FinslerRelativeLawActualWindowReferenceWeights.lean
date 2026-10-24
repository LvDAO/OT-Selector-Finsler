import OTSelector.Reconstruction.FinslerRelativeLawWindowSamplingClassPopulation
import OTSelector.Reconstruction.FinslerConcreteUpperClassPressure

/-! Literal retained reference weights from the original conditional pair law. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore
variable (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ) (I : Set ℝ)
  (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
    (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r δ loss)

/-- Fixed physical Haar/class weights: the original reference pair flow,
thinned by 1−η, multiplied by its original Haar intensity and retained on the
actual pair-window class mask. Its total remains in the physical intensity. -/
def originalWindowReferenceWeights (i : Fin D.haar.continuous.count)
    (ref : (D.haar.continuous.coefficient i).roots) {width : ℝ}
    (Q : FiniteScalarBins I width) (η : ℝ) : Fin Q.count → Fin Q.count → ℝ :=
  maskedClockFlow ((D.haar.continuous.coefficient i).clockClassAllowed Q)
    (fun j k ↦ (1 - η) * (D.rootIntensity i ref.val *
      actualClockClassFlow (γ ref.val) Q.cell Q.cell j k))

omit [BorelSpace E] [T2Space M] [PreconnectedSpace M] [BorelSpace M] [IsMarkovKernel γ] in
/-- The exact actual population split has precisely these unchanged fixed
reference weights divided by the original root intensity. -/
theorem originalWindowReferenceWeights_div (i : Fin D.haar.continuous.count)
    (ref : (D.haar.continuous.coefficient i).roots) {width : ℝ}
    (Q : FiniteScalarBins I width) (η : ℝ) (z : ℚ → M) (j k : Fin Q.count) :
    maskedClockFlow
      (fun j k ↦ ((Q.cell j ×ˢ Q.cell k) ∩ (D.haar.continuous.coefficient i).window.region).Nonempty)
      (fun j k ↦ (1 - η) * (D.rootIntensity i ref.val *
        actualClockClassFlow (γ ref.val) Q.cell Q.cell j k) / D.rootIntensity i z) j k =
      D.originalWindowReferenceWeights γ gap I i ref Q η j k / D.rootIntensity i z := by
  have he (j k : Fin Q.count) :
      ((Q.cell j ×ˢ Q.cell k) ∩ (D.haar.continuous.coefficient i).window.region).Nonempty ↔
        (D.haar.continuous.coefficient i).clockClassAllowed Q j k := by
    simp only [OriginalPopulationCoefficientCore.clockClassAllowed, nonempty_def, mem_inter_iff, mem_prod]
    aesop
  simp only [he, originalWindowReferenceWeights, maskedClockFlow]
  split_ifs <;> simp only [zero_div]

omit [BorelSpace E] [BorelSpace M] in
/-- The original positive Haar density and original pair-window loss give
nonnegative, nonzero retained weights with an explicit mass lower bound.
Full global clock bins cover the original marginals; the local pair window is
used only for its original joint-law loss. -/
theorem originalWindowReferenceWeights_mass (i : Fin D.haar.continuous.count)
    (ref : (D.haar.continuous.coefficient i).roots) {width : ℝ}
    (Q : FiniteScalarBins I width) {η : ℝ} (hη : η < 1)
    (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) :
    (∀ j k, 0 ≤ D.originalWindowReferenceWeights γ gap I i ref Q η j k) ∧
    (∀ j k, ¬(D.haar.continuous.coefficient i).clockClassAllowed Q j k →
      D.originalWindowReferenceWeights γ gap I i ref Q η j k = 0) ∧
    (1 - η) * D.rootIntensity i ref.val * (1 - δ.toReal) ≤
      (∑ j, ∑ k, D.originalWindowReferenceWeights γ gap I i ref Q η j k) ∧
    0 < ∑ j, ∑ k, D.originalWindowReferenceWeights γ gap I i ref Q η j k := by
  let _instMetric : MetricSpace M := F.metricSpace
  let C := D.haar.continuous.coefficient i
  let A := actualClockClassFlow (γ ref.val) Q.cell Q.cell
  let keep := C.clockClassAllowed Q
  have href : ref.val ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i, ref.property⟩
  have hgood := (D.haar.continuous.population.good ref.val href).1
  have hcoverS : ∀ᵐ s ∂condDistrib u a μ ref.val, s ∈ ⋃ j, Q.cell j := by
    simpa only [Q.union_eq] using hgood.2.2.1
  have hcoverT : ∀ᵐ t ∂condDistrib u a ν ref.val, t ∈ ⋃ k, Q.cell k := by
    simpa only [Q.union_eq] using hgood.2.2.2
  have hf := actualClockClassFlow_original_feasible_at (γ ref.val)
    (condDistrib u a μ ref.val) (condDistrib u a ν ref.val) hgood.1
    Q.cell Q.cell Q.measurable_cell Q.measurable_cell Q.disjoint Q.disjoint hcoverS hcoverT
    (fun _ _ ↦ True) (fun _ ↦ True) (Filter.Eventually.of_forall fun _ ↦ trivial)
    (fun _ _ _ _ _ _ _ ↦ trivial)
  have htotal : (∑ j, ∑ k, A j k) = 1 := hf.2.2.2.2
  have hloss := C.coupling_loss ref.val ref.property (γ ref.val) hgood.1
    (hgood.2.1.mono fun p hp ↦ by linarith)
  have hbad := actualClockClassFlow_masked_mass_le (γ ref.val) Q.cell Q.cell
    Q.measurable_cell Q.measurable_cell Q.disjoint Q.disjoint C.window.region
    (fun j k ↦ ¬ keep j k) (fun j k hnot p hp hH ↦ hnot ⟨p, hH, hp⟩)
  have hbadBound : (∑ j, ∑ k, maskedClockFlow (fun j k ↦ ¬keep j k) A j k) ≤ δ.toReal :=
    hbad.trans (ENNReal.toReal_mono hδ hloss.le)
  have hsplit : (∑ j, ∑ k, maskedClockFlow keep A j k) +
      (∑ j, ∑ k, maskedClockFlow (fun j k ↦ ¬keep j k) A j k) = 1 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, maskedClockFlow_add_complement]
    exact htotal
  have hmain : 1 - δ.toReal ≤ ∑ j, ∑ k, maskedClockFlow keep A j k := by linarith
  have hrefI : ref.val ∈ (D.haar.intensity i).roots := by
    rw [D.haar.intensity_roots]
    exact ref.property
  have hdpos : 0 < D.rootIntensity i ref.val := (D.haar.intensity i).lower_pos.trans_le
    ((D.haar.intensity i).bounds _ (mem_image_of_mem _ hrefI)).1
  have hscale : 0 < (1 - η) * D.rootIntensity i ref.val := mul_pos (sub_pos.mpr hη) hdpos
  have hentry (j k : Fin Q.count) : D.originalWindowReferenceWeights γ gap I i ref Q η j k =
      ((1 - η) * D.rootIntensity i ref.val) * maskedClockFlow keep A j k := by
    by_cases h : keep j k <;>
      simp only [originalWindowReferenceWeights, maskedClockFlow, keep, C] at h ⊢
    · simp only [h, ite_true, A]
      ring
    · simp only [h, ite_false, mul_zero]
  have hmass : (∑ j, ∑ k, D.originalWindowReferenceWeights γ gap I i ref Q η j k) =
      ((1 - η) * D.rootIntensity i ref.val) * (∑ j, ∑ k, maskedClockFlow keep A j k) := by
    simp_rw [hentry, ← Finset.mul_sum]
  have hbound : (1 - η) * D.rootIntensity i ref.val * (1 - δ.toReal) ≤
      ∑ j, ∑ k, D.originalWindowReferenceWeights γ gap I i ref Q η j k := by
    rw [hmass]
    exact mul_le_mul_of_nonneg_left hmain hscale.le
  refine ⟨?_, ?_, hbound, (mul_pos hscale (sub_pos.mpr hδ1)).trans_le hbound⟩
  · intro j k
    rw [hentry]
    apply mul_nonneg hscale.le
    exact (by dsimp only [maskedClockFlow]; split_ifs; exacts [hf.1 _ _, le_rfl])
  · intro j k hnot
    simp only [originalWindowReferenceWeights, maskedClockFlow, ite_eq_right hnot]

end PopulationLocalPressureCore
end OTSelector.Reconstruction
