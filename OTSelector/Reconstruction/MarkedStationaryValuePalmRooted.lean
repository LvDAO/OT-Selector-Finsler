import OTSelector.Reconstruction.MarkedStationaryValuePalmCube

/-!
# Rooted Campbell factorization on original multidimensional random measures

The Palm measure is constructed from the actual original environment law,
random counting kernel and physical reroot. Its factorization and normalization
follow from the proved invariance and actual unit-cube moment.
-/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
variable {ι Ω M : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace M]

/-- The literal multidimensional Palm readout is the original environment and
counted root restricted to its original spatial unit cube. -/
theorem cubePalm_rootedCampbell_eq (P : Measure Ω) [SFinite P]
    (N : Kernel Ω (ι → ℝ)) [IsSFiniteKernel N]
    (reroot : Ω × (ι → ℝ) → M) (hr : Measurable reroot) :
    cubePalm ι (rootedCampbell P N reroot) =
      ((P ⊗ₘ N).restrict (univ ×ˢ palmUnitCube ι)).map reroot := by
  ext B hB
  rw [cubePalm_apply ι _ hB,
    rootedCampbell_apply_prod P N reroot hr (measurableSet_palmUnitCube ι) hB,
    Measure.map_apply hr hB, Measure.restrict_apply (hr hB),
    Measure.compProd_apply ((hr hB).inter (MeasurableSet.univ.prod (measurableSet_palmUnitCube ι)))]
  congr 1
  funext w
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage, mem_inter_iff, mem_prod, mem_univ, true_and]
  exact and_comm

/-- Every nonnegative Palm observable is exactly an original unit-cube
point-rooted integral, with no independent auxiliary input law. -/
theorem lintegral_cubePalm_rootedCampbell (P : Measure Ω) [SFinite P]
    (N : Kernel Ω (ι → ℝ)) [IsSFiniteKernel N]
    (reroot : Ω × (ι → ℝ) → M) (hr : Measurable reroot)
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ m, f m ∂cubePalm ι (rootedCampbell P N reroot)) =
      ∫⁻ w, ∫⁻ x in palmUnitCube ι, f (reroot (w, x)) ∂N w ∂P := by
  rw [cubePalm_rootedCampbell_eq P N reroot hr, lintegral_map hf hr]
  simpa only [Measure.restrict_univ, Function.comp_def] using
    (Measure.setLIntegral_compProd (hf.comp hr) MeasurableSet.univ (measurableSet_palmUnitCube ι))

theorem cubePalm_rootedCampbell_univ (P : Measure Ω) [SFinite P]
    (N : Kernel Ω (ι → ℝ)) [IsSFiniteKernel N]
    (reroot : Ω × (ι → ℝ) → M) (hr : Measurable reroot) :
    cubePalm ι (rootedCampbell P N reroot) univ =
      ∫⁻ w, N w (palmUnitCube ι) ∂P := by
  rw [cubePalm_apply ι _ MeasurableSet.univ,
    rootedCampbell_apply_prod P N reroot hr (measurableSet_palmUnitCube ι) MeasurableSet.univ]
  simp only [mem_univ, and_true, ofPred_mem_eq]

omit [Fintype ι] in
/-- Actual environment covariance and the actual root cocycle supply spatial
invariance of the multidimensional rooted Campbell measure. -/
theorem measurePreserving_rootedCampbellCube_of_covariant (P : Measure Ω) [SFinite P]
    (N : Kernel Ω (ι → ℝ)) [IsSFiniteKernel N]
    (reroot : Ω × (ι → ℝ) → M) (hr : Measurable reroot)
    (a : ι → ℝ) {shift : Ω → Ω} (hshift : MeasurePreserving shift P P)
    (hN : ∀ᵐ w ∂P, N (shift w) = (N w).map (a + ·))
    (hrcov : ∀ᵐ w ∂P, ∀ᵐ x ∂N w, reroot (shift w, a + x) = reroot (w, x)) :
    MeasurePreserving (fun p : (ι → ℝ) × M ↦ (a + p.1, p.2))
      (rootedCampbell P N reroot) (rootedCampbell P N reroot) := by
  have hpoint (w : Ω) : Measurable (fun x : ι → ℝ ↦ (x, reroot (w, x))) :=
    measurable_id.prodMk (hr.comp measurable_prodMk_left)
  have hadd : Measurable (fun x : ι → ℝ ↦ a + x) := measurable_const.add measurable_id
  have hloc : Measurable (fun p : (ι → ℝ) × M ↦ (a + p.1, p.2)) :=
    (measurable_const.add measurable_fst).prodMk measurable_snd
  rw [rootedCampbell_eq_bind P N reroot hr]
  apply measurePreserving_bind_of_covariant P (rootedPointKernel N reroot)
    (Kernel.measurable _) hshift hloc
  filter_upwards [hN, hrcov] with w hNw hrw
  rw [rootedPointKernel_apply N reroot hr, rootedPointKernel_apply N reroot hr, hNw,
    Measure.map_map (hpoint (shift w)) hadd, Measure.map_map hloc (hpoint w)]
  apply Measure.map_congr
  filter_upwards [hrw] with x hx
  exact Prod.ext rfl hx

/-- Genuine multidimensional Campbell/Palm factorization from the original
stationary environment and original counting kernel. -/
theorem rootedCampbell_eq_volume_prod_cubePalm (P : Measure Ω) [SFinite P]
    (N : Kernel Ω (ι → ℝ)) [IsSFiniteKernel N]
    (reroot : Ω × (ι → ℝ) → M) (hr : Measurable reroot)
    (shift : (ι → ℝ) → Ω → Ω) (hshift : ∀ a, MeasurePreserving (shift a) P P)
    (hN : ∀ a, ∀ᵐ w ∂P, N (shift a w) = (N w).map (a + ·))
    (hrcov : ∀ a, ∀ᵐ w ∂P, ∀ᵐ x ∂N w,
      reroot (shift a w, a + x) = reroot (w, x))
    (hunit : (∫⁻ w, N w (palmUnitCube ι) ∂P) < ∞) :
    rootedCampbell P N reroot = (volume : Measure (ι → ℝ)).prod
      (cubePalm ι (rootedCampbell P N reroot)) := by
  apply campbell_eq_volume_prod_cubePalm
  · intro a
    exact measurePreserving_rootedCampbellCube_of_covariant P N reroot hr a (hshift a)
      (hN a) (hrcov a)
  · rw [rootedCampbell_apply_prod P N reroot hr (measurableSet_palmUnitCube ι) MeasurableSet.univ]
    simpa only [mem_univ, and_true, ofPred_mem_eq] using hunit

/-- Unit original spatial intensity normalizes the constructed Palm measure
without prescribing any Palm law or independent replacement process. -/
theorem isProbabilityMeasure_cubePalm_rootedCampbell
    (P : Measure Ω) [SFinite P] (N : Kernel Ω (ι → ℝ)) [IsSFiniteKernel N]
    (reroot : Ω × (ι → ℝ) → M) (hr : Measurable reroot)
    (hunit : (∫⁻ w, N w (palmUnitCube ι) ∂P) = 1) :
    IsProbabilityMeasure (cubePalm ι (rootedCampbell P N reroot)) := by
  constructor
  rw [cubePalm_rootedCampbell_univ P N reroot hr, hunit]

end OTSelector.Reconstruction
