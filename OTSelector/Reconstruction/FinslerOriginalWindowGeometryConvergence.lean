import OTSelector.Reconstruction.FinslerOriginalClockPressureFreezing
import OTSelector.Reconstruction.FinslerOriginalConditionalLawConvergence

/-! Actual conditional-law variation on the original Finsler continuity cores
passes exactly through scalar-range lifts and arbitrary retained pairings. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The actual compact original geometry and physical reconstruction
produce uniform coefficient/probe convergence along approaching original
roots. No error sequence, rank condition or probe regularity callback is added. -/
theorem PopulationLocalPressureCore.original_window_geometry_eventually
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count)
    (z : ℕ → (D.haar.continuous.coefficient i).roots)
    (ref : (D.haar.continuous.coefficient i).roots) (hz : Tendsto z atTop (𝓝 ref))
    (f : M × M →ᵇ ℝ) :
    ∀ ε > 0, ∀ η > 0, ∀ᶠ n in atTop,
      ∀ p ∈ (D.haar.continuous.coefficient i).window.region,
        (∀ w, |matrixQuadratic ((D.haar.continuous.coefficient i).matrix (z n).val p) w -
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix ref.val p) w| ≤
            ε * matrixQuadratic ((D.haar.continuous.coefficient i).matrix ref.val p) w) ∧
        |originalReferenceClockProbe (D.haar.continuous.coefficient i) (z n).val (z n).property f p -
          originalReferenceClockProbe (D.haar.continuous.coefficient i) ref.val ref.property f p| ≤ η := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  letI : MetricSpace (ℚ → M) := TopologicalSpace.metrizableSpaceMetric (ℚ → M)
  let C := D.haar.continuous.coefficient i
  have hzval : Tendsto (fun n ↦ (z n).val) atTop (𝓝 ref.val) :=
    continuous_subtype_val.continuousAt.tendsto.comp hz
  intro ε hε η hη
  obtain ⟨radius,hradius,hfreeze⟩ := exists_uniform_relative_matrixQuadratic
    (C.roots_compact.prod C.window.isCompact_region) C.coefficient_continuous
    (fun p hp ↦ C.coefficient_posDef p.1 hp.1 p.2 hp.2) hε
  obtain ⟨U,hU,hgeometry⟩ := D.exists_original_pair_geometry_neighborhoods
    hF hcomplete hu ha hinj i f f.continuous hε hη zero_lt_one
  have hnear : ∀ᶠ n in atTop, (z n).val ∈ Metric.ball ref.val radius :=
    hzval (Metric.ball_mem_nhds ref.val hradius)
  have hneigh : ∀ᶠ n in atTop, (z n).val ∈ U ref.val :=
    hzval ((hU ref.val).1.mem_nhds (hU ref.val).2)
  filter_upwards [hnear,hneigh] with n hn hnu
  intro p hp
  constructor
  · apply hfreeze ((z n).val,p) ⟨(z n).property,hp⟩ (ref.val,p) ⟨ref.property,hp⟩
    simpa only [Prod.dist_eq,dist_self,max_eq_left (dist_nonneg),Metric.mem_ball] using hn
  · have hphysical := (hgeometry ref.val ref.property (z n).val ⟨(z n).property,hnu⟩
      (z n).val ⟨(z n).property,hnu⟩).2.2 p.1 hp.1.1 p.2 hp.1.2
    have heq (w : ℚ → M) (hw : w ∈ C.roots) :
        originalReferenceClockProbe C w hw f p =
          f (D.corePoint i (w,p.1),D.corePoint i (w,p.2)) := by
      dsimp only [originalReferenceClockProbe,PopulationLocalPressureCore.corePoint]
      rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj C.seedIndex
        ⟨w,C.roots_subset_piece hw⟩]
    rw [← heq (z n).val (z n).property,← heq ref.val ref.property] at hphysical
    exact hphysical

end OTSelector.Reconstruction
