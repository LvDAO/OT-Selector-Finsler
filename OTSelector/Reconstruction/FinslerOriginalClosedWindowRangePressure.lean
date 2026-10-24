import OTSelector.Reconstruction.FinslerOriginalClosedWindowPressureIdentification
import OTSelector.Reconstruction.OriginalMarkedScalePressurePullback

/-! Exact scalar-range pullback identifies the actual measurable original
retained pressure with the continuous pressure used by physical class models. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- Normalizing the fixed actual range lift gives exactly the two original
normalized canonical-kernel marginals under the literal scalar readout. -/
theorem PopulationLocalPressureCore.originalClosedWindow_range_marginals
    {range : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    (π : Measure (range × range))
    (hmap : π.map (Prod.map Subtype.val Subtype.val) = γ ref.val)
    (law : ProbabilityMeasure (range × range))
    (hlaw : (law : Measure _) = normalizedFiniteLaw
      (π.restrict ((Prod.map Subtype.val Subtype.val) ⁻¹'
        (D.haar.continuous.coefficient i).window.region))) :
    let χ := D.originalClosedWindowPairKernel hcomplete γ
    ((law.map measurable_fst.aemeasurable : Measure range).map Subtype.val =
      (originalNormalizedRetainedPairKernel χ).map Prod.fst ref.val) ∧
    ((law.map measurable_snd.aemeasurable : Measure range).map Subtype.val =
      (originalNormalizedRetainedPairKernel χ).map Prod.snd ref.val) := by
  let C := D.haar.continuous.coefficient i
  let χ := D.originalClosedWindowPairKernel hcomplete γ
  let read : range × range → ℝ × ℝ := Prod.map Subtype.val Subtype.val
  have hread : Measurable read := measurable_subtype_coe.prodMap measurable_subtype_coe
  have hraw : (π.restrict (read ⁻¹' C.window.region)).map read =
      (γ ref.val).restrict C.window.region := by
    rw [← Measure.restrict_map hread C.window.isCompact_region.measurableSet,hmap]
  have hnorm : (law : Measure (range × range)).map read =
      normalizedFiniteLaw ((γ ref.val).restrict C.window.region) := by
    rw [hlaw,normalizedFiniteLaw_map _ read hread,hraw]
  have hmass : 0 < (χ ref.val).real univ := (sub_pos.mpr hδ1).trans
    (D.originalClosedWindowPairKernel_mass_lower γ hcomplete hgap hδ i ref)
  have hkernel : originalNormalizedRetainedPairKernel χ ref.val =
      normalizedFiniteLaw ((γ ref.val).restrict C.window.region) := by
    rw [originalNormalizedRetainedPairKernel_apply_eq χ ref.val hmass,
      D.originalClosedWindowPairKernel_eq_on_piece hcomplete γ i ref.val ref.property]
  constructor
  · change ((law : Measure (range × range)).map Prod.fst).map Subtype.val = _
    have hcompose : ((law : Measure (range × range)).map Prod.fst).map Subtype.val =
        ((law : Measure (range × range)).map read).map Prod.fst := by
      rw [Measure.map_map measurable_subtype_coe measurable_fst,Measure.map_map measurable_fst hread]
      rfl
    rw [hcompose,hnorm,Kernel.map_apply _ measurable_fst,hkernel]
  · change ((law : Measure (range × range)).map Prod.snd).map Subtype.val = _
    have hcompose : ((law : Measure (range × range)).map Prod.snd).map Subtype.val =
        ((law : Measure (range × range)).map read).map Prod.snd := by
      rw [Measure.map_map measurable_subtype_coe measurable_snd,Measure.map_map measurable_snd hread]
      rfl
    rw [hcompose,hnorm,Kernel.map_apply _ measurable_snd,hkernel]

/-- At AE actual original roots, every exact original range lift has exactly
the measurable b-probe pressure, at all real scales and all physical tilts.
This connects the continuous target of physical class refinement to that same
canonical original root pressure. -/
theorem PopulationLocalPressureCore.ae_originalClosedWindow_scalePressure_eq_range
    {range : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂μ, b (a x,u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y,u y) = y)
    (hlabel : ν.map a = μ.map a)
    (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (f : M × M →ᵇ ℝ) (i : Fin D.haar.continuous.count) :
    let C := D.haar.continuous.coefficient i
    let χ := D.originalClosedWindowPairKernel hcomplete γ
    ∀ᵐ z ∂(μ.map a).restrict C.roots, ∀ hz : z ∈ C.roots,
      ∀ (π : Measure (range × range)), π.map (Prod.map Subtype.val Subtype.val) = γ z →
      ∀ law : ProbabilityMeasure (range × range), (law : Measure _) = normalizedFiniteLaw
        (π.restrict ((Prod.map Subtype.val Subtype.val) ⁻¹' C.window.region)) → ∀ R t,
        originalSeedRetainedScalePressure (P C.seedIndex).seed a χ b f R t z =
          legalMarkedScalePressure (finrank ℝ (P C.seedIndex).seed.covector.ker) Subtype.val Subtype.val
            (law.map measurable_fst.aemeasurable : Measure range)
            (law.map measurable_snd.aemeasurable : Measure range)
            (fun x y w ↦ matrixQuadratic (C.matrix z (x.val,y.val)) w)
            (C.originalRangeClockProbe z hz f) R t := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let χ := D.originalClosedWindowPairKernel hcomplete γ
  have hphysical := D.ae_originalClosedWindow_scalePressure_eq_core γ hF hcomplete hu ha hinj horder
    hb hμreg hνreg hμinv hνinv hlabel hgap hδ hδ1 f i
  filter_upwards [hphysical] with z hscale
  intro hz π hmap law hlaw R t
  have hmarg := D.originalClosedWindow_range_marginals γ hcomplete hgap hδ hδ1 i ⟨z,hz⟩ π hmap law hlaw
  have hkin : Measurable (fun p : (ℝ × ℝ) ×
      (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) ↦
        matrixQuadratic (C.matrix z p.1) p.2) :=
    (measurable_originalSeedRootKinetic (P C.seedIndex).seed hF hcomplete hu ha hinj).comp
      measurable_prodMk_left
  have hprobe : Measurable (fun p : ℝ × ℝ ↦ originalReferenceClockProbe C z hz f p) :=
    (continuous_originalReferenceClockProbe C hF z hz f f.continuous).measurable
  have hpull := legalMarkedScalePressure_eq_pullback
    (finrank ℝ (P C.seedIndex).seed.covector.ker)
    (law.map measurable_fst.aemeasurable : Measure range)
    (law.map measurable_snd.aemeasurable : Measure range)
    ((originalNormalizedRetainedPairKernel χ).map Prod.fst z)
    ((originalNormalizedRetainedPairKernel χ).map Prod.snd z)
    measurable_subtype_coe measurable_subtype_coe hmarg.1 hmarg.2 measurable_id measurable_id
    (fun x y w ↦ matrixQuadratic (C.matrix z (x,y)) w) hkin
    (fun x y ↦ originalReferenceClockProbe C z hz f (x,y)) hprobe R t
  exact (hscale hz R t).trans (by
    convert hpull using 1
    all_goals rfl)

end OTSelector.Reconstruction
