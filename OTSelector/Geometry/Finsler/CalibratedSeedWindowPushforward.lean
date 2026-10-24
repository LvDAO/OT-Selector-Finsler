import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.CalibratedSeedWindowLabels
import OTSelector.Geometry.Finsler.CalibratedSeedWindowVolume
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Manifold.ManifoldTubeJacobian
import OTSelector.MeasureTheory.AreaFormula.ParameterizedJacobianMeasurable
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedSeedWindowPushforward.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedSeedWindowPushforward`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CalibratedSeedWindowPushforward

* **Conditions:** A Borel piece of an actual window with its pullback density and original injective label–clock map.
* **Objects:** A finite original transverse label reference and the exact joint law as its time-product density, extended by zero from legal coordinates.
* **Proof detail:** Prove the generic embedded withDensity pushforward rule, apply clock translation and product transport, then insert the original mass-piece indicator and geometric density.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.

Source relation (derived): Generic product/extension lemmas support the geometric assembly; the output is the original label–clock law.
-/

/-!
# Actual geometric densities on the original label-clock space

Every Borel piece of an original calibrated window pushes forward with its actual
normalized Jacobian and original chart density. The finite label reference is the
original seed Haar measure on the bounded base, retaining its normalization.
-/

open Set MeasureTheory Manifold Metric
open scoped Topology ContDiff ENNReal

noncomputable section

private theorem map_withDensity_extend_of_map_eq_restrict
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {q : A → B} (hq : MeasurableEmbedding q) (μ : Measure A) (R : Measure B)
    (hmap : μ.map q = R.restrict (range q)) (d : A → ℝ≥0∞) (hd : Measurable d) :
    (μ.withDensity d).map q = R.withDensity (Function.extend q d 0) := by
  classical
  let G := Function.extend q d (0 : B → ℝ≥0∞)
  have hG : Measurable G := hq.measurable_extend hd measurable_const
  have hGq (x : A) : G (q x) = d x := hq.injective.extend_apply d 0 x
  have hzero : (range q).indicator G = G := by
    funext x
    by_cases hx : x ∈ range q
    · exact indicator_of_mem hx G
    · rw [indicator_of_notMem hx]
      exact (Function.extend_apply' d (0 : B → ℝ≥0∞) x hx).symm
  have hpush : (μ.withDensity d).map q = (μ.map q).withDensity G := by
    ext s hs
    rw [Measure.map_apply hq.measurable hs, withDensity_apply _ (hq.measurable hs),
      withDensity_apply _ hs, setLIntegral_map hs hG hq.measurable]
    simp only [hGq]
  rw [hpush, hmap, ← withDensity_indicator hq.measurableSet_range, hzero]

private theorem window_pushforward_product
    {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (κ : Measure W) [SFinite κ] {L : Set W} (hL : MeasurableSet L)
    {I : Set ℝ} (hI : MeasurableSet I)
    [SFinite (κ.comap ((↑) : L → W))]
    {e : L → Z} (he : MeasurableEmbedding e) (c : ℝ)
    (d : (I ×ˢ L) → ℝ≥0∞) (hd : Measurable d) :
    let q : (I ×ˢ L) → Z × ℝ := fun z ↦
      (e ⟨z.val.2, z.property.2⟩, c + z.val.1)
    let μpar := ((volume : Measure ℝ).prod κ).comap ((↑) : (I ×ˢ L) → ℝ × W)
    let k := κ.comap ((↑) : L → W)
    let β := k.map e
    MeasurableEmbedding q ∧
      (μpar.withDensity d).map q = (β.prod volume).withDensity (Function.extend q d 0) := by
  classical
  let q : (I ×ˢ L) → Z × ℝ := fun z ↦
    (e ⟨z.val.2, z.property.2⟩, c + z.val.1)
  let μpar := ((volume : Measure ℝ).prod κ).comap ((↑) : (I ×ˢ L) → ℝ × W)
  let k := κ.comap ((↑) : L → W)
  let τ := (volume : Measure ℝ).comap ((↑) : I → ℝ)
  let β := k.map e
  let r := MeasurableEquiv.Set.prod I L
  let T := MeasurableEquiv.addLeft c
  let j : I → ℝ := fun t ↦ c + t.val
  have hcoeI := MeasurableEmbedding.subtype_coe hI
  have hcoeL := MeasurableEmbedding.subtype_coe hL
  have hcoeD := MeasurableEmbedding.subtype_coe (hI.prod hL)
  have hτmap : τ.map ((↑) : I → ℝ) = volume.restrict I :=
    map_comap_subtype_coe hI volume
  have hτsigma : SigmaFinite τ :=
    SigmaFinite.of_map τ measurable_subtype_coe.aemeasurable (by
      rw [hτmap]
      infer_instance)
  have hj : MeasurableEmbedding j := T.measurableEmbedding.comp hcoeI
  have hq : MeasurableEmbedding q :=
    ((he.prodMap hj).comp
      (MeasurableEquiv.prodComm : (I × L) ≃ᵐ (L × I)).measurableEmbedding).comp
      r.measurableEmbedding
  have hpar : (τ.prod k).map r.symm = μpar := by
    apply hcoeD.map_injective
    rw [Measure.map_map hcoeD.measurable r.symm.measurable]
    change (τ.prod k).map (Prod.map ((↑) : I → ℝ) ((↑) : L → W)) =
      μpar.map ((↑) : (I ×ˢ L) → ℝ × W)
    rw [← Measure.map_prod_map τ k measurable_subtype_coe measurable_subtype_coe,
      hτmap, map_comap_subtype_coe hL, map_comap_subtype_coe (hI.prod hL),
      Measure.prod_restrict]
  have hjmap : τ.map j = volume.restrict (T '' I) := by
    change τ.map (T ∘ ((↑) : I → ℝ)) = _
    rw [← Measure.map_map T.measurable measurable_subtype_coe, hτmap]
    have htr := T.measurableEmbedding.restrict_map (volume : Measure ℝ) (T '' I)
    rw [T.injective.preimage_image] at htr
    have hTmap : (volume : Measure ℝ).map T = volume :=
      (measurePreserving_add_left (volume : Measure ℝ) c).map_eq
    rw [← htr, hTmap]
  have hβrange : β.restrict (range e) = β := by
    rw [he.restrict_map, preimage_range, Measure.restrict_univ]
  have hqrange : range q = range e ×ˢ (T '' I) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨⟨x.val.2, x.property.2⟩, rfl⟩, ⟨x.val.1, x.property.1, rfl⟩⟩
    · rintro ⟨⟨w, hw⟩, t, ht, htz⟩
      exact ⟨⟨(t, w.val), ht, w.property⟩, Prod.ext hw htz⟩
  have hmap : μpar.map q = (β.prod volume).restrict (range q) := by
    rw [← hpar, Measure.map_map hq.measurable r.symm.measurable]
    change ((τ.prod k).map ((Prod.map e j) ∘ Prod.swap)) = _
    rw [← Measure.map_map (he.measurable.prodMap hj.measurable) measurable_swap,
      Measure.prod_swap, ← Measure.map_prod_map k τ he.measurable hj.measurable,
      hjmap, hqrange, ← Measure.prod_restrict, hβrange]
  exact ⟨hq, map_withDensity_extend_of_map_eq_restrict hq μpar (β.prod volume) hmap d hd⟩

private theorem window_pushforward_product_of_domain
    {W Z : Type*} [MeasurableSpace W] [MeasurableSpace Z]
    (κ : Measure W) [SFinite κ] {L : Set W} (hL : MeasurableSet L)
    {I : Set ℝ} (hI : MeasurableSet I)
    [SFinite (κ.comap ((↑) : L → W))]
    {e : L → Z} (he : MeasurableEmbedding e) (c : ℝ)
    {D : Set (ℝ × W)} (hDprod : D = I ×ˢ L) (q : D → Z × ℝ)
    (hq : ∀ z, q z =
      (e ⟨z.val.2, ((Set.ext_iff.mp hDprod z.val).mp z.property).2⟩, c + z.val.1))
    (d : D → ℝ≥0∞) (hd : Measurable d) :
    let μpar := ((volume : Measure ℝ).prod κ).comap ((↑) : D → ℝ × W)
    let k := κ.comap ((↑) : L → W)
    let β := k.map e
    MeasurableEmbedding q ∧
      (μpar.withDensity d).map q = (β.prod volume).withDensity (Function.extend q d 0) := by
  subst D
  have hqfun : q = fun z : (I ×ˢ L) ↦
      (e ⟨z.val.2, z.property.2⟩, c + z.val.1) := funext hq
  subst q
  exact window_pushforward_product κ hL hI he c d hd


namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- An exact measurable pullback density on the actual window pushes to the
original label-clock space, with the actual finite seed reference and clock. -/
theorem map_labelClock_restrict_eq_withDensity_of_comap
    (P : CalibratedSeedWindow F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowPushforwardLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instWindowPushforwardOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure]
    (κ : Measure P.seed.covector.ker) [κ.IsAddHaarMeasure]
    (hprod : tubeParameterMeasure P.seed.normalization m =
      (volume : Measure ℝ).prod κ)
    (η : Measure M) (w : P.domain → ℝ≥0∞) (hw : Measurable w)
    (hpullback : η.comap (fun z : P.domain ↦ P.toManifold z) =
      ((tubeParameterMeasure P.seed.normalization m).comap
        ((↑) : P.domain → ℝ × P.seed.covector.ker)).withDensity w)
    {C : Set M} (hC : MeasurableSet C)
    (hCP : C ⊆ P.toManifold '' P.domain) :
    let L := P.labels ∩ ball P.center.2 (P.seed.radius P.center)
    let k := κ.comap ((↑) : L → P.seed.covector.ker)
    let e : L → Z := fun w ↦ a (P.seed.curve w 0)
    let β := k.map e
    let q : P.domain → Z × ℝ := fun z ↦
      (a (P.toManifold z), u (P.toManifold z))
    let d : P.domain → ℝ≥0∞ := fun z ↦
      w z * (C.indicator (fun _ : M ↦ (1 : ℝ≥0∞))) (P.toManifold z)
    let G : Z × ℝ → ℝ≥0∞ := Function.extend q d (fun _ ↦ 0)
    IsFiniteMeasure β ∧ Measurable G ∧
      (η.restrict C).map (fun x ↦ (a x, u x)) =
        (β.prod (volume : Measure ℝ)).withDensity G
 := by
  classical
  let _instWindowPushforwardMetric : MetricSpace M := F.metricSpace
  let L := P.labels ∩ ball P.center.2 (P.seed.radius P.center)
  let k := κ.comap ((↑) : L → P.seed.covector.ker)
  let e : L → Z := fun w ↦ a (P.seed.curve w 0)
  let β := k.map e
  let X : P.domain → M := fun z ↦ P.toManifold z
  let q : P.domain → Z × ℝ := fun z ↦ (a (X z), u (X z))
  let d : P.domain → ℝ≥0∞ := fun z ↦
    w z * (C.indicator (fun _ : M ↦ (1 : ℝ≥0∞))) (X z)
  let G : Z × ℝ → ℝ≥0∞ := Function.extend q d (fun _ ↦ 0)
  let μpar := (tubeParameterMeasure P.seed.normalization m).comap
    ((↑) : P.domain → ℝ × P.seed.covector.ker)
  change IsFiniteMeasure β ∧ Measurable G ∧
    (η.restrict C).map (fun x ↦ (a x, u x)) = (β.prod volume).withDensity G
  have hL : MeasurableSet L := (P.measurableSet_labels hu).inter isOpen_ball.measurableSet
  have hk : IsFiniteMeasure k := by
    constructor
    change κ.comap ((↑) : L → P.seed.covector.ker) univ < (∞ : ℝ≥0∞)
    rw [comap_subtype_coe_apply hL, Subtype.coe_image_univ]
    exact lt_of_le_of_lt (measure_mono inter_subset_right) measure_ball_lt_top
  have hβ : IsFiniteMeasure β := inferInstance
  have : StandardBorelSpace L := hL.standardBorel
  have he : MeasurableEmbedding e := by
    let j : L → P.labels := fun z ↦ ⟨z.val, z.property.1⟩
    have hj : MeasurableEmbedding j := by
      apply Measurable.measurableEmbedding
      · exact measurable_subtype_coe.subtype_mk
      · intro x y h
        exact Subtype.ext (congrArg (fun v : P.labels ↦ v.val) h)
    exact (P.measurableEmbedding_seedLabel hF hcomplete hu ha hinj).comp hj
  have hD := P.measurableSet_domain hu
  have hX : MeasurableEmbedding X := P.measurableEmbedding_toManifold hF hcomplete hu
  let I := Ioo (P.left : ℝ) P.right ∩ ball P.center.1 (P.seed.radius P.center)
  have hI : MeasurableSet I := isOpen_Ioo.measurableSet.inter isOpen_ball.measurableSet
  have hclock (z : P.domain) : u (X z) = (P.seed.level : ℝ) + z.val.1 := by
    exact (hF.calibrated_window_of_complete_unit_endpoints hu
      (P.seed.complete z.val.2 z.property.2.2.1)
      (P.seed.unit z.val.2 z.property.2.2.1)
      z.property.2.2.2.1 z.property.2.2.2.2).1 z.val.1
        ⟨z.property.2.1.1.le, z.property.2.1.2.le⟩
  have hlabel (z : P.domain) : a (X z) = a (P.seed.curve z.val.2 0) :=
    P.label_toManifold_eq_initial hF hcomplete hu horder z.property
  have hDprod : P.domain = I ×ˢ L := P.domain_eq_prod
  have hd : Measurable d := hw.mul
    ((measurable_const.indicator hC).comp hX.measurable)
  have hqform (z : P.domain) : q z =
      (e ⟨z.val.2, ((Set.ext_iff.mp hDprod z.val).mp z.property).2⟩,
        (P.seed.level : ℝ) + z.val.1) := Prod.ext (hlabel z) (hclock z)
  obtain ⟨hq, hgeometry⟩ := window_pushforward_product_of_domain κ hL hI he
    (P.seed.level : ℝ) hDprod q hqform d hd
  have hG : Measurable G := hq.measurable_extend hd measurable_const
  refine ⟨hβ, hG, ?_⟩
  have hphysical : (μpar.withDensity d).map q =
      (η.restrict C).map (fun x ↦ (a x, u x)) := by
    have hdC : d = (X ⁻¹' C).indicator w := by
      funext z
      by_cases hz : X z ∈ C <;> simp [d, hz]
    have hpull : μpar.withDensity d = (η.comap X).restrict (X ⁻¹' C) := by
      rw [hdC, withDensity_indicator (hC.preimage hX.measurable),
        ← restrict_withDensity (hC.preimage hX.measurable)]
      rw [hpullback]
    have hmapX : (μpar.withDensity d).map X = η.restrict C := by
      rw [hpull, ← hX.restrict_map,
        P.map_comap_toManifold_eq_restrict hF hcomplete hu η,
        Measure.restrict_restrict_of_subset hCP]
    have hT : Measurable (fun x ↦ (a x, u x)) := ha.prodMk hu.continuous.measurable
    rw [show q = (fun x ↦ (a x, u x)) ∘ X from rfl, ← Measure.map_map hT hX.measurable,
      hmapX]
  rw [← hphysical]
  have hzero : (0 : Z × ℝ → ℝ≥0∞) = (fun _ ↦ 0) := by ext; rfl
  rw [hzero] at hgeometry
  simpa only [μpar, hprod, β, k, G] using hgeometry


/-- Every Borel physical subpiece of an actual calibrated window pushes to the
original label-clock space with its zero-extended, normalized geometric density.
The finite seed reference depends only on the window, old labels and Haar choice. -/
theorem map_labelClock_restrict_eq_withDensity
    (P : CalibratedSeedWindow F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instWindowPushforwardLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective
      (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instWindowPushforwardOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (m : Measure E) [m.IsAddHaarMeasure]
    (κ : Measure P.seed.covector.ker) [κ.IsAddHaarMeasure]
    (hprod : tubeParameterMeasure P.seed.normalization m =
      (volume : Measure ℝ).prod κ)
    (η : Measure M) [SFinite η]
    (hηchart :
      (η.restrict (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).source).map
        (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)) ≪ m)
    {C : Set M} (hC : MeasurableSet C)
    (hCP : C ⊆ P.toManifold '' P.domain) :
    let L := P.labels ∩ ball P.center.2 (P.seed.radius P.center)
    let k := κ.comap ((↑) : L → P.seed.covector.ker)
    let e : L → Z := fun w ↦ a (P.seed.curve w 0)
    let β := k.map e
    let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
    let ρ := ((η.restrict χ.source).map χ).rnDeriv m
    let q : P.domain → Z × ℝ := fun z ↦
      (a (P.toManifold z), u (P.toManifold z))
    let d : P.domain → ℝ≥0∞ := fun z ↦
      (ENNReal.ofReal (parameterizedJacobian P.readout P.seed.normalization z) *
        ρ (P.readout z)) * (C.indicator (fun _ : M ↦ (1 : ℝ≥0∞))) (P.toManifold z)
    let G : Z × ℝ → ℝ≥0∞ := Function.extend q d (fun _ ↦ 0)
    IsFiniteMeasure β ∧ Measurable G ∧
      (η.restrict C).map (fun x ↦ (a x, u x)) =
        (β.prod (volume : Measure ℝ)).withDensity G
 := by
  let _instWindowPushforwardMetric : MetricSpace M := F.metricSpace
  let χ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
  let ρ := ((η.restrict χ.source).map χ).rnDeriv m
  let w : P.domain → ℝ≥0∞ := fun z ↦ ENNReal.ofReal
    (parameterizedJacobian P.readout P.seed.normalization z) * ρ (P.readout z)
  have hr : Measurable (fun z : P.domain ↦ P.readout z) :=
    (continuousOn_iff_continuous_domRestrict.mp
      (P.lipschitzOn_readout.continuousOn.mono inter_subset_left)).measurable
  have hw : Measurable w :=
    (((measurable_parameterizedJacobian P.readout P.seed.normalization).comp
      measurable_subtype_coe).ennreal_ofReal).mul ((Measure.measurable_rnDeriv _ _).comp hr)
  exact P.map_labelClock_restrict_eq_withDensity_of_comap hF hcomplete hu ha hinj horder
    m κ hprod η w hw
    (P.comap_toManifold_eq_withDensity_chartDensity hF hcomplete hu m η hηchart) hC hCP

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

end
end
