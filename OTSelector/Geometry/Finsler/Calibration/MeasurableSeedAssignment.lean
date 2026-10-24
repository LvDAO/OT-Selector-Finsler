import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.Calibration.RootLabelValue
import OTSelector.Geometry.Finsler.Calibration.SeedPhysicalMap
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationFiniteSeedAssignment.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationFiniteSeedAssignment`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.MeasurableSeedAssignment

* **Conditions:** A countable family of actual seeds covers regular paired endpoints, and the given labels and clocks separate regular points and encode calibration.
* **Objects:** Borel eligibility sets for seed endpoints/pairs and a measurable eligible seed index preserving the supplied original paired law.
* **Proof detail:** Recover the initial seed label by calibrated clock equality, identify the endpoint image using a Borel inverse, and choose the first eligible index from a countable enumeration.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.

Source relation (derived): A generic measurable cover assignment plus an actual geometric eligibility proof; no new population or measurable witness choice over uncountable seeds is introduced.
-/

/-!
# Measurable original seed assignment for complete physical endpoint pairs

Regular calibrated endpoints recover the original seed root even at the ends
of a calibrated segment. Their Borel eligibility sets admit a measurable first
index for any produced finite family, preserving the complete original paired law.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A countable measurable cover has a measurable first eligible index, with an
explicit unmatched value outside the cover. -/
theorem exists_measurable_cover_index
    {X J : Type*} [MeasurableSpace X] [Countable J] [MeasurableSpace (Option J)]
    (C : J → Set X) (hC : ∀ j, MeasurableSet (C j)) :
    ∃ f : X → Option J, Measurable f ∧
      ∀ x, (∃ j, x ∈ C j) → ∃ j, f x = some j ∧ x ∈ C j := by
  classical
  let _inst : Encodable J := Encodable.ofCountable J
  let p (x : X) (n : ℕ) : Prop :=
    (n = 0 ∧ ¬ ∃ j, x ∈ C j) ∨ ∃ j, n = Encodable.encode j + 1 ∧ x ∈ C j
  have hex (x : X) : ∃ n, p x n := by
    by_cases h : ∃ j, x ∈ C j
    · obtain ⟨j, hj⟩ := h
      exact ⟨Encodable.encode j + 1, Or.inr ⟨j, rfl, hj⟩⟩
    · exact ⟨0, Or.inl ⟨rfl, h⟩⟩
  have hm (n : ℕ) : MeasurableSet {x | p x n} := by
    dsimp only [p]
    apply MeasurableSet.union
    · by_cases hn : n = 0
      · simp only [hn, true_and]
        convert (MeasurableSet.iUnion hC).compl using 1
        ext x
        simp
        rfl
      · simp only [hn, false_and]
        change MeasurableSet (∅ : Set X)
        exact MeasurableSet.empty
    · have hj (j : J) : MeasurableSet {x | n = Encodable.encode j + 1 ∧ x ∈ C j} := by
        by_cases hn : n = Encodable.encode j + 1
        · convert hC j using 1
          ext x
          simp only [Set.mem_ofPred_eq, hn, true_and]
        · simp only [hn, false_and, Set.ofPred_false]
          exact MeasurableSet.empty
      convert MeasurableSet.iUnion hj using 1
      ext x
      simp
      rfl
  let decode (n : ℕ) : Option J := if n = 0 then none else Encodable.decode (α := J) (n - 1)
  refine ⟨fun x ↦ decode (Nat.find (hex x)),
    (measurable_of_countable decode).comp (measurable_find hex hm), ?_⟩
  intro x hx
  rcases Nat.find_spec (hex x) with h | ⟨j, hj, hjC⟩
  · exact (h.2 hx).elim
  · refine ⟨j, ?_, hjC⟩
    simp only [hj, decode, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
      Nat.add_sub_cancel, Encodable.encodek]

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- The original label remains the seed label at every regular calibrated endpoint. -/
theorem seed_label_eq_initial_of_clock_regular
    (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z}
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {w : S.covector.ker} (hw : w ∈ S.labels) {t : ℝ}
    (hclock : u (S.curve w t) = S.level + t)
    (hreg : S.curve w t ∈ F.potentialRegularDomain u) :
    a (S.curve w t) = a (S.curve w 0) := by
  let _inst : MetricSpace M := F.metricSpace
  have hzero : u (S.curve w 0) = S.level + 0 := by
    simpa only [add_zero] using S.potential_initial hw
  have hr0 := hF.mem_potentialRegularDomain_of_mem_calibratedInterior hcomplete hu
    (S.mapsTo_initial_calibratedInterior hF hu hw)
  rcases le_total 0 t with ht | ht
  · have hc := hF.calibrated_window_of_complete_unit_endpoints hu
      (S.complete w hw) (S.unit w hw) hzero hclock
    have hd : dist (S.curve w 0) (S.curve w t) = t := by
      simpa only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg ht] using
        hc.2.1.dist_eq ⟨0, left_mem_Icc.mpr ht⟩ ⟨t, right_mem_Icc.mpr ht⟩
    apply ((horder _ hr0 _ hreg).mpr ?_).1.symm
    rw [hclock, hzero, hd]
    ring
  · have hc := hF.calibrated_window_of_complete_unit_endpoints hu
      (S.complete w hw) (S.unit w hw) hclock hzero
    have hd : dist (S.curve w t) (S.curve w 0) = -t := by
      simpa only [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonpos ht] using
        hc.2.1.dist_eq ⟨t, left_mem_Icc.mpr ht⟩ ⟨0, right_mem_Icc.mpr ht⟩
    apply ((horder _ hreg _ hr0).mpr ?_).1
    rw [hclock, hzero, hd]
    ring

variable [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]

/-- Endpoints represented by one actual seed through the unchanged population root. -/
def populationSeedEndpointSet (S : F.CalibratedLevelSeedPatch u) (a : M → Z) : Set M :=
  {x | x ∈ F.potentialRegularDomain u ∧
    populationSeedRootLabelValue S a (a x) ∈ S.labels ∧
    populationSeedPhysicalMap S (populationSeedRootLabelValue S a (a x), u x) = x}

/-- The full endpoint set is Borel, including regular endpoints of calibration intervals. -/
theorem measurableSet_populationSeedEndpointSet
    (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    MeasurableSet (populationSeedEndpointSet S a) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  have hl := (measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj).comp ha
  exact (hF.measurableSet_potentialRegularDomain hcomplete u).inter
    ((hl S.labels_measurable).inter (measurableSet_eq_fun
      ((measurable_populationSeedPhysicalMap S).comp
        (hl.prodMk hu.continuous.measurable)) measurable_id))

/-- Every actual regular endpoint represented by the seed belongs to its Borel endpoint set. -/
theorem mem_populationSeedEndpointSet_of_curve
    (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {w : S.covector.ker} (hw : w ∈ S.labels) {x : M}
    (hx : x ∈ F.potentialRegularDomain u)
    (hcurve : S.curve w (u x - S.level) = x) :
    x ∈ populationSeedEndpointSet S a := by
  have hl : a x = a (S.curve w 0) := by
    rw [← hcurve]
    apply seed_label_eq_initial_of_clock_regular S hF hcomplete hu horder hw
    · rw [hcurve]
      ring
    · rwa [hcurve]
  have hw' : populationSeedRootLabelValue S a (a x) = w := by
    rw [hl]
    exact populationSeedRootLabelValue_at_label S hF hcomplete hu ha hinj ⟨w, hw⟩
  refine ⟨hx, hw' ▸ hw, ?_⟩
  rw [hw']
  exact (populationSeedPhysicalMap_at_label S ⟨w, hw⟩ (u x)).trans hcurve

variable [MeasurableEq Z]

/-- Pairs recovered by one seed through their common original root. -/
def populationSeedPairSet (S : F.CalibratedLevelSeedPatch u) (a : M → Z) : Set (M × M) :=
  (populationSeedEndpointSet S a ×ˢ populationSeedEndpointSet S a) ∩
    {p | a p.1 = a p.2}

/-- Original seed pair eligibility is measurable. -/
theorem measurableSet_populationSeedPairSet
    (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val))) :
    MeasurableSet (populationSeedPairSet S a) := by
  exact ((measurableSet_populationSeedEndpointSet S hF hcomplete hu ha hinj).prod
    (measurableSet_populationSeedEndpointSet S hF hcomplete hu ha hinj)).inter
      (measurableSet_eq_fun (ha.comp measurable_fst) (ha.comp measurable_snd))

omit [MeasurableEq Z] in
/-- Every original regular pair covered by the same actual seed has that seed's
measurable eligibility, including both physical endpoints. -/
theorem mem_populationSeedPairSet_of_curve
    (S : F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    {w : S.covector.ker} (hw : w ∈ S.labels) {x y : M}
    (hx : x ∈ F.potentialRegularDomain u) (hy : y ∈ F.potentialRegularDomain u)
    (hcx : S.curve w (u x - S.level) = x)
    (hcy : S.curve w (u y - S.level) = y) :
    (x, y) ∈ populationSeedPairSet S a := by
  refine ⟨⟨mem_populationSeedEndpointSet_of_curve S hF hcomplete hu ha hinj horder hw hx hcx,
    mem_populationSeedEndpointSet_of_curve S hF hcomplete hu ha hinj horder hw hy hcy⟩, ?_⟩
  have he (z : M) (hz : z ∈ F.potentialRegularDomain u)
      (hc : S.curve w (u z - S.level) = z) : a z = a (S.curve w 0) := by
    rw [← hc]
    apply seed_label_eq_initial_of_clock_regular S hF hcomplete hu horder hw
    · rw [hc]
      ring
    · rwa [hc]
  exact (he x hx hcx).trans (he y hy hcy).symm

/-- A produced finite family covering the original paired law admits a measurable
actual chart assignment without discarding any original pair mass. -/
theorem exists_measurable_population_seed_assignment
    {J : Type*} [Countable J] [MeasurableSpace (Option J)]
    (P : J → F.CalibratedLevelSeedPatch u) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (π : Measure (M × M))
    (hregular : ∀ᵐ p ∂π,
      p.1 ∈ F.potentialRegularDomain u ∧ p.2 ∈ F.potentialRegularDomain u)
    (hcover : ∀ᵐ p ∂π, ∃ j, ∃ w ∈ (P j).labels,
      (P j).curve w (u p.1 - (P j).level) = p.1 ∧
        (P j).curve w (u p.2 - (P j).level) = p.2) :
    ∃ chart : M × M → Option J, Measurable chart ∧
      ∀ᵐ p ∂π, ∃ j, chart p = some j ∧ p ∈ populationSeedPairSet (P j) a := by
  obtain ⟨chart, hm, hchoice⟩ := exists_measurable_cover_index
    (fun j ↦ populationSeedPairSet (P j) a)
    (fun j ↦ measurableSet_populationSeedPairSet (P j) hF hcomplete hu ha hinj)
  refine ⟨chart, hm, ?_⟩
  filter_upwards [hregular, hcover] with p hp hpc
  apply hchoice p
  obtain ⟨j, w, hw, hx, hy⟩ := hpc
  exact ⟨j, mem_populationSeedPairSet_of_curve (P j) hF hcomplete hu ha hinj horder
    hw hp.1 hp.2 hx hy⟩

end OTSelector.Reconstruction

end
end
