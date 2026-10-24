import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.HopfRinow
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialCurveLipschitz
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Finsler.PotentialPairShift
import OTSelector.Geometry.Finsler.PotentialRegularMass
import OTSelector.Topology.ContinuousCurveCode
import OTSelector.Transport.Coupling.CostEquivalence
import OTSelector.Transport.Coupling.LabelDisintegration
import OTSelector.Transport.Coupling.OptimalPlanExistence
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerGeometricDisintegration.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerGeometricDisintegration`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.GeometricDisintegration

* **Conditions:** Smooth strong convexity and metric completeness, two chartwise absolutely continuous probabilities with disjoint compact carriers. The private helper instead starts from an explicit calibration characterization and a regular labeled domain.
* **Objects:** One actual optimal potential, measurable complete-geodesic labels injective together with the clock, a common quotient marginal and the exact conditional-kernel description of every distance-optimal plan.
* **Proof detail:** Construct regular calibrated curves and ordered labels, use optimal calibration to force equality of quotient marginals, then disintegrate and reconstruct same-label forward couplings.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=52): Section 5.3, Theorem 5.9(i)–(iv), pp. 52–53, equations (5.12)–(5.14); balance proof p. 56.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25): 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=20): 452E, p. 20: consistency and strong consistency; 452G(a)–(c), p. 21: probability kernels and concentration on fibers.
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): main.tex, proposition label prop:general-optimal-face, lines 422–483, equation eq:general-optimal-face.

Source relation (derived): The ray/needle package and standard-Borel disintegration support the construction. The explicit whole-face equivalence is local assembly; conditional absolute continuity is established separately.
-/

/-!
# The original Finsler optimal face over its constructed geometric labels

Disjoint compactly carried, chartwise absolutely continuous original probabilities determine
one actual optimal potential and a common full-marginal regular domain. The original complete
geodesics construct measurable labels whose combination with the potential is injective there.
Within this domain, equal labels and increasing potential are equivalent to true calibration.
An actual optimizer forces equality of the two label laws. Every original distance-optimal
coupling is then exactly a mixture of ordered couplings of the two actual conditional laws
within each geometric label, and every such mixture is optimal.
The same potential and labels are used throughout.
This does not assert absolute continuity of the conditional laws or a limiting selector.
-/

open Set MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Reconstruction

private theorem optimal_face_of_same_calibrated_labels
    {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z]
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (hface : ∀ π : Measure (M × M), Vlasov.IsCoupling π μ ν →
      (IsOptimalCoupling edist μ ν π ↔ ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2))
    {N : Set M} (hN : MeasurableSet N)
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
    {a : M → Z} (ha : Measurable a)
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hex : ∃ π : Measure (M × M), IsOptimalCoupling edist μ ν π) :
    μ.map a = ν.map a ∧ ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
      ∃ κ : Kernel Z (M × M), IsMarkovKernel κ ∧ κ ∘ₘ μ.map a = π ∧
        ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ z)
          (condDistrib id a μ z) (condDistrib id a ν z) ∧
          ∀ᵐ p ∂κ z, p.1 ∈ N ∧ p.2 ∈ N ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2 := by
  let R : Set (M × M) :=
    {p | p.1 ∈ N ∧ p.2 ∈ N ∧ u p.2 - u p.1 = dist p.1 p.2}
  have hR : MeasurableSet R := (measurable_fst hN).inter ((measurable_snd hN).inter
    (measurableSet_eq_fun
      ((hu.continuous.measurable.comp measurable_snd).sub
        (hu.continuous.measurable.comp measurable_fst))
      (continuous_fst.dist continuous_snd).measurable))
  have hiff (π : Measure (M × M)) : IsOptimalCoupling edist μ ν π ↔
      μ.map a = ν.map a ∧ ∃ κ : Kernel Z (M × M), IsMarkovKernel κ ∧
        κ ∘ₘ μ.map a = π ∧ ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ z)
          (condDistrib id a μ z) (condDistrib id a ν z) ∧ ∀ᵐ p ∂κ z, p ∈ R := by
    have hsupport : IsOptimalCoupling edist μ ν π ↔
        Vlasov.IsCoupling π μ ν ∧ ∀ᵐ p ∂π, p ∈ R := by
      constructor
      · intro hπ
        have hleft : ∀ᵐ p ∂π, p.1 ∈ N := ae_of_ae_map measurable_fst.aemeasurable
          (by rwa [hπ.1.1])
        have hright : ∀ᵐ p ∂π, p.2 ∈ N := ae_of_ae_map measurable_snd.aemeasurable
          (by rwa [hπ.1.2])
        refine ⟨hπ.1, ?_⟩
        filter_upwards [hleft, hright, (hface π hπ.1).mp hπ] with p hp hq hcal
        exact ⟨hp, hq, hcal⟩
      · rintro ⟨hπ, hsupp⟩
        exact (hface π hπ).mpr (hsupp.mono fun _ h ↦ h.2.2)
    exact hsupport.trans (isCoupling_supported_iff_conditional_couplings ha ha hR
      (fun p hp ↦ ((horder p.1 hp.1 p.2 hp.2.1).mpr hp.2.2).1))
  obtain ⟨π₀, hπ₀⟩ := hex
  have hbalance := ((hiff π₀).mp hπ₀).1
  have hsupp (p : M × M) : (p ∈ R) ↔
      p.1 ∈ N ∧ p.2 ∈ N ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2 := by
    constructor
    · rintro ⟨hp, hq, hcal⟩
      exact ⟨hp, hq, (horder p.1 hp p.2 hq).mpr hcal⟩
    · rintro ⟨hp, hq, heq, hle⟩
      exact ⟨hp, hq, (horder p.1 hp p.2 hq).mp ⟨heq, hle⟩⟩
  refine ⟨hbalance, fun π ↦ ?_⟩
  simpa only [and_iff_right hbalance, hsupp] using hiff π


variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : Geometry.ContinuousFinslerNorm E M}

omit [MeasurableSpace E] [BorelSpace E] in
private theorem exists_measurable_ordered_labels_of_actual_family (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instGeometricLabelsHelperLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {N : Set M} (hN : MeasurableSet N)
    (hd : ∀ x ∈ N, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (G : N → ℝ → M) (hEL : ∀ x, F.IsEulerLagrangeOn (G x) univ)
    (hG : Measurable (Function.uncurry G))
    (hstate : ∀ x, G x 0 = x.val ∧ ∃ v : TangentSpace 𝓘(ℝ, E) x.val, v ≠ 0 ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (G x) ⟨0, (1 : ℝ)⟩ = ⟨x.val, v⟩ ∧
      fderiv ℝ (F.fiberEnergy x.val) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x.val) :
    let _instGeometricLabelsHelperMetric : MetricSpace M := F.metricSpace
    ∃ a : M → (ℚ → M), Measurable a ∧
      Function.Injective (fun x : N ↦ (a x.val, u x.val)) ∧
      ∀ x ∈ N, ∀ y ∈ N, (a x = a y ∧ u x ≤ u y) ↔
        u y - u x = dist x y := by
  classical
  let _instGeometricLabelsHelperProofMetric : MetricSpace M := F.metricSpace
  let code : N → (ℚ → M) := fun x ↦ rationalCurveCode (fun t ↦ G x (t - u x.val))
  have hmcode : Measurable code := measurable_rationalCurveCode_clock hG
    (hu.continuous.measurable.comp measurable_subtype_coe)
  let a : M → (ℚ → M) := fun x ↦ if hx : x ∈ N then code ⟨x, hx⟩ else fun _ ↦ x
  have hma : Measurable a := by
    have hmout : Measurable (fun x : {x : M // x ∉ N} ↦ fun _ : ℚ ↦ x.val) :=
      measurable_pi_lambda _ (fun _ ↦ measurable_subtype_coe)
    exact hmcode.dite hmout hN
  have ha (x : M) (hx : x ∈ N) : a x = code ⟨x, hx⟩ := by
    simp only [a, dite_eq_left hx]
  have hcont (x : N) : Continuous (G x) :=
    continuousOn_univ.mp (hF.contMDiffOn_of_isEulerLagrangeOn (hEL x)).continuousOn
  refine ⟨a, hma, ?_, ?_⟩
  · have hi := injective_rationalCurveCode_clock G hcont Subtype.val Subtype.val_injective
      (fun x ↦ (hstate x).1) (fun x ↦ u x.val)
    intro x y hxy
    apply hi
    simpa only [ha x.val x.property, ha y.val y.property, code] using hxy
  · intro x hx y hy
    constructor
    · rintro ⟨heq, hle⟩
      obtain ⟨v, hv, hvi, hvp⟩ := (hstate ⟨x, hx⟩).2
      have hlip := hF.lipschitzWith_of_complete_potential_covector hu (hd x hx)
        (hEL ⟨x, hx⟩) hv hvi hvp
      rw [ha x hx, ha y hy] at heq
      have hcurve := eq_of_rationalCurveCode_eq
        ((hcont ⟨x, hx⟩).comp (continuous_id.sub continuous_const))
        ((hcont ⟨y, hy⟩).comp (continuous_id.sub continuous_const)) heq
      have hpoint := congrFun hcurve (u y)
      change G ⟨x, hx⟩ (u y - u x) = G ⟨y, hy⟩ (u y - u y) at hpoint
      simp only [sub_self, (hstate ⟨y, hy⟩).1] at hpoint
      have hupper := hlip.dist_le_mul (u y - u x) 0
      have hlower := hu.dist_le_mul y x
      simp only [NNReal.coe_one, one_mul, Real.dist_eq, sub_zero,
        abs_of_nonneg (sub_nonneg.mpr hle), hpoint, (hstate ⟨x, hx⟩).1] at hupper hlower
      exact le_antisymm (by simpa only [dist_comm x y] using hlower)
        (by simpa only [dist_comm x y] using hupper)
    · intro hsat
      obtain ⟨v, hv, hvi, hvp⟩ := (hstate ⟨x, hx⟩).2
      obtain ⟨w, hw, hwi, hwp⟩ := (hstate ⟨y, hy⟩).2
      have hshift := hF.eq_timeShift_of_calibrated_pair hcomplete hu hsat (hd x hx) (hd y hy)
        (hEL ⟨x, hx⟩) (hEL ⟨y, hy⟩) hv hw hvi hwi hvp hwp
      refine ⟨?_, sub_nonneg.mp (hsat.symm ▸ dist_nonneg)⟩
      rw [ha x hx, ha y hy]
      exact rationalCurveCode_clock_eq_of_timeShift hshift


/-- The original geometric data construct the potential, injective label-clock coordinates,
common label law, and exact conditional-coupling description of the whole optimal face. -/
theorem exists_finsler_geometric_disintegration (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    let _instGeometricDisintegrationStatementMetric : MetricSpace M := F.metricSpace
    let _instGeometricDisintegrationStatementProper : ProperSpace M :=
      F.properSpace_of_complete hcomplete
    let _instGeometricDisintegrationStatementBorel : StandardBorelSpace M := inferInstance
    let _instGeometricDisintegrationStatementNonempty : Nonempty M :=
      nonempty_of_isProbabilityMeasure μ
    ∃ (u : M → ℝ) (a : M → (ℚ → M)), LipschitzWith 1 u ∧
      MeasurableSet (F.potentialRegularDomain u) ∧
      (∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u) ∧
      (∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u) ∧ Measurable a ∧
      Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)) ∧
      (∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) ∧
      μ.map a = ν.map a ∧
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ κ : Kernel (ℚ → M) (M × M), IsMarkovKernel κ ∧ κ ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (κ z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂κ z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2 := by
  let _instGeometricDisintegrationMetric : MetricSpace M := F.metricSpace
  let _instGeometricDisintegrationProper : ProperSpace M :=
    F.properSpace_of_complete hcomplete
  let _instGeometricDisintegrationNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  let _instGeometricDisintegrationStandardBorel : StandardBorelSpace M := inferInstance
  obtain ⟨u, hu, hμN, hνN, hface⟩ :=
    hF.exists_optimal_calibration_with_full_regular_domain hcomplete m μ ν
      hμchart hνchart hA hB hAB hμ hν
  have hN := hF.measurableSet_potentialRegularDomain hcomplete u
  obtain ⟨G, hEL, hG, hstate⟩ := hF.exists_measurable_potential_global_family hcomplete u
  obtain ⟨a, ha, hinj, horder⟩ := exists_measurable_ordered_labels_of_actual_family
    hF hcomplete hu hN (fun x hx ↦ hx.1) G hEL hG hstate
  have hex : ∃ π : Measure (M × M), IsOptimalCoupling edist μ ν π :=
    exists_isOptimalCoupling_edist_of_compact_carrier μ ν (hA.union hB)
      (hμ.mono fun _ hx ↦ Or.inl hx) (hν.mono fun _ hy ↦ Or.inr hy)
  obtain ⟨hbalance, hdisint⟩ :=
    optimal_face_of_same_calibrated_labels μ ν hu hface hN hμN hνN ha horder hex
  exact ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hdisint⟩

end OTSelector.Reconstruction

end
end
