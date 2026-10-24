import OTSelector.Reconstruction.FinslerOriginalEndgameActualWired
import OTSelector.Reconstruction.FinslerAssemblyPotentialInvariance

/-!
# Paper-facing selector statement and across-potential independence

This module closes the two statement-fidelity gaps recorded in
`research/AUDIT-THEOREM-STATEMENT.md`:

1. **Independence of the limit from the potential** (main.tex:107-109).  The paper states
   that the physical limit depends only on `(F, mu, nu)`, independently of optimal
   potentials, coordinates, labels and finite-sample tie-breaking.
   `finsler_assembly_limit_independent_of_potential` proves this at the four-input assembly
   level.  The paper-facing selector conclusion is formalised here as the predicate
   `IsPaperSelectorPlan`, whose arguments are only the marginals `mu, nu`, the sampling data
   `P, X, Y` and the plan itself.  It mentions no potential, readout derivative, pressure
   field, coordinate system, label or tie-breaking rule.  Consequently any two plans
   satisfying the paper's displayed conclusion are equal
   (`paperSelectorPlan_independent_of_potential`), so every admissible potential produces
   the same limit.

2. **Factored paper-facing theorem.**  The wired endgame theorem
   `existsUnique_general_finsler_selector_at_derivedPotential` bundles the paper's displayed
   conclusion with three internal reconstruction clauses.  `existsUnique_paperSelectorPlan`
   states *only* the paper's conclusion (eq. (1): the whole empirical optimal face
   converges in probability to a deterministic population distance-optimal plan); the
   internal clauses are collected in the separate lemma `internalSelectorClauses`.

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability
  TopologicalSpace
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff ENNReal NNReal CompactlySupported BoundedContinuousFunction
  BigOperators

noncomputable section

namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **The paper-facing selector conclusion.**  A probability plan `pi` on `M x M` is a
paper selector plan for marginals `mu, nu` and samples `P, X, Y` when

* `pi` is a population distance-optimal coupling of `mu` and `nu` for the original length
  cost (represented by `edist`; on `F.metricSpace` this is the path-length distance `d_F`);
* the whole empirical optimal face converges to `pi` in probability in every weak
  neighbourhood (topological form of eq. (1));
* the displayed metric form of eq. (1) holds: for every metric-type `d` with open
  `eps`-balls, the probability that some empirical optimum is at `d`-distance at least
  `eps` from `pi` tends to zero, i.e. `sup over Opt_n of d(., pi)` tends to zero in
  probability.

No potential, pressure field, readout derivative, coordinate, label or tie-breaking rule
occurs among the arguments; this is the formal content of the paper's independence claim. -/
def IsPaperSelectorPlan {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [ProperSpace M]
    (mu nu : ProbabilityMeasure M) {Omega : ℕ → Type*} [∀ n, MeasurableSpace (Omega n)]
    (P : ∀ n, Measure (Omega n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Omega n → M) (pi : ProbabilityMeasure (M × M)) : Prop :=
  IsOptimalCoupling edist (mu : Measure M) (nu : Measure M) (pi : Measure (M × M)) ∧
    (∀ U ∈ nhds pi, Tendsto (fun n => (P n).real
      {s | ∃ gamma ∈ Pressure.empiricalOptimalFace
        (fun i => X n i s) (fun i => Y n i s), gamma ∉ U}) atTop (nhds 0)) ∧
    (∀ d : ProbabilityMeasure (M × M) → ProbabilityMeasure (M × M) → ℝ,
      d pi pi = 0 →
      (∀ eps : ℝ, 0 < eps → IsOpen {gamma : ProbabilityMeasure (M × M) |
        d gamma pi < eps}) →
      ∀ eps : ℝ, 0 < eps → Tendsto (fun n => (P n).real
        {s | ∃ gamma ∈ Pressure.empiricalOptimalFace
          (fun i => X n i s) (fun i => Y n i s), eps ≤ d gamma pi}) atTop (nhds 0))

/-- **Across-potential independence (main.tex:107-109).**

Any two plans satisfying the paper-facing selector conclusion for the same manifold,
marginals and samples coincide.  The hypotheses `h_1, h_2` are exactly the plans delivered by
the selector theorem at two admissible potentials `u_1, u_2`: the endgame theorem
`existsUnique_general_finsler_selector_at_derivedPotential` and the paper-data theorem
`existsUnique_general_finsler_selector_at_potential_paperData` both entail this predicate for their
output plan.  Since `IsPaperSelectorPlan` mentions no potential or readout data, the plan is
independent of the potential choice.  This is the paper-statement-level counterpart of
`finsler_assembly_limit_independent_of_potential`. -/
theorem paperSelectorPlan_independent_of_potential
    {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M] [ProperSpace M]
    {Omega : ℕ → Type*} [∀ n, MeasurableSpace (Omega n)]
    (P : ∀ n, Measure (Omega n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Omega n → M)
    {mu nu : ProbabilityMeasure M} {pi_1 pi_2 : ProbabilityMeasure (M × M)}
    (h_1 : IsPaperSelectorPlan mu nu P X Y pi_1)
    (h_2 : IsPaperSelectorPlan mu nu P X Y pi_2) :
    pi_1 = pi_2 :=
  eq_of_tendsto_empiricalOptimalFace P X Y h_1.2.1 h_2.2.1

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}


/-- **Paper-facing selector theorem (eq. (1) only).**

For the paper population and sampling data plus the currently named analytic inputs, there
exists a unique probability plan on M x M satisfying the paper displayed conclusion:
a population distance-optimal coupling whose whole empirical optimal face converges to it in
probability, both in the weak-neighbourhood form and in the metric sup form of eq. (1).
This is exactly the conclusion of main.tex thm:general-finsler-selector with the three
internal reconstruction clauses removed; they are factored out in internalSelectorClauses.
No existential over a potential, derivative, pressure field or final-input record occurs. -/
theorem existsUnique_paperSelectorPlan
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i))
    (hY : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)), (P n).map (X n i) =
      ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)), (P n).map (Y n j) =
      ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (seedDatum : PaperGeometricSeedDatum F
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁))
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    {Seed : ℕ → F.CalibratedSeedWindow
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)} {a : M → Z}
    {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}
    {g : FinalProbeSpace A B → ℝ → Z → ℝ} {q : ℝ}
    (frozenCost : (f : FinalProbeSpace A B) → ℝ → ∀ n, Ω n → ℝ)
    (hfrozen_int : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (P n))
    (hfrozen_dom : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤
        finslerSupportedPressure F (physicalSourceProbability ωM ρ₀)
          (physicalTargetProbability ωM ρ₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx => Or.inl hx) (hνB.mono fun _ hy => Or.inr hy)
          (fun i => X n i s) (fun i => Y n i s)
          (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
            hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    (hfrozen_mean_shifted : ∀ (f : FinalProbeSpace A B) (t ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        frozenPressureLower (K := A ∪ B) Seed a κ lambda g q f t +
            |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n)
    (qU mU : ℕ) (hmU : 0 < mU)
    (pc : FinalProbeSpace A B → ℝ → (Fin qU → Fin mU) → ℝ)
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopData F (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
        hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
        qU mU hmU ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin qU → Fin mU), (data f t hpert).p c t = pc f t c)
    {S : CalibratedLevelSeedPatch F
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)} {w : S.covector.ker}
    {μc νc : Measure ℝ}
    (Dp : OriginalSeedConditionalMoments S w μc νc)
    (hw : w ∈ S.labels) (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μc νc gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μc νc) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {Glane : ℝ} {glane : ℝ → ℝ → ℝ}
    (hglane : Measurable (Function.uncurry glane))
    (hgblane : ∀ a b, |glane a b| ≤ Glane)
    (hkin_nonneg : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      0 ≤ Dp.originalFocalKinetic gap a b v)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      c * ∑ i, v i ^ 2 ≤ Dp.originalFocalKinetic gap a b v)
    (α β : Measure UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      PointProcess.MarkedCloudPoint → PointProcess.MarkedCloudPoint → ℝ)
    (hAtlas : AtlasStationaryPressureIdentification (Seed := Seed) (a := a)
      (κ := κ) (lambda := lambda) α β
      (originalLaneDatumFamily A B Dp hF hw hq hgap hbounds pi hpi horder
        hglane hgblane hkin_nonneg) coef probeFam q)
    (hFrozenN2 : FrozenStationaryPressureIdentification (Seed := Seed) (a := a)
      (κ := κ) (lambda := lambda) g α β coef probeFam q)
    (hEnv : UpperPoolEnvelope qU mU pc
      (originalLaneDatumFamily A B Dp hF hw hq hgap hbounds pi hpi horder
        hglane hgblane hkin_nonneg))
    (hderiv : FinslerReadoutTiltDerivative
      (paperEndgameData_actual_wired hF hcomplete hdim ωM ρ₀ ρ₁ hA hB hAB hμA hνB
        P X Y hX hY hXi hYi hXlaw hYlaw hXY
        (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
          hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
        (paperCalibratedPotential_lipschitz hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
          hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
        seedDatum frozenCost hfrozen_int hfrozen_dom hfrozen_mean_shifted qU mU
        hmU pc data hpc Dp hw hq hgap hbounds pi hpi horder hglane hgblane
        hkin_nonneg hc hkin α β coef probeFam hAtlas hFrozenN2 hEnv).pressureLower) :
    let _instFinalMetric : MetricSpace M := F.metricSpace
    let _instFinalProper : ProperSpace M := F.properSpace_of_complete hcomplete
    ∃! pi : ProbabilityMeasure (M × M),
      IsPaperSelectorPlan (physicalSourceProbability ωM ρ₀)
        (physicalTargetProbability ωM ρ₁) P X Y pi := by
  classical
  let _instFinalMetric : MetricSpace M := F.metricSpace
  let _instFinalProper : ProperSpace M := F.properSpace_of_complete hcomplete
  have hmain := existsUnique_general_finsler_selector_at_derivedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY seedDatum frozenCost hfrozen_int hfrozen_dom hfrozen_mean_shifted qU mU hmU pc data hpc Dp hw hq hgap hbounds pi hpi horder hglane hgblane hkin_nonneg hc hkin α β coef probeFam hAtlas hFrozenN2 hEnv hderiv
  obtain ⟨hAinput, hpalm, derivative, hHasDeriv, hpiuniq⟩ := hmain
  obtain ⟨pi0, ⟨hMoment, hNbhd, hMet, hOpt⟩, hUniq⟩ := hpiuniq
  refine ⟨pi0, ⟨hOpt, hNbhd, hMet⟩, ?_⟩
  intro pi2 hpi2
  exact (paperSelectorPlan_independent_of_potential P X Y
    ⟨hOpt, hNbhd, hMet⟩ hpi2).symm

/-- **Internal reconstruction clauses, factored out of the paper-facing theorem.**

These are the three conclusion clauses of
existsUnique_general_finsler_selector_at_derivedPotential that are *not* part of the
paper displayed conclusion: (a) the nonempty final-input record, (b) the palm-law scalar
normalization limit, and (c) the existence of the readout derivative at zero tilt.  They are
kept here as a separate lemma so that existsUnique_paperSelectorPlan reads exactly like the
paper; the moment identity that ties the derivative to the plan remains part of the main
theorem. -/
theorem internalSelectorClauses
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (X n i))
    (hY : ∀ (n : ℕ) (i : Fin (n + 1)), Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ (n : ℕ) (i : Fin (n + 1)), (P n).map (X n i) =
      ((physicalSourceProbability ωM ρ₀ : Measure M)))
    (hYlaw : ∀ (n : ℕ) (j : Fin (n + 1)), (P n).map (Y n j) =
      ((physicalTargetProbability ωM ρ₁ : Measure M)))
    (hXY : ∀ n, IndepFun (fun ξ i => X n i ξ) (fun ξ j => Y n j ξ) (P n))
    (seedDatum : PaperGeometricSeedDatum F
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
      (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁))
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    {Seed : ℕ → F.CalibratedSeedWindow
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)} {a : M → Z}
    {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}
    {g : FinalProbeSpace A B → ℝ → Z → ℝ} {q : ℝ}
    (frozenCost : (f : FinalProbeSpace A B) → ℝ → ∀ n, Ω n → ℝ)
    (hfrozen_int : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (P n))
    (hfrozen_dom : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤
        finslerSupportedPressure F (physicalSourceProbability ωM ρ₀)
          (physicalTargetProbability ωM ρ₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx => Or.inl hx) (hνB.mono fun _ hy => Or.inr hy)
          (fun i => X n i s) (fun i => Y n i s)
          (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
            hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    (hfrozen_mean_shifted : ∀ (f : FinalProbeSpace A B) (t ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        frozenPressureLower (K := A ∪ B) Seed a κ lambda g q f t +
            |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n)
    (qU mU : ℕ) (hmU : 0 < mU)
    (pc : FinalProbeSpace A B → ℝ → (Fin qU → Fin mU) → ℝ)
    {Am Cm : Type*} [MeasurableSpace Am] [MeasurableSpace Cm]
    (data : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < (1 : ℝ) →
      PopData F (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
        hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
        qU mU hmU ωM ρ₀ ρ₁ hA hB hμA hνB Am Cm f t)
    (hpc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (hpert : |t| < (1 : ℝ))
      (c : Fin qU → Fin mU), (data f t hpert).p c t = pc f t c)
    {S : CalibratedLevelSeedPatch F
      (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
        hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)} {w : S.covector.ker}
    {μc νc : Measure ℝ}
    (Dp : OriginalSeedConditionalMoments S w μc νc)
    (hw : w ∈ S.labels) (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μc νc gap diameter)
    (pi : Measure (ℝ × ℝ)) [IsFiniteMeasure pi]
    (hpi : Vlasov.IsCoupling pi μc νc) (horder : ∀ᵐ p ∂pi, p.1 ≤ p.2)
    {Glane : ℝ} {glane : ℝ → ℝ → ℝ}
    (hglane : Measurable (Function.uncurry glane))
    (hgblane : ∀ a b, |glane a b| ≤ Glane)
    (hkin_nonneg : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      0 ≤ Dp.originalFocalKinetic gap a b v)
    {c : ℝ} (hc : 0 < c)
    (hkin : ∀ a b (v : Fin (finrank ℝ S.covector.ker) → ℝ),
      c * ∑ i, v i ^ 2 ≤ Dp.originalFocalKinetic gap a b v)
    (α β : Measure UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      PointProcess.MarkedCloudPoint → PointProcess.MarkedCloudPoint → ℝ)
    (hAtlas : AtlasStationaryPressureIdentification (Seed := Seed) (a := a)
      (κ := κ) (lambda := lambda) α β
      (originalLaneDatumFamily A B Dp hF hw hq hgap hbounds pi hpi horder
        hglane hgblane hkin_nonneg) coef probeFam q)
    (hFrozenN2 : FrozenStationaryPressureIdentification (Seed := Seed) (a := a)
      (κ := κ) (lambda := lambda) g α β coef probeFam q)
    (hEnv : UpperPoolEnvelope qU mU pc
      (originalLaneDatumFamily A B Dp hF hw hq hgap hbounds pi hpi horder
        hglane hgblane hkin_nonneg))
    (hderiv : FinslerReadoutTiltDerivative
      (paperEndgameData_actual_wired hF hcomplete hdim ωM ρ₀ ρ₁ hA hB hAB hμA hνB
        P X Y hX hY hXi hYi hXlaw hYlaw hXY
        (paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
          hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
        (paperCalibratedPotential_lipschitz hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
          hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB)
        seedDatum frozenCost hfrozen_int hfrozen_dom hfrozen_mean_shifted qU mU
        hmU pc data hpc Dp hw hq hgap hbounds pi hpi horder hglane hgblane
        hkin_nonneg hc hkin α β coef probeFam hAtlas hFrozenN2 hEnv).pressureLower) :
    let u := paperCalibratedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
      hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
    let hu : (letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :=
      paperCalibratedPotential_lipschitz hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
        hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB
    let D := paperEndgameData_actual_wired hF hcomplete hdim ωM ρ₀ ρ₁ hA hB hAB
      hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY u hu seedDatum frozenCost
      hfrozen_int hfrozen_dom hfrozen_mean_shifted qU mU hmU pc data hpc Dp hw hq
      hgap hbounds pi hpi horder hglane hgblane hkin_nonneg hc hkin α β coef probeFam
      hAtlas hFrozenN2 hEnv
    let _instFinalMetric : MetricSpace M := F.metricSpace
    let _instFinalProper : ProperSpace M := F.properSpace_of_complete hcomplete
    Nonempty (FinslerSelectorFinalInputs F (physicalSourceProbability ωM ρ₀)
          (physicalTargetProbability ωM ρ₁) hA hB hμA hνB P X Y u) ∧
      Tendsto (fun n => D.geometric.palm_sample_law.normalization n *
        D.geometric.palm_sample_law.maskedMean n -
        D.geometric.palm_sample_law.populationValue n) atTop (𝓝 0) ∧
      ∃ derivative : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ,
        ∀ f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ,
          HasDerivAt (fun t => D.pressureLower f t) (derivative f) 0 := by
  classical
  have hmain := existsUnique_general_finsler_selector_at_derivedPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμA hνB P X Y hX hY hXi hYi hXlaw hYlaw hXY seedDatum frozenCost hfrozen_int hfrozen_dom hfrozen_mean_shifted qU mU hmU pc data hpc Dp hw hq hgap hbounds pi hpi horder hglane hgblane hkin_nonneg hc hkin α β coef probeFam hAtlas hFrozenN2 hEnv hderiv
  obtain ⟨hAinput, hpalm, derivative, hHasDeriv, hpiuniq⟩ := hmain
  exact ⟨hAinput, hpalm, derivative, hHasDeriv⟩

end OTSelector.Reconstruction
