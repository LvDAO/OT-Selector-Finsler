import OTSelector.Reconstruction.FinslerOriginalFrozenSupportBoundWiring
import OTSelector.Reconstruction.FinslerOriginalTilePairRegularity
import OTSelector.Probability.CanonicalIidSampling

/-!
# Frozen tile integrability on the original sampled arrays

The frozen physical cost is bounded on each retained geometric tile mask, although it need
not be bounded away from that mask. This local bound controls every feasible fractional
readout. Measurable endpoint arrays, probe entries and assignment entries therefore give
integrability against any finite sample measure, at every real frozen scale. In particular
the argument applies to the original two-colour iid law and to the growing physical scale.
-/

open Set Function Matrix MeasureTheory ProbabilityTheory Manifold Module
open OTSelector.Geometry OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped Topology ContDiff NNReal ENNReal BigOperators BoundedContinuousFunction

noncomputable section

namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
  {D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss}
  {ε : ℝ} (T : D.TaylorTiles ε)

namespace PopulationLocalPressureCore.TaylorTiles

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- A masked tile entry is measurable on the original sample space. The mask selects the
corresponding entry of the measurable simultaneous frozen matrix. -/
theorem measurable_maskedFrozenCoreMatrix
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenIntegrabilityMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (X Y : Ω → Fin n → M)
    (hX : ∀ i, Measurable (fun s ↦ X s i))
    (hY : ∀ j, Measurable (fun s ↦ Y s j))
    (scale t : ℝ) (h : Ω → T.Index → Matrix (Fin n) (Fin n) ℝ)
    (hh : ∀ c i j, Measurable (fun s ↦ h s c i j)) (c : T.Index) (i j : Fin n) :
    Measurable (fun s ↦ maskedFrozenCost (T.edgeEvent (X s) (Y s) c)
      (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c)
        (X s) (Y s) scale t (h s c)) i j) := by
  classical
  have htotal := T.measurable_originalFrozenCoreMatrix hF hcomplete hu ha hinj
    X Y hX hY scale t h hh i j
  have hmask := T.measurable_edgeEvent hu ha X Y hX hY c i j
  have hid : (fun s ↦ maskedFrozenCost (T.edgeEvent (X s) (Y s) c)
      (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c)
        (X s) (Y s) scale t (h s c)) i j) =
      fun s ↦ if (i, j) ∈ T.edgeEvent (X s) (Y s) c then
        T.originalFrozenCoreMatrix (X s) (Y s) scale t (h s) i j else 0 := by
    funext s
    split_ifs with hs
    · rw [maskedFrozenCost_apply_of_mem hs,
        T.originalFrozenCoreMatrix_on (X s) (Y s) scale t (h s) hs]
    · exact maskedFrozenCost_apply_of_not_mem hs
  rw [hid]
  exact Measurable.ite hmask htotal measurable_const

/-- Entrywise measurable assignments produce measurable frozen tile costs; no
measurability assumption on the assembled cost is needed. -/
theorem measurable_tileFrozenCost_of_entries
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenIntegrabilityMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (X Y : Ω → Fin n → M)
    (hX : ∀ i, Measurable (fun s ↦ X s i))
    (hY : ∀ j, Measurable (fun s ↦ Y s j))
    (h : Ω → T.Index → Matrix (Fin n) (Fin n) ℝ)
    (hh : ∀ c i j, Measurable (fun s ↦ h s c i j))
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, Measurable (fun s ↦ A s i j)) (scale t : ℝ) (c : T.Index) :
    Measurable (T.tileFrozenCost X Y h A scale t c) := by
  unfold tileFrozenCost fractionalAssignmentCost
  exact Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
    (hA i j).mul (T.measurable_maskedFrozenCoreMatrix hF hcomplete hu ha hinj
      X Y hX hY scale t h hh c i j)

/-- Each tile has a uniform masked entry bound at every real scale. Only its own
geometric mask is used to bound the frozen physical cost. -/
theorem exists_maskedFrozenCoreMatrix_bound
    (X Y : Ω → Fin n → M) (h : Ω → T.Index → Matrix (Fin n) (Fin n) ℝ)
    (scale t : ℝ) (c : T.Index) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ s i j, |h s c i j| ≤ G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s i j,
      |maskedFrozenCost (T.edgeEvent (X s) (Y s) c)
        (frozenCoreMatrix (T.core c) ε (fun _ _ ↦ T.reference c)
          (X s) (Y s) scale t (h s c)) i j| ≤ C := by
  obtain ⟨Mfc, hMfc0, hMfc⟩ := T.exists_frozenCost_bound_on_mask c
  refine ⟨|1 - 2 * ε| * (|scale| * Mfc) + |t| * G, by positivity, ?_⟩
  intro s i j
  by_cases hs : (i, j) ∈ T.edgeEvent (X s) (Y s) c
  · rw [maskedFrozenCost_apply_of_mem hs]
    exact T.tileCostPair_abs_le_on_mask c scale t (fun _ ↦ h s c i j) hMfc
      (fun _ ↦ hG s i j) (X s i, Y s j) hs
  · rw [maskedFrozenCost_apply_of_not_mem hs, abs_zero]
    positivity

/-- Feasibility turns the local geometric entry bound into a bound on the total
tile cost. Optimality of the assignment is unnecessary for this estimate. -/
theorem exists_tileFrozenCost_bound_of_feasible
    (X Y : Ω → Fin n → M) (h : Ω → T.Index → Matrix (Fin n) (Fin n) ℝ)
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ s, A s ∈ doublyStochastic ℝ (Fin n))
    (scale t : ℝ) (c : T.Index) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ s i j, |h s c i j| ≤ G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, |T.tileFrozenCost X Y h A scale t c s| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := T.exists_maskedFrozenCoreMatrix_bound X Y h scale t c hG0 hG
  refine ⟨(n : ℝ) * C, mul_nonneg (Nat.cast_nonneg _) hC0, fun s ↦ ?_⟩
  exact fractionalAssignmentCost_abs_le_of_feasible (hA s) (hC s)

/-- Geometric mask bounds and measurable entries imply integrability on every
finite original sample law, without a global frozen-cost bound or a cost callback. -/
theorem integrable_tileFrozenCost_of_geometricMask
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenIntegrabilityMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (sample : Measure Ω) [IsFiniteMeasure sample]
    (X Y : Ω → Fin n → M)
    (hX : ∀ i, Measurable (fun s ↦ X s i))
    (hY : ∀ j, Measurable (fun s ↦ Y s j))
    (h : Ω → T.Index → Matrix (Fin n) (Fin n) ℝ)
    (hh : ∀ c i j, Measurable (fun s ↦ h s c i j))
    (A : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hAmeas : ∀ i j, Measurable (fun s ↦ A s i j))
    (hA : ∀ s, A s ∈ doublyStochastic ℝ (Fin n))
    (scale t : ℝ) (c : T.Index) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ s i j, |h s c i j| ≤ G) :
    Integrable (T.tileFrozenCost X Y h A scale t c) sample := by
  obtain ⟨C, _, hC⟩ := T.exists_tileFrozenCost_bound_of_feasible X Y h A hA
    scale t c hG0 hG
  exact Integrable.of_bound
    (T.measurable_tileFrozenCost_of_entries hF hcomplete hu ha hinj X Y hX hY h hh
      A hAmeas scale t c).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun s ↦ by simpa only [Real.norm_eq_abs] using hC s)

/-- The normalized scene probes give integrable frozen tile costs on arbitrary
finite sample laws at any sequence of physical scales, including growing scales. -/
theorem integrable_normalizedProbe_tileFrozenCost_of_geometricMask
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (K : Set M)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenIntegrabilityMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n j, Measurable (Y n j))
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hbaseMeas : ∀ n c i j, Measurable (fun s ↦ base n s c i j))
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hAssignMeas : ∀ n i j, Measurable (fun s ↦ Assign n s i j))
    (hAssign : ∀ n s, Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (scale : ℕ → ℝ) {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ n s c i j, |base n s c i j| ≤ Bp) :
    ∀ t n c, Integrable (T.tileFrozenCost
      (fun s i ↦ X n i s) (fun s j ↦ Y n j s)
      (fun s c' ↦ normalizedProbe (K := K) base t n s c')
      (Assign n) (scale n) t c) (sample n) := by
  intro t n c
  apply T.integrable_tileFrozenCost_of_geometricMask hF hcomplete hu ha hinj
    (sample n) (fun s i ↦ X n i s) (fun s j ↦ Y n j s) (hX n) (hY n)
    (fun s c' ↦ normalizedProbe (K := K) base t n s c')
    (fun c' i j ↦ (hbaseMeas n c' i j).const_mul
      (1 / ((1 + |t|) * ((n + 1 : ℕ) : ℝ))))
    (Assign n) (hAssignMeas n) (hAssign n) (scale n) t c
    (show 0 ≤ Bp / ((n + 1 : ℕ) : ℝ) from div_nonneg hBp (by positivity))
  exact fun s i j ↦ normalizedProbe_abs_le (K := K) base hBp hbase t n s c i j

/-- The original canonical independent sample has integrable frozen tile costs
at the paper's scale `(n + 1) ^ (2 / (dim E - 1))`. No decaying-scale bound is used. -/
theorem integrable_canonicalIID_tileFrozenCost_of_geometricMask (K : Set M)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenIntegrabilityMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (μ ν : ProbabilityMeasure M)
    (base : ∀ n, canonicalOmega M n → T.Index →
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hbaseMeas : ∀ n c i j, Measurable (fun s ↦ base n s c i j))
    (Assign : ∀ n, canonicalOmega M n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hAssignMeas : ∀ n i j, Measurable (fun s ↦ Assign n s i j))
    (hAssign : ∀ n s, Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    {Bp : ℝ} (hBp : 0 ≤ Bp) (hbase : ∀ n s c i j, |base n s c i j| ≤ Bp) :
    ∀ t n c, Integrable (T.tileFrozenCost
      (fun s i ↦ canonicalX n i s) (fun s j ↦ canonicalY n j s)
      (fun s c' ↦ normalizedProbe (K := K) base t n s c') (Assign n)
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) t c)
      (canonicalLaw μ ν n) := by
  exact T.integrable_normalizedProbe_tileFrozenCost_of_geometricMask K
    hF hcomplete hu ha hinj (canonicalLaw μ ν) canonicalX canonicalY
    measurable_canonicalX measurable_canonicalY base hbaseMeas Assign hAssignMeas hAssign
    (fun n ↦ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1)))) hBp hbase

end PopulationLocalPressureCore.TaylorTiles

open PopulationLocalPressureCore.TaylorTiles

variable [IsManifold 𝓘(ℝ, E) ⊤ M]
  [MeasurableSpace.CountablySeparated (ℚ → M)]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {q : ℝ}

/-- The actual lower-probability lane with frozen integrability derived on the retained
geometric masks. Primitive entry measurability replaces the assembled-cost callback, and
compact tile geometry supplies the local frozen-cost bounds at the genuine iid scale. -/
theorem hprobFrozenInputs_actual_lane_of_geometricMask
    [PseudoMetricSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFrozenSupportBoundMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hε : 0 ≤ ε) (hε1 : 2 * ε < 1)
    (hdist : ∀ x y : M, dist x y = (F.lengthEDist x y).toReal)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (dens₀ dens₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (dens₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM dens₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM dens₁ : Measure M), y ∈ B)
    (sample : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (sample n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (sample n)) (hYi : ∀ n, iIndepFun (Y n) (sample n))
    (hXlaw : ∀ n i, (sample n).map (X n i) =
      (physicalSourceProbability ωM dens₀ : Measure M))
    (hYlaw : ∀ n i, (sample n).map (Y n i) =
      (physicalTargetProbability ωM dens₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (sample n))
    (radius : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ)
    (base : ∀ n, Ω n → T.Index → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Assign : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    {Bp : ℝ} (hBp : 0 ≤ Bp)
    (hbase : ∀ (n : ℕ) (s : Ω n) (c' : T.Index) (i j : Fin (n + 1)),
      |base n s c' i j| ≤ Bp)
    (hAssignDS : ∀ (n : ℕ) (s : Ω n),
      Assign n s ∈ doublyStochastic ℝ (Fin (n + 1)))
    (hbaseMeas : ∀ n c i j, Measurable (fun s ↦ base n s c i j))
    (hAssignMeas : ∀ n i j, Measurable (fun s ↦ Assign n s i j))
    (hPopt : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      OptimalFractionalAssignment (perturbedEdgeCost
        (fun i j ↦ (((n + 1 : ℕ) : ℝ) ^
            (2 / ((Module.finrank ℝ E : ℝ) - 1))) *
          distanceSlackEdgeCost (fun i ↦ X n i s) (fun i ↦ Y n i s) u i j)
        (carrierProbeMatrix (physicalSourceProbability ωM dens₀)
          (physicalTargetProbability ωM dens₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) f) t) (Assign n s))
    (hgeom : ∀ (n : ℕ), ∀ᵐ s ∂sample n, ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c →
      FrozenCoreEdgeGeometry (T.core c) (T.cover c.1)
        (fun _ _ ↦ T.reference c) (fun i ↦ X n i s) (fun i ↦ Y n i s) i j)
    (hgh : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂sample n,
      ∀ (c : T.Index) (i j : Fin (n + 1)),
      (i, j) ∈ T.edgeEvent (fun i ↦ X n i s) (fun i ↦ Y n i s) c →
      |carrierProbeMatrix (physicalSourceProbability ωM dens₀)
          (physicalTargetProbability ωM dens₁) (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) f i j -
        normalizedProbe (K := A ∪ B) base t n s c i j| ≤ (‖f‖₊ : ℝ))
    (g : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → (ℚ → M) → ℝ)
    (hId : RootedTileCampbellMeanIdentification P a κ lambda g q sample
      (hprobFrozenCostFamily (K := A ∪ B) T X Y base Assign
        (fun n ↦ (((n + 1 : ℕ) : ℝ) ^
          (2 / ((Module.finrank ℝ E : ℝ) - 1))))) T.Index)
    (Ψ : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (hread : frozenPressureLower P a κ lambda g q = Ψ) :
    FinalProbLowerData F (physicalSourceProbability ωM dens₀)
      (physicalTargetProbability ωM dens₁) hA hB hμA hνB sample X Y u
      (fun f t ↦ Ψ f t - |t| * (‖f‖₊ : ℝ)) radius := by
  have hint := T.integrable_normalizedProbe_tileFrozenCost_of_geometricMask (A ∪ B)
    hF hcomplete hu ha hinj sample X Y hX hY base hbaseMeas Assign hAssignMeas hAssignDS
    (fun n ↦ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1)))) hBp hbase
  exact hprobFrozenInputs_actual_composed (T := T) (F := F) hdim ωM dens₀ dens₁
    hA hB hμA hνB sample X Y hX hY hXi hYi hXlaw hYlaw hXY radius
    (fun n ↦ (((n + 1 : ℕ) : ℝ) ^
      (2 / ((Module.finrank ℝ E : ℝ) - 1)))) base Assign
    (fun _f t n c ↦ hint t n c)
    (frozenSupportBound_of_geometricLane (T := T) (F := F) hF hcomplete hu ha
      hinj hε hε1 hdist (hA.union hB).measurableSet
      (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
      X Y base Assign sample hPopt hgeom hgh)
    g hId Ψ hread hcomplete hu

end OTSelector.Reconstruction
