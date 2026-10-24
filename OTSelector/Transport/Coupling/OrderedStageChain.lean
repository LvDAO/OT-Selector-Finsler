import OTSelector.Transport.Coupling.FiniteMarginalSplit
import OTSelector.Transport.Coupling.FiniteMeasureGluing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseStageCouplingOrderedCore.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseStageCouplingOrderedCore`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseStageCouplingOrderedCore

**Conditions:** Finite stage measures have active-plus-birth/active-plus-exit marginal identities, finite mass and a standard Borel state space; the initial active mass vanishes.

**Objects:** Class-labelled active/completed prefix witnesses preserving birth-before-exit order.

**Proof detail:** Split the next stage along active and newly born masses, disintegrate/glue the actual active joint, and add completed exits and labelled births; induction preserves the exact marginals and chronological support.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185), Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4); [OTSelector project, Original classwise stage Neumann construction](main.tex#eq:interleaved-path-stage-neumann), main.tex label eq:interleaved-path-stage-neumann, line 10809.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Genuine class-labelled finite coupling chains retain birth-before-exit order. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 600000
variable {E : Type*} [MeasurableSpace E]

/-- A finite prefix of the actual class-labelled source or target laws. -/
def finiteStageLabelledPrefix (S : ℕ → Measure E) (n : ℕ) : Measure (ℕ × E) :=
  ∑ k ∈ Finset.range n, (S k).map (fun x ↦ (k, x))

@[simp] theorem finiteStageLabelledPrefix_zero (S : ℕ → Measure E) :
    finiteStageLabelledPrefix S 0 = 0 := by simp [finiteStageLabelledPrefix]

@[simp] theorem finiteStageLabelledPrefix_succ (S : ℕ → Measure E) (n : ℕ) :
    finiteStageLabelledPrefix S (n + 1) =
      finiteStageLabelledPrefix S n + (S n).map (fun x ↦ (n, x)) := by
  simp [finiteStageLabelledPrefix, Finset.sum_range_succ]

/-- A prefix consists of actual completed paths and actual still-active paths.
The active plan retains each path's original source class. -/
structure FiniteOrderedStagePrefix (ν S T : ℕ → Measure E) (n : ℕ) where
  completed : Measure ((ℕ × E) × (ℕ × E))
  active : Measure ((ℕ × E) × E)
  completed_finite : IsFiniteMeasure completed
  active_finite : IsFiniteMeasure active
  source_balance : completed.fst + active.fst = finiteStageLabelledPrefix S n
  target_balance : completed.snd = finiteStageLabelledPrefix T n
  active_target : active.snd = ν n
  completed_order : ∀ᵐ z ∂completed, z.1.1 ≤ z.2.1
  active_birth : ∀ᵐ a ∂active.fst, a.1 < n

/-- An empty initial retained law starts the actual induction with zero plans. -/
theorem exists_finiteOrderedStagePrefix_zero (ν S T : ℕ → Measure E) (hν : ν 0 = 0) :
    Nonempty (FiniteOrderedStagePrefix ν S T 0) := by
  refine ⟨⟨0, 0, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp
  · simp
  · simpa using hν.symm
  · simp
  · simp

/-- The actual splits and three-point joint of one class extension. Keeping
this witness allows order and cost arguments to share the same construction. -/
structure FiniteOrderedStageStep (ν S T : ℕ → Measure E) (n : ℕ)
    (w : FiniteOrderedStagePrefix ν S T n) (π : Measure (E × E)) where
  continuing : Measure (E × E)
  birth : Measure (E × E)
  triple : Measure (((ℕ × E) × E) × E)
  nextActive : Measure ((ℕ × E) × E)
  exits : Measure ((ℕ × E) × E)
  continuing_finite : IsFiniteMeasure continuing
  birth_finite : IsFiniteMeasure birth
  triple_finite : IsFiniteMeasure triple
  nextActive_finite : IsFiniteMeasure nextActive
  exits_finite : IsFiniteMeasure exits
  source_decomp : continuing + birth = π
  continuing_source : continuing.fst = ν n
  birth_source : birth.fst = S n
  triple_first : triple.fst = w.active
  triple_second : triple.map (fun z ↦ (z.1.2, z.2)) = continuing
  target_decomp : nextActive + exits =
    triple.map (fun z ↦ (z.1.1, z.2)) + birth.map (fun z ↦ ((n, z.1), z.2))
  active_target : nextActive.snd = ν (n + 1)
  exits_target : exits.snd = T n

/-- Actual one-step RN splitting and disintegration produce the extension
witness, including its genuine three-point plan and both exact pair marginals. -/
theorem exists_finiteOrderedStageStep
    (ν S T : ℕ → Measure E) (n : ℕ)
    [StandardBorelSpace E] [Nonempty E]
    [∀ k, IsFiniteMeasure (ν k)] [∀ k, IsFiniteMeasure (S k)]
    [∀ k, IsFiniteMeasure (T k)]
    (w : FiniteOrderedStagePrefix ν S T n)
    (π : Measure (E × E)) [IsFiniteMeasure π]
    (hπ₁ : π.fst = ν n + S n) (hπ₂ : π.snd = ν (n + 1) + T n) :
    Nonempty (FiniteOrderedStageStep ν S T n w π) := by
  let : IsFiniteMeasure w.active := w.active_finite
  obtain ⟨c, b, hc, hb, hcb, hcν, hbS⟩ :=
    exists_finiteStageCoupling_source_split π (ν n) (S n) hπ₁
  let : IsFiniteMeasure c := hc
  let : IsFiniteMeasure b := hb
  obtain ⟨θ, hθ, hθ₁, hθ₂⟩ :=
    exists_finiteStageCouplingJoint w.active c (w.active_target.trans hcν.symm)
  let : IsFiniteMeasure θ := hθ
  let incoming := θ.map (fun z ↦ (z.1.1, z.2)) + b.map (fun z ↦ ((n, z.1), z.2))
  have hδ : Measurable (fun z : ((ℕ × E) × E) × E ↦ (z.1.1, z.2)) := by fun_prop
  have hfresh : Measurable (fun z : E × E ↦ ((n, z.1), z.2)) := by fun_prop
  have hδ₂ : (θ.map (fun z ↦ (z.1.1, z.2))).snd = c.snd := by
    rw [← hθ₂]
    simp only [Measure.snd, Measure.map_map measurable_snd hδ,
      Measure.map_map measurable_snd
        (show Measurable (fun z : ((ℕ × E) × E) × E ↦ (z.1.2, z.2)) by fun_prop)]
    rfl
  have hfresh₂ : (b.map (fun z ↦ ((n, z.1), z.2))).snd = b.snd := by
    rw [Measure.snd, Measure.map_map measurable_snd hfresh]
    rfl
  have hincoming₂ : incoming.snd = ν (n + 1) + T n := by
    dsimp only [incoming]
    rw [Measure.snd_add, hδ₂, hfresh₂, ← Measure.snd_add, hcb, hπ₂]
  obtain ⟨α, β, hα, hβ, hαβ, hαν, hβT⟩ :=
    exists_finiteStageCoupling_target_split incoming (ν (n + 1)) (T n) hincoming₂
  exact ⟨⟨c, b, θ, α, β, hc, hb, hθ, hα, hβ, hcb, hcν, hbS,
    hθ₁, hθ₂, hαβ, hαν, hβT⟩⟩

/-- The same genuine step witness extends the ordered-prefix invariant.
The completed and active measures are explicit projections of this witness. -/
def FiniteOrderedStageStep.toPrefix
    {ν S T : ℕ → Measure E} {n : ℕ}
    {w : FiniteOrderedStagePrefix ν S T n} {π : Measure (E × E)}
    (v : FiniteOrderedStageStep ν S T n w π) :
    FiniteOrderedStagePrefix ν S T (n + 1) := by
  let : IsFiniteMeasure w.completed := w.completed_finite
  let : IsFiniteMeasure w.active := w.active_finite
  let : IsFiniteMeasure v.continuing := v.continuing_finite
  let : IsFiniteMeasure v.birth := v.birth_finite
  let : IsFiniteMeasure v.triple := v.triple_finite
  let : IsFiniteMeasure v.nextActive := v.nextActive_finite
  let : IsFiniteMeasure v.exits := v.exits_finite
  let δ := v.triple.map (fun z ↦ (z.1.1, z.2))
  let fresh := v.birth.map (fun z ↦ ((n, z.1), z.2))
  let incoming := δ + fresh
  have hδ : Measurable (fun z : ((ℕ × E) × E) × E ↦ (z.1.1, z.2)) := by fun_prop
  have hδ₁ : δ.fst = w.active.fst := by
    change (v.triple.map (fun z ↦ (z.1.1, z.2))).fst = w.active.fst
    rw [← v.triple_first]
    simp only [Measure.fst, Measure.map_map measurable_fst hδ,
      Measure.map_map measurable_fst measurable_fst]
    rfl
  have hfresh : Measurable (fun z : E × E ↦ ((n, z.1), z.2)) := by fun_prop
  have hfresh₁ : fresh.fst = (S n).map (fun x ↦ (n, x)) := by
    rw [show fresh = v.birth.map _ from rfl, Measure.fst,
      Measure.map_map measurable_fst hfresh]
    change v.birth.map ((fun x ↦ (n, x)) ∘ Prod.fst) = _
    rw [← Measure.map_map (show Measurable (fun x : E ↦ (n, x)) by fun_prop) measurable_fst]
    exact congrArg (fun μ ↦ μ.map (fun x ↦ (n, x))) v.birth_source
  have hαβ : v.nextActive + v.exits = incoming := v.target_decomp
  have hbirth : ∀ᵐ a ∂incoming.fst, a.1 ≤ n := by
    rw [show incoming = δ + fresh from rfl, Measure.fst_add, hδ₁, hfresh₁,
      ae_add_measure_iff]
    constructor
    · exact w.active_birth.mono fun a ha ↦ Nat.le_of_lt ha
    · exact (ae_map_iff (show Measurable (fun x : E ↦ (n, x)) by fun_prop).aemeasurable
        (by measurability)).mpr (ae_of_all _ fun _ ↦ le_rfl)
  have hαle : v.nextActive ≤ incoming := by rw [← hαβ]; exact Measure.le_add_right le_rfl
  have hβle : v.exits ≤ incoming := by rw [← hαβ]; exact Measure.le_add_left le_rfl
  have hαbirth : ∀ᵐ a ∂v.nextActive.fst, a.1 < n + 1 := by
    have h : ∀ᵐ a ∂v.nextActive.fst, a.1 ≤ n :=
      hbirth.filter_mono (ae_mono (Measure.fst_mono hαle))
    exact h.mono fun a ha ↦ Nat.lt_succ_of_le ha
  have hβbirth : ∀ᵐ z ∂v.exits, z.1.1 ≤ n :=
    ae_of_ae_map measurable_fst.aemeasurable
      (hbirth.filter_mono (ae_mono (Measure.fst_mono hβle)))
  let exit := v.exits.map (fun z ↦ (z.1, (n, z.2)))
  have hexit : Measurable (fun z : (ℕ × E) × E ↦ (z.1, (n, z.2))) := by fun_prop
  have hexit₁ : exit.fst = v.exits.fst := by
    rw [show exit = v.exits.map _ from rfl, Measure.fst,
      Measure.map_map measurable_fst hexit]
    rfl
  have hexit₂ : exit.snd = (T n).map (fun x ↦ (n, x)) := by
    rw [show exit = v.exits.map _ from rfl, Measure.snd,
      Measure.map_map measurable_snd hexit]
    change v.exits.map ((fun x ↦ (n, x)) ∘ Prod.snd) = _
    rw [← Measure.map_map (show Measurable (fun x : E ↦ (n, x)) by fun_prop) measurable_snd]
    exact congrArg (fun μ ↦ μ.map (fun x ↦ (n, x))) v.exits_target
  have hexit_order : ∀ᵐ z ∂exit, z.1.1 ≤ z.2.1 := by
    exact (ae_map_iff hexit.aemeasurable (by measurability)).mpr hβbirth
  refine ⟨w.completed + exit, v.nextActive, inferInstance, v.nextActive_finite,
    ?_, ?_, v.active_target, ?_, hαbirth⟩
  · rw [Measure.fst_add, hexit₁, add_assoc, add_comm v.exits.fst v.nextActive.fst,
      ← Measure.fst_add, hαβ]
    rw [show incoming = δ + fresh from rfl, Measure.fst_add, hδ₁, hfresh₁,
      ← add_assoc, w.source_balance, finiteStageLabelledPrefix_succ]
  · rw [Measure.snd_add, w.target_balance, hexit₂, finiteStageLabelledPrefix_succ]
  · exact ae_add_measure_iff.mpr ⟨w.completed_order, hexit_order⟩

/-- One actual class step extends the ordered finite-prefix invariant. -/
theorem exists_finiteOrderedStagePrefix_succ
    (ν S T : ℕ → Measure E) (n : ℕ)
    [StandardBorelSpace E] [Nonempty E]
    [∀ k, IsFiniteMeasure (ν k)] [∀ k, IsFiniteMeasure (S k)]
    [∀ k, IsFiniteMeasure (T k)]
    (w : FiniteOrderedStagePrefix ν S T n)
    (π : Measure (E × E)) [IsFiniteMeasure π]
    (hπ₁ : π.fst = ν n + S n) (hπ₂ : π.snd = ν (n + 1) + T n) :
    Nonempty (FiniteOrderedStagePrefix ν S T (n + 1)) := by
  obtain ⟨v⟩ := exists_finiteOrderedStageStep ν S T n w π hπ₁ hπ₂
  exact ⟨v.toPrefix⟩

/-- Every genuine finite class chain admits the completed/active invariant at
its actual finite endpoint. Each step is constructed from the supplied plan. -/
theorem exists_finiteOrderedStagePrefix
    [StandardBorelSpace E] [Nonempty E]
    (ν S T : ℕ → Measure E) (π : ℕ → Measure (E × E)) (n : ℕ)
    [∀ k, IsFiniteMeasure (ν k)] [∀ k, IsFiniteMeasure (S k)]
    [∀ k, IsFiniteMeasure (T k)] [∀ k, IsFiniteMeasure (π k)]
    (hν₀ : ν 0 = 0)
    (hπ₁ : ∀ k < n, (π k).fst = ν k + S k)
    (hπ₂ : ∀ k < n, (π k).snd = ν (k + 1) + T k) :
    Nonempty (FiniteOrderedStagePrefix ν S T n) := by
  revert hπ₁ hπ₂
  induction n with
  | zero =>
      intro _ _
      exact exists_finiteOrderedStagePrefix_zero ν S T hν₀
  | succ n ih =>
      intro hπ₁ hπ₂
      obtain ⟨w⟩ := ih (fun k hk ↦ hπ₁ k (Nat.lt_succ_of_lt hk))
        (fun k hk ↦ hπ₂ k (Nat.lt_succ_of_lt hk))
      exact exists_finiteOrderedStagePrefix_succ ν S T n w (π n)
        (hπ₁ n (Nat.lt_succ_self n)) (hπ₂ n (Nat.lt_succ_self n))

end OTSelector.Reconstruction

end
end
