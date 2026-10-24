import OTSelector.Transport.Coupling.OrderedStageChain
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseStageCouplingOrdered.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseStageCouplingOrdered`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseStageCouplingOrdered

**Conditions:** A finite standard-Borel coupling chain has the stated stage marginals and zero initial/final active mass; strict order additionally requires one source/target color absent per stage.

**Objects:** Actual class-labelled global couplings with birth class ≤ exit class, or strict inequality.

**Proof detail:** Build the ordered prefix inductively and eliminate the final active measure using its zero marginal; label-prefix support excludes later births and the single-color condition rules out equal birth/exit classes.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185), Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Original classwise stage Neumann construction](main.tex#eq:interleaved-path-stage-neumann), main.tex label eq:interleaved-path-stage-neumann, line 10809.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Actual ordered source-to-target couplings for finite classwise chains. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 600000
variable {E : Type*} [MeasurableSpace E]

/-- Every actual source in a finite labelled prefix has a class below its end. -/
theorem finiteStageLabelledPrefix_ae_lt (S : ℕ → Measure E) (n : ℕ) :
    ∀ᵐ a ∂finiteStageLabelledPrefix S n, a.1 < n := by
  rw [finiteStageLabelledPrefix, ae_finsetSum_measure_iff]
  intro k hk
  exact (ae_map_iff (show Measurable (fun x : E ↦ (k, x)) by fun_prop).aemeasurable
    (by measurability)).mpr (ae_of_all _ fun _ ↦ Finset.mem_range.mp hk)

/-- A zero class law contributes no source or target with that label, including
when the physical laws of different classes overlap. -/
theorem finiteStageLabelledPrefix_ae_ne_of_zero
    (S : ℕ → Measure E) (n i : ℕ) (hSi : S i = 0) :
    ∀ᵐ a ∂finiteStageLabelledPrefix S n, a.1 ≠ i := by
  rw [finiteStageLabelledPrefix, ae_finsetSum_measure_iff]
  intro k _
  by_cases hki : k = i
  · subst k
    simp [hSi]
  · exact (ae_map_iff (show Measurable (fun x : E ↦ (k, x)) by fun_prop).aemeasurable
      (by measurability)).mpr (ae_of_all _ fun _ ↦ hki)

/-- The actual finite stage plans yield a genuine coupling between all labelled
source and target laws, supported on nondecreasing classes. No global coupling,
path ancestry, disjointness, unit mass, or positive-mass hypothesis is supplied. -/
theorem exists_finiteOrderedClasswiseCoupling
    [StandardBorelSpace E] [Nonempty E]
    (ν S T : ℕ → Measure E) (π : ℕ → Measure (E × E)) (n : ℕ)
    [∀ k, IsFiniteMeasure (ν k)] [∀ k, IsFiniteMeasure (S k)]
    [∀ k, IsFiniteMeasure (T k)] [∀ k, IsFiniteMeasure (π k)]
    (hν₀ : ν 0 = 0) (hνn : ν n = 0)
    (hπ₁ : ∀ k < n, (π k).fst = ν k + S k)
    (hπ₂ : ∀ k < n, (π k).snd = ν (k + 1) + T k) :
    ∃ Γ : Measure ((ℕ × E) × (ℕ × E)), IsFiniteMeasure Γ ∧
      Vlasov.IsCoupling Γ (finiteStageLabelledPrefix S n) (finiteStageLabelledPrefix T n) ∧
      ∀ᵐ z ∂Γ, z.1.1 ≤ z.2.1 := by
  obtain ⟨w⟩ := exists_finiteOrderedStagePrefix ν S T π n hν₀ hπ₁ hπ₂
  have hactive : w.active = 0 := by
    apply (Measure.map_eq_zero_iff measurable_snd.aemeasurable).mp
    exact w.active_target.trans hνn
  refine ⟨w.completed, w.completed_finite, ⟨?_, w.target_balance⟩, w.completed_order⟩
  simpa [hactive, Measure.fst] using w.source_balance

/-- When at least one colour vanishes in each class, the actual labelled
coupling moves strictly forward in class. Coincident physical atoms cause no
exception because the conclusion concerns retained class labels. -/
theorem exists_finiteStrictOrderedClasswiseCoupling
    [StandardBorelSpace E] [Nonempty E]
    (ν S T : ℕ → Measure E) (π : ℕ → Measure (E × E)) (n : ℕ)
    [∀ k, IsFiniteMeasure (ν k)] [∀ k, IsFiniteMeasure (S k)]
    [∀ k, IsFiniteMeasure (T k)] [∀ k, IsFiniteMeasure (π k)]
    (hν₀ : ν 0 = 0) (hνn : ν n = 0)
    (hπ₁ : ∀ k < n, (π k).fst = ν k + S k)
    (hπ₂ : ∀ k < n, (π k).snd = ν (k + 1) + T k)
    (hcolours : ∀ k < n, S k = 0 ∨ T k = 0) :
    ∃ Γ : Measure ((ℕ × E) × (ℕ × E)), IsFiniteMeasure Γ ∧
      Vlasov.IsCoupling Γ (finiteStageLabelledPrefix S n) (finiteStageLabelledPrefix T n) ∧
      ∀ᵐ z ∂Γ, z.1.1 < z.2.1 := by
  obtain ⟨Γ, hΓfin, hΓ, horder⟩ :=
    exists_finiteOrderedClasswiseCoupling ν S T π n hν₀ hνn hπ₁ hπ₂
  have hsource : ∀ᵐ z ∂Γ, z.1.1 < n := by
    have h : ∀ᵐ a ∂Γ.fst, a.1 < n := by
      rw [Measure.fst, hΓ.1]
      exact finiteStageLabelledPrefix_ae_lt S n
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have havoid : ∀ k, ∀ᵐ z ∂Γ, z.1.1 ≠ k ∨ z.2.1 ≠ k := by
    intro k
    by_cases hkn : k < n
    · rcases hcolours k hkn with hS | hT
      · have h : ∀ᵐ a ∂Γ.fst, a.1 ≠ k := by
          rw [Measure.fst, hΓ.1]
          exact finiteStageLabelledPrefix_ae_ne_of_zero S n k hS
        exact (ae_of_ae_map measurable_fst.aemeasurable h).mono fun _ hz ↦ Or.inl hz
      · have h : ∀ᵐ a ∂Γ.snd, a.1 ≠ k := by
          rw [Measure.snd, hΓ.2]
          exact finiteStageLabelledPrefix_ae_ne_of_zero T n k hT
        exact (ae_of_ae_map measurable_snd.aemeasurable h).mono fun _ hz ↦ Or.inr hz
    · exact hsource.mono fun _ hz ↦ Or.inl (Nat.ne_of_lt (lt_of_lt_of_le hz (Nat.le_of_not_gt hkn)))
  have hall : ∀ᵐ z ∂Γ, ∀ k, z.1.1 ≠ k ∨ z.2.1 ≠ k := ae_all_iff.mpr havoid
  refine ⟨Γ, hΓfin, hΓ, ?_⟩
  filter_upwards [horder, hall] with z hz hall
  apply Nat.lt_of_le_of_ne hz
  intro heq
  rcases hall z.1.1 with hs | ht
  · exact hs rfl
  · exact ht heq.symm

end OTSelector.Reconstruction

end
end
