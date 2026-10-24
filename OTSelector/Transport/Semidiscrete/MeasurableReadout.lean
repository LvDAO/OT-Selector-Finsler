import Mathlib.Probability.Kernel.CondDistrib
import OTSelector.Probability.Dirichlet.CavityExchangeability
import OTSelector.Probability.Dirichlet.CavityLaw
import OTSelector.Probability.Dirichlet.CavitySuccess
import OTSelector.Probability.DirichletReference
import OTSelector.Transport.Semidiscrete.CavityCells
import OTSelector.Transport.Semidiscrete.Cells
import OTSelector.Transport.Semidiscrete.MeanPlan
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteFactor.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteFactor`; the selected original proof blocks follow. -/
section

/-!
Conditions: A finite measure on a standard-Borel source and measurable readouts constant on fibers; cavity specialization also uses its actual iid no-tie, integrability and distribution-free mass-vector law.

Objects: An almost-everywhere measurable factor readout, measurability of the cavity mean and a Dirichlet-mass readout.

Proof detail: Disintegrate or use a measurable inverse representative on almost every mass fiber, apply fiber constancy and then push the exact cavity mass law through that readout.

Sources: D. H. Fremlin, Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31 (https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30); D. H. Fremlin, 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary (https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19); Project manuscript, Section “Exact iid cavity disintegration”, Theorem thm:iid-cavity-dirichlet and Proposition prop:iid-cavity-mean, equation eq:iid-cavity-mean-plan (main.tex).
Relation: Doob–Dynkin/disintegration-style factor construction plus the project cavity law. The latter is main.tex thm:iid-cavity-dirichlet and prop:iid-cavity-mean; classical disintegration alone does not prove it.
-/

/-!
# Measurable semidiscrete readouts indexed by actual cavity masses

Regular conditional distributions supply a measurable readout on mass vectors. Actual
calibration shows that every environment in a fiber has the same readout; consequently
the conditional average equals that common value, and almost every mass has an actual
cavity representative. No measurable optimizer is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal MeasureTheory ProbabilityTheory

noncomputable section
namespace OTSelector.Probability

variable {W B : Type*} [MeasurableSpace W] [MeasurableSpace B]

/-- Conditioning on a measurable statistic yields a measurable version of every
fiber-constant real readout, with an actual representative on almost every fiber. -/
theorem exists_measurable_readout_of_fiber_constancy
    [StandardBorelSpace W] [Nonempty W] [MeasurableEq B]
    (P : Measure W) [IsFiniteMeasure P]
    (f : W → B) (hf : Measurable f) (g : W → ℝ) (hg : Measurable g)
    (hconst : ∀ w v, f w = f v → g w = g v) :
    ∃ G : B → ℝ, Measurable G ∧
      (∀ᵐ b ∂P.map f, ∃ w, f w = b ∧ G b = g w) ∧
      g =ᵐ[P] (G ∘ f) := by
  let κ := condDistrib (id : W → W) f P
  let G : B → ℝ := fun b ↦ ∫ w, g w ∂κ b
  have hG : Measurable G :=
    ((hg.comp measurable_snd).stronglyMeasurable.integral_condDistrib).measurable
  have hsupp : ∀ᵐ b ∂P.map f, ∀ᵐ w ∂κ b, f w = b := by
    apply Measure.ae_ae_of_ae_compProd (μ := P.map f) (κ := κ)
      (p := fun q : B × W ↦ f q.2 = q.1)
    change ∀ᵐ q ∂((P.map f) ⊗ₘ condDistrib id f P), f q.2 = q.1
    rw [compProd_map_condDistrib aemeasurable_id]
    apply (ae_map_iff (hf.prodMk measurable_id).aemeasurable
      (measurableSet_eq_fun (hf.comp measurable_snd) measurable_fst)).mpr
    exact Eventually.of_forall fun _ ↦ rfl
  have hrep : ∀ᵐ b ∂P.map f, ∃ w, f w = b ∧ G b = g w := by
    filter_upwards [hsupp] with b hb
    obtain ⟨w, hw⟩ := hb.exists
    refine ⟨w, hw, ?_⟩
    change (∫ v, g v ∂κ b) = g w
    calc
      _ = ∫ _v, g w ∂κ b := integral_congr_ae (hb.mono fun v hv ↦ hconst v w (hv.trans hw.symm))
      _ = _ := by simp
  refine ⟨G, hG, hrep, ?_⟩
  filter_upwards [ae_of_ae_map hf.aemeasurable hrep] with w hw
  obtain ⟨v, hv, hGv⟩ := hw
  exact (hconst w v hv.symm).trans hGv.symm

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- Measurable endpoint tests have measurable actual cavity mean readouts. -/
theorem measurable_cavityMeanReadout
    (μ : Measure S) [SFinite μ]
    (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (row : W × S → Fin (m + 1) → ℝ)
    (hret : ∀ k j, Measurable (fun w ↦ retained w k j))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (m + 1))
    (g : W × S → Fin (m + 1) → ℝ) (hg : ∀ j, Measurable (fun z ↦ g z j)) :
    Measurable (cavityMeanReadout μ retained row i g) := by
  classical
  have hm j := measurableSet_cavityCell retained row hret hrow i j
  have hf j : Measurable ((cavityCell retained row i j).indicator (fun z ↦ g z j)) :=
    (hg j).indicator (hm j)
  have heq : cavityMeanReadout μ retained row i g = fun w ↦
      ∑ j, ∫ s, (cavityCell retained row i j).indicator (fun z ↦ g z j) (w, s) ∂μ := by
    funext w
    apply Finset.sum_congr rfl
    intro j _
    have hsec : MeasurableSet {s | (w, s) ∈ cavityCell retained row i j} :=
      (hm j).preimage measurable_prodMk_left
    rw [← integral_indicator (μ := μ) (f := fun s ↦ g (w, s) j) hsec]
    rfl
  rw [heq]
  exact Finset.measurable_sum _ fun j _ ↦ (hf j).stronglyMeasurable.integral_prod_right'.measurable

/-- Every integrable paired-test cavity readout admits a measurable version on Dirichlet
weights. Almost every weight is represented by an actual, uniquely calibrated allocation. -/
theorem exists_dirichlet_cavity_readout
    [StandardBorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hci : ∀ j, Integrable (c j) μ)
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (g : S → Fin (m + 1) → ℝ)
    (hgm : ∀ j, Measurable (fun s ↦ g s j)) (hgi : ∀ j, Integrable (fun s ↦ g s j) μ) :
    ∃ G : (Fin (m + 1) → ℝ) → ℝ, Measurable G ∧
      (∀ᵐ p ∂dirichletOne m, ∃ w : Fin m → S, iidCavityMassVector μ c w = p ∧
        G p = cavityMeanReadout μ (iidCapacityInputCost c (fun k w ↦ w k))
          (fun z j ↦ c j z.2) 0 (fun z ↦ g z.2) w) ∧
      (fun w ↦ cavityMeanReadout μ (iidCapacityInputCost c (fun k w ↦ w k))
        (fun z j ↦ c j z.2) 0 (fun z ↦ g z.2) w) =ᵐ[Measure.pi (fun _ : Fin m ↦ μ)]
          (G ∘ iidCavityMassVector μ c) := by
  let : Nonempty S := nonempty_of_isProbabilityMeasure μ
  let retained := iidCapacityInputCost c (fun (k : Fin m) (w : Fin m → S) ↦ w k)
  let row : (Fin m → S) × S → Fin (m + 1) → ℝ := fun z j ↦ c j z.2
  have hret := measurable_iidCavityRetained c hc
  have hrow j : Measurable (fun z ↦ row z j) := (hc j).comp measurable_snd
  have hconst (w v : Fin m → S) (hp : iidCavityMassVector μ c w = iidCavityMassVector μ c v) :
      cavityMeanReadout μ retained row 0 (fun z ↦ g z.2) w =
        cavityMeanReadout μ retained row 0 (fun z ↦ g z.2) v := by
    apply cavityMeanReadout_eq_of_same_masses μ retained hret (fun s j ↦ c j s)
      hc hci hatom 0 w v ?_ g hgi
    intro j
    have hj := congrArg (fun p ↦ ENNReal.ofReal (p j)) hp
    simpa only [ofReal_iidCavityMassVector] using hj
  obtain ⟨G, hG, hrep, hfactor⟩ := exists_measurable_readout_of_fiber_constancy
    (Measure.pi (fun _ : Fin m ↦ μ)) (iidCavityMassVector μ c)
    (measurable_iidCavityMassVector μ c hc)
    (cavityMeanReadout μ retained row 0 (fun z ↦ g z.2))
    (measurable_cavityMeanReadout μ retained row hret hrow 0 _
      (fun j ↦ (hgm j).comp measurable_snd)) hconst
  rw [map_iidCavityMassVector_eq_dirichletOne μ c hc hatom] at hrep
  exact ⟨G, hG, hrep, hfactor⟩

end OTSelector.Probability

end
end
