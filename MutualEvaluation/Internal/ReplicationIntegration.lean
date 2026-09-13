import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ReplicationHarmonic
import MutualEvaluation.Internal.ReplicationTermination
import MutualEvaluation.Internal.FiniteProbability

/-!
INTERNAL — integration support for the anchored-task replication law.

Finite anchor integration requires section integrability only at positive-mass
anchors. The finite task mixture similarly ignores null task atoms. These
lemmas do not assume payment integrability or an information-payoff identity.
No probability law or payment definition is replaced.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open MeasureTheory Probability
attribute [local instance] Classical.propDecidable

section Anchor
variable {R : Type} [MeasurableSpace R] [Fintype R]
  [MeasurableSingletonClass R]

theorem integrable_pmf_fintype (p : PMF R) (f : R → ℝ) :
    Integrable f p.toMeasure := by
  simp

theorem integral_pmf_fintype (p : PMF R) (f : R → ℝ) :
    (∫ a, f a ∂p.toMeasure) = ∑ a, mass p a * f a := by
  rw [integral_fintype (integrable_pmf_fintype p f)]
  apply Finset.sum_congr rfl
  intro a _
  rw [measureReal_def,
    p.toMeasure_apply_singleton a (measurableSet_singleton a)]
  rfl

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Only supported anchors need integrable sections. -/
theorem integrable_anchor_prod (p : PMF R) (ν : Measure Ω) [SFinite ν]
    (f : R × Ω → ℝ) (hf : Measurable f)
    (hi : ∀ a, 0 < p a → Integrable (fun ω => f (a, ω)) ν) :
    Integrable f (p.toMeasure.prod ν) := by
  apply (integrable_prod_iff hf.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_mass_pos p] with a ha
    exact hi a ha
  · exact integrable_pmf_fintype p _

theorem integral_anchor_prod (p : PMF R) (ν : Measure Ω) [SFinite ν]
    (f : R × Ω → ℝ) (hf : Measurable f)
    (hi : ∀ a, 0 < p a → Integrable (fun ω => f (a, ω)) ν) :
    (∫ t, f t ∂p.toMeasure.prod ν) =
      ∑ a, mass p a * ∫ ω, f (a, ω) ∂ν := by
  rw [integral_prod f (integrable_anchor_prod p ν f hf hi)]
  exact integral_pmf_fintype p _

end Anchor

section Task
variable {X R : Type} [MeasurableSpace R]

theorem integrable_task_component (P : PMF X) (k : Kernel X R)
    (f : rp_Replication_Transcript R → ℝ) (x : X)
    (hi : 0 < P x → Integrable f (rp_Replication_conditionalTranscriptLaw P k x)) :
    Integrable f (P x • rp_Replication_conditionalTranscriptLaw P k x) := by
  by_cases hx : P x = 0
  · simp only [hx, zero_smul]
    exact integrable_zero_measure
  · exact (hi (pos_iff_ne_zero.mpr hx)).smul_measure (P.apply_ne_top x)

/-- Integrability under the actual finite task mixture, including null tasks. -/
theorem integrable_transcriptLaw [Fintype X] (P : PMF X) (k : Kernel X R)
    (f : rp_Replication_Transcript R → ℝ)
    (hi : ∀ x, 0 < P x → Integrable f (rp_Replication_conditionalTranscriptLaw P k x)) :
    Integrable f (rp_Replication_transcriptLaw P k) := by
  dsimp only
  apply integrable_finsetSum_measure.mpr
  intro x _
  exact integrable_task_component P k f x (hi x)

theorem integral_transcriptLaw [Fintype X] (P : PMF X) (k : Kernel X R)
    (f : rp_Replication_Transcript R → ℝ)
    (hi : ∀ x, 0 < P x → Integrable f (rp_Replication_conditionalTranscriptLaw P k x)) :
    (∫ t, f t ∂rp_Replication_transcriptLaw P k) =
      ∑ x, mass P x * ∫ t, f t ∂rp_Replication_conditionalTranscriptLaw P k x := by
  rw [ integral_finsetSum_measure
    (fun x _ => integrable_task_component P k f x (hi x))]
  simp only [integral_smul_measure, smul_eq_mul, mass]

end Task

section Gate
variable {R : Type} [MeasurableSpace R]

/-- Probability of the actual first same-task comparison event. -/
theorem iid_initial_event (p : PMF R) (E : Set R) (hE : MeasurableSet E) :
    rp_Replication_iid p {ω | ω 0 ∈ E} = p.toMeasure E := by
  classical
  have he : {ω : ℕ → R | ω 0 ∈ E} =
      Set.pi (↑({0} : Finset ℕ) : Set ℕ) (fun _ => E) := by
    ext ω
    simp
  rw [he, iid_prefix p _ _ (fun _ _ => hE)]
  simp

theorem iid_gate_integrable (p : PMF R) (E : Set R) (hE : MeasurableSet E) :
    Integrable (fun ω : ℕ → R => if ω 0 ∈ E then (1 : ℝ) else 0) (rp_Replication_iid p) := by
  have hm : MeasurableSet {ω : ℕ → R | ω 0 ∈ E} :=
    hE.preimage (measurable_pi_apply 0)
  have hg : Measurable (fun ω : ℕ → R =>
      if ω 0 ∈ E then (1 : ℝ) else 0) :=
    Measurable.ite hm measurable_const measurable_const
  apply (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
  filter_upwards [] with ω
  split_ifs <;> norm_num

theorem iid_gate_integral (p : PMF R) (E : Set R) (hE : MeasurableSet E) :
    (∫ ω : ℕ → R, if ω 0 ∈ E then (1 : ℝ) else 0 ∂rp_Replication_iid p) =
      (p.toMeasure E).toReal := by
  have hm : MeasurableSet {ω : ℕ → R | ω 0 ∈ E} :=
    hE.preimage (measurable_pi_apply 0)
  calc
    _ = (rp_Replication_iid p).real {ω | ω 0 ∈ E} := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] using
        (integral_indicator_one (μ := rp_Replication_iid p) hm)
    _ = (p.toMeasure E).toReal := by
      rw [measureReal_def, iid_initial_event p E hE]

end Gate
end MutualEvaluation.Replication
end