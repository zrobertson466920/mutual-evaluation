import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ReplicationInformation

/-!
INTERNAL — consequences for the actual replication scores.

The equalities used below were proved from the original stream experiment,
including integrability and the invalid-critic branch. They are not hypotheses
or replacements for the loop integrals.

These are channel-level conclusions for one fixed reporting kernel per
experiment. They do not assert Core.robustness, uniqueness, semantic correctness,
or protection against within-loop adaptive reporting.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open Binary Probability FiniteTask

variable {X R : Type} [Fintype X] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
variable (P : PMF X) (k : Kernel X R)

/-- Transfer over the full critic space, including invalid critics. -/
theorem V_chiSquared_eq_target :
    rp_Replication_V_chiSquared P k = PearsonTarget.value P k := by
  change sSup (Set.range fun c : Critic R => rp_Replication_u_chiSquared c P k) =
    sSup (Set.range fun c : Critic R => PearsonTarget.payoff c P k)
  simp_rw [u_chiSquared_eq_target]

theorem V_KL_eq_target :
    rp_Replication_V_KL P k = ShannonTarget.value P k := by
  change sSup (Set.range fun c : Critic R => rp_Replication_u_KL c P k) =
    sSup (Set.range fun c : Critic R => ShannonTarget.payoff c P k)
  simp_rw [u_KL_eq_target]

theorem r_chiSquared_eq_target (c : Critic R) :
    rp_Replication_r_chiSquared c P k = PearsonTarget.regret c P k := by
  exact congrArg₂ (fun a b : ℝ => a - b)
    (V_chiSquared_eq_target P k) (u_chiSquared_eq_target c P k)

theorem r_KL_eq_target (c : Critic R) :
    rp_Replication_r_KL c P k = ShannonTarget.regret c P k := by
  exact congrArg₂ (fun a b : ℝ => a - b)
    (V_KL_eq_target P k) (u_KL_eq_target c P k)

/-- The actual Pearson loop envelope is full task/report information. -/
theorem V_chiSquared_eq_impl : rp_Replication_V_chiSquared P k = rp_FiniteTask_pearson P k :=
  (V_chiSquared_eq_target P k).trans (PearsonTarget.value_eq P k)

/-- The actual harmonic loop envelope is Shannon information in nats. -/
theorem V_KL_eq_impl : rp_Replication_V_KL P k = rp_FiniteTask_shannon P k :=
  (V_KL_eq_target P k).trans (ShannonTarget.value_eq P k)

theorem u_chiSquared_literal :
    rp_Replication_u_chiSquared (rp_Binary_annotate id) P k = rp_FiniteTask_pearson P k :=
  (u_chiSquared_eq_target _ P k).trans (PearsonTarget.literal_payoff P k)

theorem u_KL_literal :
    rp_Replication_u_KL (rp_Binary_annotate id) P k = rp_FiniteTask_shannon P k :=
  (u_KL_eq_target _ P k).trans (ShannonTarget.literal_payoff P k)

theorem chiSquared_literal_optimal_impl :
    rp_Replication_u_chiSquared (rp_Binary_annotate id) P k = rp_Replication_V_chiSquared P k :=
  (u_chiSquared_literal P k).trans (MutualEvaluation.Replication.V_chiSquared_eq_impl P k).symm

theorem kl_literal_optimal_impl :
    rp_Replication_u_KL (rp_Binary_annotate id) P k = rp_Replication_V_KL P k :=
  (u_KL_literal P k).trans (MutualEvaluation.Replication.V_KL_eq_impl P k).symm

theorem u_chiSquared_nonneg (c : Critic R) : 0 ≤ rp_Replication_u_chiSquared c P k := by
  rw [u_chiSquared_eq_target]
  exact PearsonTarget.payoff_nonneg P k c

theorem u_KL_nonneg (c : Critic R) : 0 ≤ rp_Replication_u_KL c P k := by
  rw [u_KL_eq_target]
  exact ShannonTarget.payoff_nonneg P k c

theorem u_chiSquared_le_value_impl (c : Critic R) :
    rp_Replication_u_chiSquared c P k ≤ rp_Replication_V_chiSquared P k := by
  rw [u_chiSquared_eq_target, MutualEvaluation.Replication.V_chiSquared_eq_impl]
  exact PearsonTarget.payoff_le_information P k c

theorem u_KL_le_value_impl (c : Critic R) :
    rp_Replication_u_KL c P k ≤ rp_Replication_V_KL P k := by
  rw [u_KL_eq_target, MutualEvaluation.Replication.V_KL_eq_impl]
  exact ShannonTarget.payoff_le_information P k c

theorem r_chiSquared_nonneg (c : Critic R) : 0 ≤ rp_Replication_r_chiSquared c P k := by
  rw [r_chiSquared_eq_target]
  exact PearsonTarget.regret_nonneg P k c

theorem r_KL_nonneg (c : Critic R) : 0 ≤ rp_Replication_r_KL c P k := by
  rw [r_KL_eq_target]
  exact ShannonTarget.regret_nonneg P k c

omit [Fintype R] [MeasurableSingletonClass R] in
theorem r_chiSquared_zero_iff (c : Critic R) :
    rp_Replication_r_chiSquared c P k = 0 ↔ rp_Replication_u_chiSquared c P k = rp_Replication_V_chiSquared P k := by
  rw [ sub_eq_zero, eq_comm]

omit [Fintype R] [MeasurableSingletonClass R] in
theorem r_KL_zero_iff (c : Critic R) :
    rp_Replication_r_KL c P k = 0 ↔ rp_Replication_u_KL c P k = rp_Replication_V_KL P k := by
  rw [ sub_eq_zero, eq_comm]

/-- Posterior squared loss is the regret of the actual collision payment.
Real division makes null prior coordinates contribute zero. -/
theorem r_chiSquared_annotation_impl {B : Type} [Fintype B] (g : R → B) :
    rp_Replication_r_chiSquared (rp_Binary_annotate g) P k =
      ∑ x, (∑ a, rp_FiniteTask_reportMass P k a *
        (rp_FiniteTask_posterior P k a x - rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) x)^2) /
          mass P x := by
  rw [r_chiSquared_eq_target]
  exact PearsonTarget.annotation_regret P k g

/-- Conditional information is the regret of the actual harmonic payment. -/
theorem r_KL_annotation_impl {B : Type} [Fintype B] (g : R → B) :
    rp_Replication_r_KL (rp_Binary_annotate g) P k = rp_FiniteTask_conditionalInformation P k g := by
  rw [r_KL_eq_target]
  exact ShannonTarget.annotation_regret P k g

/-- Sufficiency concerns positive-mass reports, not global critic validity. -/
theorem chiSquared_annotation_zero_iff_impl {B : Type} [Fintype B] (g : R → B) :
    rp_Replication_r_chiSquared (rp_Binary_annotate g) P k = 0 ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a = rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) := by
  rw [r_chiSquared_eq_target]
  exact PearsonTarget.annotation_zero_iff P k g

theorem kl_annotation_zero_iff_impl {B : Type} [Fintype B] (g : R → B) :
    rp_Replication_r_KL (rp_Binary_annotate g) P k = 0 ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a = rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) := by
  rw [r_KL_eq_target]
  exact ShannonTarget.annotation_zero_iff P k g

theorem chiSquared_annotation_optimal_iff {B : Type} [Fintype B] (g : R → B) :
    rp_Replication_u_chiSquared (rp_Binary_annotate g) P k = rp_Replication_V_chiSquared P k ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a = rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) :=
  (r_chiSquared_zero_iff P k (rp_Binary_annotate g)).symm.trans
    (MutualEvaluation.Replication.chiSquared_annotation_zero_iff_impl P k g)

theorem kl_annotation_optimal_iff {B : Type} [Fintype B] (g : R → B) :
    rp_Replication_u_KL (rp_Binary_annotate g) P k = rp_Replication_V_KL P k ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a = rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) :=
  (r_KL_zero_iff P k (rp_Binary_annotate g)).symm.trans (MutualEvaluation.Replication.kl_annotation_zero_iff_impl P k g)

theorem chiSquared_critic_coarsening_impl {B C : Type} [Fintype B] [Fintype C]
    (g : R → B) (h : B → C) :
    rp_Replication_u_chiSquared (rp_Binary_annotate (h ∘ g)) P k ≤ rp_Replication_u_chiSquared (rp_Binary_annotate g) P k := by
  exact (u_chiSquared_eq_target (rp_Binary_annotate (h ∘ g)) P k).trans_le
    ((PearsonTarget.critic_coarsening P k g h).trans_eq
      (u_chiSquared_eq_target (rp_Binary_annotate g) P k).symm)

theorem kl_critic_coarsening_impl {B C : Type} [Fintype B] [Fintype C]
    (g : R → B) (h : B → C) :
    rp_Replication_u_KL (rp_Binary_annotate (h ∘ g)) P k ≤ rp_Replication_u_KL (rp_Binary_annotate g) P k := by
  exact (u_KL_eq_target (rp_Binary_annotate (h ∘ g)) P k).trans_le
    ((ShannonTarget.critic_coarsening P k g h).trans_eq
      (u_KL_eq_target (rp_Binary_annotate g) P k).symm)

theorem V_chiSquared_data_processing_impl {B : Type} [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B] (τ : Kernel R B) :
    rp_Replication_V_chiSquared P (fun x => (k x).bind τ) ≤ rp_Replication_V_chiSquared P k := by
  rw [MutualEvaluation.Replication.V_chiSquared_eq_impl, MutualEvaluation.Replication.V_chiSquared_eq_impl]
  exact pearson_data_processing P k τ

theorem V_KL_data_processing_impl {B : Type} [Fintype B]
    [MeasurableSpace B] [MeasurableSingletonClass B] (τ : Kernel R B) :
    rp_Replication_V_KL P (fun x => (k x).bind τ) ≤ rp_Replication_V_KL P k := by
  rw [MutualEvaluation.Replication.V_KL_eq_impl, MutualEvaluation.Replication.V_KL_eq_impl]
  exact shannon_data_processing P k τ

/-- Any truthful-channel optimizer bounds every simultaneous change of critic
and fixed reporting kernel, for the original Pearson loop score. -/
theorem chiSquared_truthful_global_optimal_impl (c : Critic R)
    (hc : rp_Replication_u_chiSquared c P k = rp_Replication_V_chiSquared P k)
    (d : Critic R) (σ : Kernel R R) :
    rp_Replication_u_chiSquared d P (fun x => (k x).bind σ) ≤ rp_Replication_u_chiSquared c P k := by
  rw [u_chiSquared_eq_target, V_chiSquared_eq_target] at hc
  simpa only [u_chiSquared_eq_target] using
    PearsonTarget.truthful_global_optimal P k c hc d σ

theorem kl_truthful_global_optimal_impl (c : Critic R)
    (hc : rp_Replication_u_KL c P k = rp_Replication_V_KL P k)
    (d : Critic R) (σ : Kernel R R) :
    rp_Replication_u_KL d P (fun x => (k x).bind σ) ≤ rp_Replication_u_KL c P k := by
  rw [u_KL_eq_target, V_KL_eq_target] at hc
  simpa only [u_KL_eq_target] using
    ShannonTarget.truthful_global_optimal P k c hc d σ

/-- Both unilateral best-response inequalities for one worker and one critic.
Worker deviations select a reporting kernel before sampling begins. -/
theorem chiSquared_truthful_best_responses (c : Critic R)
    (hc : rp_Replication_u_chiSquared c P k = rp_Replication_V_chiSquared P k) :
    (∀ d, rp_Replication_u_chiSquared d P k ≤ rp_Replication_u_chiSquared c P k) ∧
      ∀ σ : Kernel R R,
        rp_Replication_u_chiSquared c P (fun x => (k x).bind σ) ≤ rp_Replication_u_chiSquared c P k := by
  rw [u_chiSquared_eq_target, V_chiSquared_eq_target] at hc
  simpa only [u_chiSquared_eq_target] using
    PearsonTarget.truthful_best_responses P k c hc

theorem kl_truthful_best_responses (c : Critic R)
    (hc : rp_Replication_u_KL c P k = rp_Replication_V_KL P k) :
    (∀ d, rp_Replication_u_KL d P k ≤ rp_Replication_u_KL c P k) ∧
      ∀ σ : Kernel R R, rp_Replication_u_KL c P (fun x => (k x).bind σ) ≤ rp_Replication_u_KL c P k := by
  rw [u_KL_eq_target, V_KL_eq_target] at hc
  simpa only [u_KL_eq_target] using
    ShannonTarget.truthful_best_responses P k c hc

/-- Relabeling need only be injective; unused annotation labels do not matter. -/
theorem chiSquared_injective_annotation {B : Type} [Fintype B]
    (g : R → B) (hg : Function.Injective g) :
    rp_Replication_u_chiSquared (rp_Binary_annotate g) P k = rp_Replication_V_chiSquared P k ∧
      rp_Replication_r_chiSquared (rp_Binary_annotate g) P k = 0 := by
  have he : rp_Replication_u_chiSquared (rp_Binary_annotate g) P k = rp_Replication_V_chiSquared P k := by
    rw [MutualEvaluation.Replication.u_chiSquared_annotation_impl, MutualEvaluation.Replication.V_chiSquared_eq_impl]
    exact pearson_annotation_injective P k g hg
  exact ⟨he, (r_chiSquared_zero_iff P k (rp_Binary_annotate g)).2 he⟩

theorem kl_injective_annotation {B : Type} [Fintype B]
    (g : R → B) (hg : Function.Injective g) :
    rp_Replication_u_KL (rp_Binary_annotate g) P k = rp_Replication_V_KL P k ∧ rp_Replication_r_KL (rp_Binary_annotate g) P k = 0 := by
  have he : rp_Replication_u_KL (rp_Binary_annotate g) P k = rp_Replication_V_KL P k := by
    rw [MutualEvaluation.Replication.u_KL_annotation_impl, MutualEvaluation.Replication.V_KL_eq_impl]
    exact shannon_annotation_injective P k g hg
  exact ⟨he, (r_KL_zero_iff P k (rp_Binary_annotate g)).2 he⟩

end MutualEvaluation.Replication
end