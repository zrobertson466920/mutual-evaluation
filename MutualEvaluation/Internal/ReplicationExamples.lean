import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ReplicationEquilibrium
import MutualEvaluation.Internal.PearsonTargetExamples
import MutualEvaluation.Internal.ShannonTargetExamples

/-!
INTERNAL — the supplied nuisance example for the actual replication scores.

The fair prior, worker returning (X,U), and three critics are reused, not
redefined. Equality with the target scores was proved from the original
integrals, not assumed. These results concern expected payment and equilibrium,
not sampling cost, variance, uniqueness, or within-loop adaptive reporting.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication.Example
open Binary


variable [MeasurableSpace (Bool × Bool)]
  [MeasurableSingletonClass (Bool × Bool)]

theorem chiSquared_value_at_truth : rp_Replication_V_chiSquared rp_Self_fair rp_Self_Nuisance_worker = 1 :=
  (V_chiSquared_eq_target rp_Self_fair rp_Self_Nuisance_worker).trans PearsonTarget.Example.value_at_truth

theorem kl_value_at_truth : rp_Replication_V_KL rp_Self_fair rp_Self_Nuisance_worker = Real.log 2 :=
  (V_KL_eq_target rp_Self_fair rp_Self_Nuisance_worker).trans ShannonTarget.Example.value_at_truth

/-- Literal agreement and nuisance removal both retain Pearson payoff 1;
the constant annotation receives zero. These are actual loop expectations. -/
theorem chiSquared_payoff_table_impl :
    rp_Replication_u_chiSquared rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker = 1 ∧
      rp_Replication_u_chiSquared rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker = 1 ∧
      rp_Replication_u_chiSquared rp_Self_Nuisance_constant rp_Self_fair rp_Self_Nuisance_worker = 0 := by
  have h := PearsonTarget.Example.payoff_table
  exact ⟨(u_chiSquared_eq_target rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker).trans h.1,
    (u_chiSquared_eq_target rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker).trans h.2.1,
    (u_chiSquared_eq_target rp_Self_Nuisance_constant rp_Self_fair rp_Self_Nuisance_worker).trans h.2.2⟩

/-- The harmonic loop retains log 2 nats for literal and task-only annotation,
and zero for the constant annotation. -/
theorem kl_payoff_table_impl :
    rp_Replication_u_KL rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker = Real.log 2 ∧
      rp_Replication_u_KL rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker = Real.log 2 ∧
      rp_Replication_u_KL rp_Self_Nuisance_constant rp_Self_fair rp_Self_Nuisance_worker = 0 := by
  have h := ShannonTarget.Example.payoff_table
  exact ⟨(u_KL_eq_target rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker).trans h.1,
    (u_KL_eq_target rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker).trans h.2.1,
    (u_KL_eq_target rp_Self_Nuisance_constant rp_Self_fair rp_Self_Nuisance_worker).trans h.2.2⟩

theorem chiSquared_regret_table_impl :
    rp_Replication_r_chiSquared rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker = 0 ∧
      rp_Replication_r_chiSquared rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker = 0 ∧
      rp_Replication_r_chiSquared rp_Self_Nuisance_constant rp_Self_fair rp_Self_Nuisance_worker = 1 := by
  have h := PearsonTarget.Example.regret_table
  exact ⟨(r_chiSquared_eq_target rp_Self_fair rp_Self_Nuisance_worker rp_Self_Nuisance_literal).trans h.1,
    (r_chiSquared_eq_target rp_Self_fair rp_Self_Nuisance_worker rp_Self_Nuisance_task).trans h.2.1,
    (r_chiSquared_eq_target rp_Self_fair rp_Self_Nuisance_worker rp_Self_Nuisance_constant).trans h.2.2⟩

theorem kl_regret_table_impl :
    rp_Replication_r_KL rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker = 0 ∧
      rp_Replication_r_KL rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker = 0 ∧
      rp_Replication_r_KL rp_Self_Nuisance_constant rp_Self_fair rp_Self_Nuisance_worker = Real.log 2 := by
  have h := ShannonTarget.Example.regret_table
  exact ⟨(r_KL_eq_target rp_Self_fair rp_Self_Nuisance_worker rp_Self_Nuisance_literal).trans h.1,
    (r_KL_eq_target rp_Self_fair rp_Self_Nuisance_worker rp_Self_Nuisance_task).trans h.2.1,
    (r_KL_eq_target rp_Self_fair rp_Self_Nuisance_worker rp_Self_Nuisance_constant).trans h.2.2⟩

/-- Two different full critic tables attain the same actual Pearson envelope. -/
theorem chiSquared_truthful_optima :
    rp_Self_Nuisance_literal ≠ rp_Self_Nuisance_task ∧
      rp_Replication_u_chiSquared rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker = rp_Replication_V_chiSquared rp_Self_fair rp_Self_Nuisance_worker ∧
      rp_Replication_u_chiSquared rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker = rp_Replication_V_chiSquared rp_Self_fair rp_Self_Nuisance_worker := by
  have h := PearsonTarget.Example.truthful_optima
  exact ⟨h.1,
    (u_chiSquared_eq_target rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker).trans
      (h.2.1.trans (V_chiSquared_eq_target rp_Self_fair rp_Self_Nuisance_worker).symm),
    (u_chiSquared_eq_target rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker).trans
      (h.2.2.trans (V_chiSquared_eq_target rp_Self_fair rp_Self_Nuisance_worker).symm)⟩

theorem kl_truthful_optima :
    rp_Self_Nuisance_literal ≠ rp_Self_Nuisance_task ∧
      rp_Replication_u_KL rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker = rp_Replication_V_KL rp_Self_fair rp_Self_Nuisance_worker ∧
      rp_Replication_u_KL rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker = rp_Replication_V_KL rp_Self_fair rp_Self_Nuisance_worker := by
  have h := ShannonTarget.Example.truthful_optima
  exact ⟨h.1,
    (u_KL_eq_target rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker).trans
      (h.2.1.trans (V_KL_eq_target rp_Self_fair rp_Self_Nuisance_worker).symm),
    (u_KL_eq_target rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker).trans
      (h.2.2.trans (V_KL_eq_target rp_Self_fair rp_Self_Nuisance_worker).symm)⟩

/-- Both critics support truthful single-worker equilibrium under both
payments. The worker's deviation is a fixed kernel chosen before sampling. -/
theorem truthful_equilibria :
    rp_Replication_reportingNash ((rp_Replication_pearsonScore (Bool) (Bool × Bool)))
      rp_Self_fair rp_Self_Nuisance_worker PMF.pure rp_Self_Nuisance_literal ∧
    rp_Replication_reportingNash ((rp_Replication_pearsonScore (Bool) (Bool × Bool)))
      rp_Self_fair rp_Self_Nuisance_worker PMF.pure rp_Self_Nuisance_task ∧
    rp_Replication_reportingNash ((rp_Replication_klScore (Bool) (Bool × Bool)))
      rp_Self_fair rp_Self_Nuisance_worker PMF.pure rp_Self_Nuisance_literal ∧
    rp_Replication_reportingNash ((rp_Replication_klScore (Bool) (Bool × Bool)))
      rp_Self_fair rp_Self_Nuisance_worker PMF.pure rp_Self_Nuisance_task :=
  ⟨MutualEvaluation.Replication.chiSquared_truthful_nash_impl rp_Self_fair rp_Self_Nuisance_worker rp_Self_Nuisance_literal chiSquared_truthful_optima.2.1,
    MutualEvaluation.Replication.chiSquared_truthful_nash_impl rp_Self_fair rp_Self_Nuisance_worker rp_Self_Nuisance_task chiSquared_truthful_optima.2.2,
    MutualEvaluation.Replication.kl_truthful_nash_impl rp_Self_fair rp_Self_Nuisance_worker rp_Self_Nuisance_literal kl_truthful_optima.2.1,
    MutualEvaluation.Replication.kl_truthful_nash_impl rp_Self_fair rp_Self_Nuisance_worker rp_Self_Nuisance_task kl_truthful_optima.2.2⟩

/-- Bijective annotations only relabel the report and have zero loop regret. -/
theorem chiSquared_bijective_annotation_impl {B : Type} [Fintype B]
    (g : Bool × Bool → B) (hg : Function.Bijective g) :
    rp_Replication_u_chiSquared (rp_Binary_annotate g) rp_Self_fair rp_Self_Nuisance_worker = 1 ∧
      rp_Replication_r_chiSquared (rp_Binary_annotate g) rp_Self_fair rp_Self_Nuisance_worker = 0 := by
  have h := PearsonTarget.Example.bijective_annotation g hg
  exact ⟨(u_chiSquared_eq_target (rp_Binary_annotate g) rp_Self_fair rp_Self_Nuisance_worker).trans h.1,
    (r_chiSquared_eq_target rp_Self_fair rp_Self_Nuisance_worker (rp_Binary_annotate g)).trans h.2⟩

theorem kl_bijective_annotation_impl {B : Type} [Fintype B]
    (g : Bool × Bool → B) (hg : Function.Bijective g) :
    rp_Replication_u_KL (rp_Binary_annotate g) rp_Self_fair rp_Self_Nuisance_worker = Real.log 2 ∧
      rp_Replication_r_KL (rp_Binary_annotate g) rp_Self_fair rp_Self_Nuisance_worker = 0 := by
  have h := ShannonTarget.Example.bijective_annotation g hg
  exact ⟨(u_KL_eq_target (rp_Binary_annotate g) rp_Self_fair rp_Self_Nuisance_worker).trans h.1,
    (r_KL_eq_target rp_Self_fair rp_Self_Nuisance_worker (rp_Binary_annotate g)).trans h.2⟩

end MutualEvaluation.Replication.Example
end