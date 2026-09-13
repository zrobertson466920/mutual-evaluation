import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ReplicationConsequences

/-!
INTERNAL — single-worker equilibrium for channel-parameterized scores.

The worker selects one reporting kernel before the experiment; the critic
selects one rule. Both receive the same expected score. This interface uses
Score directly and does not identify the replication experiment with Core's
two-worker Game or assert its robustness condition.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open Binary

/- Nash inequalities for one worker and one critic with a common score.
A worker deviation replaces the entire fixed reporting kernel, not one call
or a history-dependent part of the replication experiment. -/


variable {X R : Type} [Fintype X] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
variable (P : PMF X) (w : Kernel X R)

/-- Truth and any truthful-channel optimizer form a Nash equilibrium for
the original collision-gated payment. Truth is the point-mass kernel. -/
theorem chiSquared_truthful_nash_impl (c : Critic R)
    (hc : rp_Replication_u_chiSquared c P w = rp_Replication_V_chiSquared P w) :
    rp_Replication_reportingNash ((rp_Replication_pearsonScore (X) (R))) P w PMF.pure c := by
  dsimp only
  simpa only [ PMF.bind_pure] using
    chiSquared_truthful_best_responses P w c hc

/-- The same equilibrium conclusion for the original harmonic payment.
The score remains channel-parameterized throughout. -/
theorem kl_truthful_nash_impl (c : Critic R)
    (hc : rp_Replication_u_KL c P w = rp_Replication_V_KL P w) :
    rp_Replication_reportingNash ((rp_Replication_klScore (X) (R))) P w PMF.pure c := by
  dsimp only
  simpa only [ PMF.bind_pure] using
    kl_truthful_best_responses P w c hc

/-- Literal agreement supplies an equilibrium for both actual loop scores.
This asserts existence, not uniqueness or semantic correctness. -/
theorem literal_truthful_equilibria :
    rp_Replication_reportingNash ((rp_Replication_pearsonScore (X) (R))) P w PMF.pure (rp_Binary_annotate id) ∧
      rp_Replication_reportingNash ((rp_Replication_klScore (X) (R))) P w PMF.pure (rp_Binary_annotate id) :=
  ⟨MutualEvaluation.Replication.chiSquared_truthful_nash_impl P w _ (MutualEvaluation.Replication.chiSquared_literal_optimal_impl P w),
    MutualEvaluation.Replication.kl_truthful_nash_impl P w _ (MutualEvaluation.Replication.kl_literal_optimal_impl P w)⟩

end MutualEvaluation.Replication
end