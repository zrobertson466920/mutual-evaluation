import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.SelfEquilibrium

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-!
# Lossless nuisance removal versus information loss

The raw return is (X,U), with a fresh independent fair nuisance bit on each run.
Literal agreement and task-only annotation are distinct globally valid critics.
Both are optimal at truth; a constant annotation loses all task information.
These are fair-binary Pearson payoff results, not KL or sampling-cost results.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Self.Nuisance
open Probability Binary



def workers : Fin 2 → Kernel Bool (Bool × Bool) :=
  ![rp_Self_Nuisance_worker, fun x => PMF.pure (x, false)]

abbrev G : Game Bool (Bool × Bool) := game workers



def ρ : PMF (Outcome (Bool × Bool)) := law G truth

private theorem mass_worker (x : Bool) (a : Bool × Bool) :
    mass (rp_Self_Nuisance_worker x) a = if a.1 = x then (1 / 2 : ℝ) else 0 := by
  change mass ((rp_Self_fair).bind fun u => PMF.pure (x, u)) a = _
  rw [mass_bind]
  rcases a with ⟨a, u⟩
  cases x <;> cases a <;> cases u <;>
    norm_num [mass, PMF.uniformOfFintype_apply, PMF.pure_apply]

private theorem raw_mass (a : Bool × Bool) : reportMass rp_Self_Nuisance_worker a = 1 / 4 := by
  rcases a with ⟨x, u⟩
  cases x <;> norm_num [reportMass, mass_worker]

private theorem raw_posterior (a : Bool × Bool) :
    posterior rp_Self_Nuisance_worker a = if a.1 then 1 else 0 := by
  rcases a with ⟨x, u⟩
  cases x <;> norm_num [posterior, mass_worker]

private theorem information_one : information rp_Self_Nuisance_worker = 1 := by
  norm_num [information, raw_mass, raw_posterior, Fintype.sum_prod_type]

private theorem reported_truth : reported workers truth = rp_Self_Nuisance_worker := by
  funext x
  simp [reported, truth, workers, PMF.bind_pure]

theorem value_at_truth : V G ρ = 1 := by
  change V (game workers) (law (game workers) truth) = 1
  rw [value workers truth, reported_truth, information_one]

private theorem literal_optimal : G.u rp_Self_Nuisance_literal ρ = V G ρ := by
  change (game workers).u (rp_Binary_annotate id) (law (game workers) truth) =
    V (game workers) (law (game workers) truth)
  rw [literal_payoff workers truth, value workers truth]

private theorem task_optimal : G.u rp_Self_Nuisance_task ρ = V G ρ := by
  change (game workers).u rp_Self_Nuisance_task (law (game workers) truth) =
    V (game workers) (law (game workers) truth)
  apply (Self.optimal_iff workers truth rp_Self_Nuisance_task (MutualEvaluation.Binary.annotate_valid_impl Prod.fst)).2
  intro a b hab _ _
  have he : a.1 = b.1 := (annotate_rel Prod.fst a b).1 hab
  rw [reported_truth, raw_posterior, raw_posterior, he]

private theorem constant_zero : G.u rp_Self_Nuisance_constant ρ = 0 := by
  change (game workers).u (rp_Binary_annotate (fun _ : Bool × Bool => ()))
    (law (game workers) truth) = 0
  refine (payoff_valid workers
    (rp_Binary_annotate (fun _ : Bool × Bool => ()))
    (MutualEvaluation.Binary.annotate_valid_impl (fun _ : Bool × Bool => ()))
    (law (game workers) truth)).trans ?_
  rw [self_record workers truth, reported_truth]
  refine (annotation_score (fun _ : Bool × Bool => ())
    rp_Self_Nuisance_worker).trans ?_
  norm_num [_root_.MutualEvaluation.Fiber.push, _root_.MutualEvaluation.Fiber.mean,
    raw_mass, raw_posterior, Fintype.sum_prod_type]

theorem payoff_table :
    G.u rp_Self_Nuisance_literal ρ = 1 ∧ G.u rp_Self_Nuisance_task ρ = 1 ∧ G.u rp_Self_Nuisance_constant ρ = 0 :=
  ⟨literal_optimal.trans value_at_truth, task_optimal.trans value_at_truth, constant_zero⟩

theorem regret_table :
    Abstract.regret G rp_Self_Nuisance_literal ρ = 0 ∧ Abstract.regret G rp_Self_Nuisance_task ρ = 0 ∧
      Abstract.regret G rp_Self_Nuisance_constant ρ = 1 := by
  change V G ρ - G.u rp_Self_Nuisance_literal ρ = 0 ∧ V G ρ - G.u rp_Self_Nuisance_task ρ = 0 ∧
    V G ρ - G.u rp_Self_Nuisance_constant ρ = 1
  rw [value_at_truth, payoff_table.1, payoff_table.2.1, payoff_table.2.2]
  norm_num

/-- Equality of task information does not require equality of critic tables. -/
theorem distinct : rp_Self_Nuisance_task ≠ rp_Self_Nuisance_literal := by
  intro h
  have he := congrArg
    (fun c : Critic (Bool × Bool) => (c ((false, false), (false, true)) : ℝ)) h
  norm_num at he

theorem truthful_equilibria : nash G truth rp_Self_Nuisance_literal ∧ nash G truth rp_Self_Nuisance_task :=
  ⟨Self.truthful_nash workers rp_Self_Nuisance_literal literal_optimal,
    Self.truthful_nash workers rp_Self_Nuisance_task task_optimal⟩

end MutualEvaluation.Self.Nuisance
end