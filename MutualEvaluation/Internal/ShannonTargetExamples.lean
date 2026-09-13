import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ShannonTarget
import MutualEvaluation.Internal.SelfNuisance

/-!
INTERNAL / DRAFT — the supplied nuisance example for the Shannon target.
The worker and critics are reused from Self.Nuisance, not redefined.
These conclusions concern finite-information targets, not the harmonic loop's
expected payment, runtime, variance, or adaptive reporting strategies.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.ShannonTarget.Example
open Probability Binary FiniteTask


private theorem mass_fair (x : Bool) : mass rp_Self_fair x = 1 / 2 := by
  norm_num [mass, PMF.uniformOfFintype_apply]

private theorem mass_worker (x : Bool) (a : Bool × Bool) :
    mass (rp_Self_Nuisance_worker x) a = if a.1 = x then (1 / 2 : ℝ) else 0 := by
  change mass ((rp_Self_fair).bind fun u => PMF.pure (x, u)) a = _
  rw [mass_bind]
  rcases a with ⟨a, u⟩
  cases x <;> cases a <;> cases u <;>
    norm_num [mass, PMF.uniformOfFintype_apply, PMF.pure_apply]

private theorem raw_mass (a : Bool × Bool) :
    rp_FiniteTask_reportMass rp_Self_fair rp_Self_Nuisance_worker a = 1 / 4 := by
  rw [reportMass_eq_sum]
  rcases a with ⟨x, u⟩
  cases x <;> norm_num [mass_fair, mass_worker]

theorem information_log_two : rp_FiniteTask_shannon rp_Self_fair rp_Self_Nuisance_worker = Real.log 2 := by
  norm_num [raw_mass, mass_fair, mass_worker,
    Fintype.sum_prod_type]
  ring

private theorem task_channel :
    rp_FiniteTask_annotated rp_Self_Nuisance_worker Prod.fst = (PMF.pure : Kernel Bool Bool) := by
  funext x
  simp only [ PMF.map, Function.comp_def, PMF.bind_bind,
    PMF.pure_bind, PMF.bind_const]

private theorem task_information :
    rp_FiniteTask_shannon rp_Self_fair (PMF.pure : Kernel Bool Bool) = Real.log 2 := by
  have hm (a : Bool) :
      rp_FiniteTask_reportMass rp_Self_fair (PMF.pure : Kernel Bool Bool) a = 1 / 2 := by
    change mass ((rp_Self_fair).bind PMF.pure) a = _
    rw [PMF.bind_pure, mass_fair]
  norm_num [hm, mass_fair, mass_pure]
  ring

private theorem constant_channel :
    rp_FiniteTask_annotated rp_Self_Nuisance_worker (fun _ => ()) = (fun _ : Bool => PMF.pure ()) := by
  funext x
  simp only [ PMF.map, Function.comp_def, PMF.bind_const]

private theorem constant_information :
    rp_FiniteTask_shannon rp_Self_fair (fun _ : Bool => PMF.pure ()) = 0 := by
  have hm : rp_FiniteTask_reportMass rp_Self_fair (fun _ : Bool => PMF.pure ()) () = 1 := by
    change mass ((rp_Self_fair).bind (fun _ => PMF.pure ())) () = 1
    rw [PMF.bind_const]
    norm_num [mass_pure]
  norm_num [hm, mass_fair, mass_pure]

theorem value_at_truth : value rp_Self_fair rp_Self_Nuisance_worker = Real.log 2 :=
  (value_eq rp_Self_fair rp_Self_Nuisance_worker).trans information_log_two

/-- Literal and task-only annotations both retain log 2 nats; the constant
annotation retains no task information. -/
theorem payoff_table :
    payoff rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker = Real.log 2 ∧
      payoff rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker = Real.log 2 ∧ payoff rp_Self_Nuisance_constant rp_Self_fair rp_Self_Nuisance_worker = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · exact (literal_payoff rp_Self_fair rp_Self_Nuisance_worker).trans information_log_two
  · change payoff (rp_Binary_annotate Prod.fst) rp_Self_fair rp_Self_Nuisance_worker = Real.log 2
    rw [payoff_annotation, task_channel]
    exact task_information
  · change payoff (rp_Binary_annotate (fun _ : Bool × Bool => ())) rp_Self_fair rp_Self_Nuisance_worker = 0
    refine (payoff_annotation rp_Self_fair rp_Self_Nuisance_worker
      (fun _ : Bool × Bool => ())).trans ?_
    rw [constant_channel]
    exact constant_information

theorem regret_table :
    regret rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker = 0 ∧
      regret rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker = 0 ∧ regret rp_Self_Nuisance_constant rp_Self_fair rp_Self_Nuisance_worker = Real.log 2 := by
  unfold regret
  rw [value_at_truth, payoff_table.1, payoff_table.2.1, payoff_table.2.2]
  simp

theorem truthful_optima :
    rp_Self_Nuisance_literal ≠ rp_Self_Nuisance_task ∧
      payoff rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker = value rp_Self_fair rp_Self_Nuisance_worker ∧
      payoff rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker = value rp_Self_fair rp_Self_Nuisance_worker :=
  ⟨Ne.symm Self.Nuisance.distinct,
    payoff_table.1.trans value_at_truth.symm,
    payoff_table.2.1.trans value_at_truth.symm⟩

theorem truthful_joint_bounds (d : Critic (Bool × Bool))
    (σ : Kernel (Bool × Bool) (Bool × Bool)) :
    payoff d rp_Self_fair (fun x => (rp_Self_Nuisance_worker x).bind σ) ≤ payoff rp_Self_Nuisance_literal rp_Self_fair rp_Self_Nuisance_worker ∧
      payoff d rp_Self_fair (fun x => (rp_Self_Nuisance_worker x).bind σ) ≤ payoff rp_Self_Nuisance_task rp_Self_fair rp_Self_Nuisance_worker :=
  ⟨truthful_global_optimal rp_Self_fair rp_Self_Nuisance_worker rp_Self_Nuisance_literal truthful_optima.2.1 d σ,
    truthful_global_optimal rp_Self_fair rp_Self_Nuisance_worker rp_Self_Nuisance_task truthful_optima.2.2 d σ⟩

/-- Bijective annotations relabel reports without losing task information. -/
theorem bijective_annotation {B : Type} [Fintype B]
    (g : Bool × Bool → B) (hg : Function.Bijective g) :
    payoff (rp_Binary_annotate g) rp_Self_fair rp_Self_Nuisance_worker = Real.log 2 ∧
      regret (rp_Binary_annotate g) rp_Self_fair rp_Self_Nuisance_worker = 0 := by
  have he : payoff (rp_Binary_annotate g) rp_Self_fair rp_Self_Nuisance_worker = rp_FiniteTask_shannon rp_Self_fair rp_Self_Nuisance_worker :=
    (payoff_annotation rp_Self_fair rp_Self_Nuisance_worker g).trans
      (shannon_annotation_injective rp_Self_fair rp_Self_Nuisance_worker g hg.1)
  refine ⟨he.trans information_log_two, ?_⟩
  rw [regret, value_eq, he, sub_self]

end MutualEvaluation.ShannonTarget.Example
end