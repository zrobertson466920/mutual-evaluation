import MutualEvaluation.Public.CriticTiming
import Mathlib.Probability.ProductMeasure

/-!
INTERNAL — expression syntax for upstream replication proofs.
The primitive definitions have their sole declaration sites in Public/Replication.
These scoped notations expand to expressions, not additional kernel definitions.
They allow proof support to precede the single annotated Public module.
-/
noncomputable section
namespace MutualEvaluation.Internal.ReplicationExpressions
open MeasureTheory MutualEvaluation
open MutualEvaluation.Binary MutualEvaluation.Probability
set_option quotPrecheck false
attribute [local instance] Classical.propDecidable

scoped notation "rp_Binary_Rel" =>
(fun {R : Type} (c : Critic R) (a b : R) =>
(show Prop from
(c (a, b) : ℝ) = 1))

scoped notation "rp_Binary_Valid" =>
(fun {R : Type} (c : Critic R) =>
(show Prop from
Equivalence (rp_Binary_Rel c)))

scoped notation "rp_Binary_annotate" =>
(fun {R B : Type} (g : R → B) =>
(show Critic R from
fun ab =>
  if g ab.1 = g ab.2 then ⟨1, by simp [scores]⟩ else ⟨0, by simp [scores]⟩))

scoped notation "rp_Replication_Transcript" =>
(fun (R : Type) =>
(show Type from
R × ((ℕ → R) × (ℕ → R))))

scoped notation "rp_Replication_iid" =>
(fun {R : Type} [MeasurableSpace R] (p : PMF R) =>
(show Measure (ℕ → R) from
Measure.infinitePi (fun _ : ℕ => p.toMeasure)))

scoped notation "rp_Replication_conditionalTranscriptLaw" =>
(fun {X R : Type} [MeasurableSpace R] (P : PMF X) (k : Kernel X R) (x : X) =>
(show Measure (rp_Replication_Transcript R) from
(k x).toMeasure.prod ((rp_Replication_iid (k x)).prod (rp_Replication_iid (P.bind k)))))

scoped notation "rp_Replication_transcriptLaw" =>
(fun {X R : Type} [MeasurableSpace R] [Fintype X] (P : PMF X) (k : Kernel X R) =>
(show Measure (rp_Replication_Transcript R) from
∑ x, P x • rp_Replication_conditionalTranscriptLaw P k x))

scoped notation "rp_Replication_firstHit" =>
(fun (p : ℕ → Prop) =>
(show ℕ∞ from
if h : ∃ n, p n then ((Nat.find h + 1 : ℕ) : ℕ∞) else ⊤))

scoped notation "rp_Replication_R_specific" =>
(fun {R : Type} (c : Critic R) (t : rp_Replication_Transcript R) =>
(show ℕ∞ from
rp_Replication_firstHit (fun n => rp_Binary_Rel c t.1 (t.2.1 n))))

scoped notation "rp_Replication_R_null" =>
(fun {R : Type} (c : Critic R) (t : rp_Replication_Transcript R) =>
(show ℕ∞ from
rp_Replication_firstHit (fun n => rp_Binary_Rel c t.1 (t.2.2 n))))

scoped notation "rp_Replication_W_chiSquared" =>
(fun {R : Type} (c : Critic R) (t : rp_Replication_Transcript R) =>
(show ℝ from
if rp_Binary_Valid c then
    if rp_Binary_Rel c t.1 (t.2.1 0) then
      if rp_Replication_R_null c t = ⊤ then 0 else (rp_Replication_R_null c t).toNat - 1
    else -1
  else 0))

scoped notation "rp_Replication_H" =>
(fun (n : ℕ) =>
(show ℝ from
∑ j ∈ Finset.range n, ((j : ℝ) + 1)⁻¹))

scoped notation "rp_Replication_W_KL" =>
(fun {R : Type} (c : Critic R) (t : rp_Replication_Transcript R) =>
(show ℝ from
if rp_Binary_Valid c then
    if rp_Replication_R_null c t = ⊤ ∨ rp_Replication_R_specific c t = ⊤ then 0
    else rp_Replication_H ((rp_Replication_R_null c t).toNat - 1) - rp_Replication_H ((rp_Replication_R_specific c t).toNat - 1)
  else 0))

scoped notation "rp_Replication_u_chiSquared" =>
(fun {X R : Type} [MeasurableSpace R] [Fintype X] (c : Critic R) (P : PMF X) (k : Kernel X R) =>
(show ℝ from
∫ t, rp_Replication_W_chiSquared c t ∂rp_Replication_transcriptLaw P k))

scoped notation "rp_Replication_u_KL" =>
(fun {X R : Type} [MeasurableSpace R] [Fintype X] (c : Critic R) (P : PMF X) (k : Kernel X R) =>
(show ℝ from
∫ t, rp_Replication_W_KL c t ∂rp_Replication_transcriptLaw P k))

scoped notation "rp_Replication_pearsonScore" =>
(fun (X R : Type) [MeasurableSpace R] [Fintype X] =>
(show Score R (PMF X × Kernel X R) from
{
  S := scores
  nonempty := by classical simp [scores]
  u := fun c θ => rp_Replication_u_chiSquared c θ.1 θ.2
}))

scoped notation "rp_Replication_klScore" =>
(fun (X R : Type) [MeasurableSpace R] [Fintype X] =>
(show Score R (PMF X × Kernel X R) from
{
  S := scores
  nonempty := by classical simp [scores]
  u := fun c θ => rp_Replication_u_KL c θ.1 θ.2
}))

scoped notation "rp_Replication_V_chiSquared" =>
(fun {X R : Type} [MeasurableSpace R] [Fintype X] (P : PMF X) (k : Kernel X R) =>
(show ℝ from
((rp_Replication_pearsonScore (X) (R))).envelope (P, k)))

scoped notation "rp_Replication_V_KL" =>
(fun {X R : Type} [MeasurableSpace R] [Fintype X] (P : PMF X) (k : Kernel X R) =>
(show ℝ from
((rp_Replication_klScore (X) (R))).envelope (P, k)))

scoped notation "rp_Replication_r_chiSquared" =>
(fun {X R : Type} [MeasurableSpace R] [Fintype X] (c : Critic R) (P : PMF X) (k : Kernel X R) =>
(show ℝ from
rp_Replication_V_chiSquared P k - rp_Replication_u_chiSquared c P k))

scoped notation "rp_Replication_r_KL" =>
(fun {X R : Type} [MeasurableSpace R] [Fintype X] (c : Critic R) (P : PMF X) (k : Kernel X R) =>
(show ℝ from
rp_Replication_V_KL P k - rp_Replication_u_KL c P k))

scoped notation "rp_FiniteTask_annotated" =>
(fun {X R B : Type} (k : Kernel X R) (g : R → B) =>
(show Kernel X B from
fun x => (k x).map g))

scoped notation "rp_FiniteTask_jointMass" =>
(fun {X R : Type} (P : PMF X) (k : Kernel X R) (x : X) (a : R) =>
(show ℝ from
mass P x * mass (k x) a))

scoped notation "rp_FiniteTask_reportMass" =>
(fun {X R : Type} (P : PMF X) (k : Kernel X R) (a : R) =>
(show ℝ from
mass (P.bind k) a))

scoped notation "rp_FiniteTask_posterior" =>
(fun {X R : Type} (P : PMF X) (k : Kernel X R) (a : R) (x : X) =>
(show ℝ from
rp_FiniteTask_jointMass P k x a / rp_FiniteTask_reportMass P k a))

scoped notation "rp_FiniteTask_pearson" =>
(fun {X R : Type} (P : PMF X) (k : Kernel X R) [Fintype X] [Fintype R] =>
(show ℝ from
(∑ x, ∑ a, (rp_FiniteTask_jointMass P k x a)^2 /
    (mass P x * rp_FiniteTask_reportMass P k a)) - 1))

scoped notation "rp_FiniteTask_shannon" =>
(fun {X R : Type} (P : PMF X) (k : Kernel X R) [Fintype X] [Fintype R] =>
(show ℝ from
∑ x, ∑ a, rp_FiniteTask_jointMass P k x a *
    Real.log (rp_FiniteTask_jointMass P k x a / (mass P x * rp_FiniteTask_reportMass P k a))))

scoped notation "rp_FiniteLog_divergence" =>
(fun {A : Type} [Fintype A] (p q : A → ℝ) =>
(show ℝ from
∑ a, p a * Real.log (p a / q a)))

scoped notation "rp_FiniteTask_conditionalInformation" =>
(fun {X R B : Type} (P : PMF X) (k : Kernel X R) [Fintype X] [Fintype R] (g : R → B) =>
(show ℝ from
∑ a, rp_FiniteTask_reportMass P k a *
    rp_FiniteLog_divergence (rp_FiniteTask_posterior P k a) (rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a))))

scoped notation "rp_Replication_reportingNash" =>
(fun {X R : Type} (U : Score R (PMF X × Kernel X R)) (P : PMF X) (w : Kernel X R) (σ : Kernel R R) (c : R × R → U.S) =>
(show Prop from
(∀ d, U.u d (P, fun x => (w x).bind σ) ≤
    U.u c (P, fun x => (w x).bind σ)) ∧
  ∀ τ : Kernel R R, U.u c (P, fun x => (w x).bind τ) ≤
    U.u c (P, fun x => (w x).bind σ)))

scoped notation "rp_Self_fair" =>
(show PMF Bool from
PMF.uniformOfFintype Bool)

scoped notation "rp_Self_Nuisance_worker" =>
(show Kernel Bool (Bool × Bool) from
fun x => (rp_Self_fair).map fun u => (x, u))

scoped notation "rp_Self_Nuisance_literal" =>
(show Critic (Bool × Bool) from
rp_Binary_annotate id)

scoped notation "rp_Self_Nuisance_task" =>
(show Critic (Bool × Bool) from
rp_Binary_annotate Prod.fst)

scoped notation "rp_Self_Nuisance_constant" =>
(show Critic (Bool × Bool) from
rp_Binary_annotate (fun _ => ()))

end MutualEvaluation.Internal.ReplicationExpressions
end
