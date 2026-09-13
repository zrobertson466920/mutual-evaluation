import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.FiniteTaskProcessing
import MutualEvaluation.Internal.CriticQuotient

/-!
INTERNAL / DRAFT — information-based Pearson target score.
This is NOT Replication.u_chiSquared and is not an unbiasedness certificate.
A valid critic retains the information of its quotient annotation; an invalid
critic receives zero. The envelope ranges over the full binary critic space.

All conclusions in this file concern this finite-sum target. Transfer to the
actual loop score still requires equality of payoffs for every critic.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.PearsonTarget
open Probability Binary FiniteTask
attribute [local instance] Classical.propDecidable

variable {X R : Type} [Fintype X] [Fintype R]

def payoff (c : Critic R) (P : PMF X) (k : Kernel X R) : ℝ :=
  if hc : rp_Binary_Valid c then rp_FiniteTask_pearson P (rp_FiniteTask_annotated k (classMap c hc)) else 0

def score : Score R (PMF X × Kernel X R) where
  S := scores
  nonempty := by simp [scores]
  u := fun c θ => payoff c θ.1 θ.2

def value (P : PMF X) (k : Kernel X R) : ℝ :=
  (score (X := X) (R := R)).envelope (P, k)

def regret (c : Critic R) (P : PMF X) (k : Kernel X R) : ℝ :=
  value P k - payoff c P k

variable (P : PMF X) (k : Kernel X R)

theorem payoff_valid (c : Critic R) (hc : rp_Binary_Valid c) :
    payoff c P k = rp_FiniteTask_pearson P (rp_FiniteTask_annotated k (classMap c hc)) := by
  simp only [payoff, dif_pos hc]

theorem payoff_invalid (c : Critic R) (hc : ¬ rp_Binary_Valid c) :
    payoff c P k = 0 := by
  simp only [payoff, dif_neg hc]

/-- Any finite annotation representation gives the same target payoff as
the canonical quotient. The target does not depend on the choice of labels. -/
theorem payoff_annotation {B : Type} [Fintype B] (g : R → B) :
    payoff (rp_Binary_annotate g) P k = rp_FiniteTask_pearson P (rp_FiniteTask_annotated k g) := by
  rw [payoff_valid P k _ (MutualEvaluation.Binary.annotate_valid_impl g)]
  exact pearson_annotation_eq_of_fibers P k
    (classMap (rp_Binary_annotate g) (MutualEvaluation.Binary.annotate_valid_impl g)) g
    (fun a b => (classMap_eq_iff (rp_Binary_annotate g) (MutualEvaluation.Binary.annotate_valid_impl g) a b).trans
      (annotate_rel g a b))

theorem literal_payoff :
    payoff (rp_Binary_annotate id) P k = rp_FiniteTask_pearson P k :=
  (payoff_annotation P k id).trans
    (pearson_annotation_injective P k id (fun _ _ h => h))

theorem payoff_nonneg (c : Critic R) : 0 ≤ payoff c P k := by
  by_cases hc : rp_Binary_Valid c
  · rw [payoff_valid P k c hc]
    exact pearson_nonneg _ _
  · rw [payoff_invalid P k c hc]

theorem payoff_le_information (c : Critic R) :
    payoff c P k ≤ rp_FiniteTask_pearson P k := by
  by_cases hc : rp_Binary_Valid c
  · rw [payoff_valid P k c hc]
    exact pearson_annotation_mono P k (classMap c hc)
  · rw [payoff_invalid P k c hc]
    exact pearson_nonneg P k

/-- The target envelope is attained by literal agreement, despite including
invalid critics in its strategy space. No waiting-time expectation is used. -/
theorem value_eq : value P k = rp_FiniteTask_pearson P k := by
  change sSup (Set.range fun c : Critic R => payoff c P k) = rp_FiniteTask_pearson P k
  have hb : BddAbove (Set.range fun c : Critic R => payoff c P k) := by
    refine ⟨rp_FiniteTask_pearson P k, ?_⟩
    rintro _ ⟨c, rfl⟩
    exact payoff_le_information P k c
  apply le_antisymm
  · apply csSup_le
    · exact ⟨payoff (rp_Binary_annotate id) P k, ⟨rp_Binary_annotate id, rfl⟩⟩
    · rintro _ ⟨c, rfl⟩
      exact payoff_le_information P k c
  · calc
      rp_FiniteTask_pearson P k = payoff (rp_Binary_annotate id) P k := (literal_payoff P k).symm
      _ ≤ sSup (Set.range fun c : Critic R => payoff c P k) :=
        le_csSup hb ⟨rp_Binary_annotate id, rfl⟩

theorem literal_optimal : payoff (rp_Binary_annotate id) P k = value P k :=
  (literal_payoff P k).trans (value_eq P k).symm

theorem regret_nonneg (c : Critic R) : 0 ≤ regret c P k := by
  rw [regret, value_eq]
  exact sub_nonneg.mpr (payoff_le_information P k c)

theorem regret_zero_iff (c : Critic R) :
    regret c P k = 0 ↔ payoff c P k = value P k :=
  sub_eq_zero.trans eq_comm

/-- Derived regret of the target score, for a globally valid critic. -/
theorem regret_formula (c : Critic R) (hc : rp_Binary_Valid c) :
    regret c P k =
      ∑ x, (∑ a, rp_FiniteTask_reportMass P k a *
        (rp_FiniteTask_posterior P k a x -
          rp_FiniteTask_posterior P (rp_FiniteTask_annotated k (classMap c hc)) (classMap c hc a) x)^2) /
            mass P x := by
  rw [regret, value_eq, payoff_valid P k c hc]
  exact pearson_annotation_loss P k (classMap c hc)

theorem annotation_regret {B : Type} [Fintype B] (g : R → B) :
    regret (rp_Binary_annotate g) P k =
      ∑ x, (∑ a, rp_FiniteTask_reportMass P k a *
        (rp_FiniteTask_posterior P k a x - rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) x)^2) /
          mass P x := by
  rw [regret, value_eq, payoff_annotation]
  exact pearson_annotation_loss P k g

theorem annotation_zero_iff {B : Type} [Fintype B] (g : R → B) :
    regret (rp_Binary_annotate g) P k = 0 ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a = rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) := by
  rw [regret, value_eq, payoff_annotation, sub_eq_zero]
  exact pearson_annotation_eq_iff P k g

/-- Global critic validity is distinct from posterior sufficiency on support. -/
theorem optimal_iff (c : Critic R) (hc : rp_Binary_Valid c) :
    payoff c P k = value P k ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a =
          rp_FiniteTask_posterior P (rp_FiniteTask_annotated k (classMap c hc)) (classMap c hc a) := by
  rw [payoff_valid P k c hc, value_eq]
  exact eq_comm.trans (pearson_annotation_eq_iff P k (classMap c hc))

theorem critic_coarsening {B C : Type} [Fintype B] [Fintype C]
    (g : R → B) (h : B → C) :
    payoff (rp_Binary_annotate (h ∘ g)) P k ≤ payoff (rp_Binary_annotate g) P k := by
  rw [payoff_annotation, payoff_annotation]
  exact pearson_annotation_coarsen P k g h

theorem value_data_processing {B : Type} [Fintype B] (τ : Kernel R B) :
    value P (fun x => (k x).bind τ) ≤ value P k := by
  rw [value_eq, value_eq]
  exact pearson_data_processing P k τ

/-- Any critic optimal at the ungarbled channel bounds every simultaneous
change of critic and fixed reporting kernel, for the target score only. -/
theorem truthful_global_optimal (c : Critic R)
    (hc : payoff c P k = value P k) (d : Critic R) (σ : Kernel R R) :
    payoff d P (fun x => (k x).bind σ) ≤ payoff c P k := by
  rw [hc, value_eq]
  exact (payoff_le_information P _ d).trans (pearson_data_processing P k σ)

/-- The two unilateral best-response inequalities for a single worker and
critic. Worker deviations choose one kernel before the experiment. These are
channel-level target-score conclusions, not a Core Game or loop certificate. -/
theorem truthful_best_responses (c : Critic R)
    (hc : payoff c P k = value P k) :
    (∀ d, payoff d P k ≤ payoff c P k) ∧
      ∀ σ : Kernel R R, payoff c P (fun x => (k x).bind σ) ≤ payoff c P k := by
  constructor
  · intro d
    rw [hc, value_eq]
    exact payoff_le_information P k d
  · intro σ
    exact truthful_global_optimal P k c hc c σ

end MutualEvaluation.PearsonTarget
end