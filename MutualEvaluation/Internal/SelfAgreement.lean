import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.SelfInformation
import MutualEvaluation.Internal.FiberVariance
import MutualEvaluation.Internal.CriticQuotient

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-!
# Normalized self-agreement and posterior loss

The class representation holds on arbitrary pair laws. Information identities
require two independent observations conditional on the same fair binary task.
Validity concerns the entire critic table; posterior loss concerns positive mass.
This module defines a law functional, not an operational replication loop.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Self
open Probability Binary _root_.MutualEvaluation.Fiber
attribute [local instance] Classical.propDecidable

variable {R B : Type} [Fintype R]

def Q (c : Critic R) (μ : PMF (R × R)) (a : R) : ℝ :=
  ∑ b, if rp_Binary_Rel c a b then mass (μ.map Prod.fst) b else 0

def H (c : Critic R) (μ : PMF (R × R)) (a : R) : ℝ :=
  ∑ b, if rp_Binary_Rel c a b then mass μ (a, b) else 0

/-- Real division makes a zero-mass class contribute zero. -/
def agreement (c : Critic R) (μ : PMF (R × R)) : ℝ :=
  (∑ a, H c μ a / Q c μ a) - 1

/-- Weighted mean of actual report posteriors within the critic's class.
Its value on a zero-mass class is zero. -/
def classPosterior (c : Critic R) (hc : rp_Binary_Valid c) (k : Kernel Bool R) (a : R) : ℝ :=
  mean (classMap c hc) (reportMass k) (posterior k) (classMap c hc a)

/-! Private aggregation helpers keep the public review surface small. -/

private def fiberH (g : R → B) (μ : PMF (R × R)) (a : R) : ℝ :=
  ∑ b, if g b = g a then mass μ (a, b) else 0

private def atomScore (g : R → B) (μ : PMF (R × R)) : ℝ :=
  (∑ a, fiberH g μ a / push g (mass (μ.map Prod.fst)) (g a)) - 1

private theorem annotation_atom (g : R → B) (μ : PMF (R × R)) :
    agreement (rp_Binary_annotate g) μ = atomScore g μ := by
  simp only [agreement, H, Q, annotate_rel, atomScore, fiberH, push]
  simp [eq_comm]

private theorem agreement_atom (c : Critic R) (hc : rp_Binary_Valid c) (μ : PMF (R × R)) :
    agreement c μ = atomScore (classMap c hc) μ := by
  have he (a b : R) :
      rp_Binary_Rel c a b ↔ classMap c hc b = classMap c hc a := by
    rw [eq_comm, classMap_eq_iff]
  simp only [agreement, H, Q, he, atomScore, fiberH, push]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1 <;> apply Finset.sum_congr rfl <;> intro b _ <;> split_ifs <;> rfl

private theorem atom_representation [Fintype B] (g : R → B) (μ : PMF (R × R)) :
    atomScore g μ =
      (∑ z, (∑ a, ∑ b, if g a = z ∧ g b = z then mass μ (a, b) else 0) /
        push g (mass (μ.map Prod.fst)) z) - 1 := by
  have he (z : B) : push g (fiberH g μ) z =
      ∑ a, ∑ b, if g a = z ∧ g b = z then mass μ (a, b) else 0 := by
    unfold push fiberH
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : g a = z <;> simp [ha]
  unfold atomScore
  simp only [div_eq_mul_inv]
  rw [← push_mul g (fiberH g μ) (fun z => (push g (mass (μ.map Prod.fst)) z)⁻¹)]
  simp only [he]

/-- Each equivalence class appears once. The numerator is its joint class event.
No repeated-channel or full-support hypothesis is needed for this representation. -/
theorem representation (c : Critic R) (hc : rp_Binary_Valid c) (μ : PMF (R × R)) :
    agreement c μ =
      (∑ z : Classes c hc,
        (∑ a, ∑ b, if classMap c hc a = z ∧ classMap c hc b = z
          then mass μ (a, b) else 0) /
        (∑ a, if classMap c hc a = z then mass (μ.map Prod.fst) a else 0)) - 1 := by
  rw [agreement_atom c hc, atom_representation]
  simp only [push]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> rfl

private theorem fiberH_repeated (g : R → B) (k : Kernel Bool R) (a : R) :
    fiberH g (repeated k) a =
      reportMass k a * push g (reportMass k) (g a) +
        4 * (reportMass k a * (posterior k a - 1 / 2)) *
          (push g (reportMass k) (g a) *
            (mean g (reportMass k) (posterior k) (g a) - 1 / 2)) := by
  have hm := mass_mul_mean g (reportMass k) (posterior k) (reportMass_nonneg k) (g a)
  simp only [mul_sub]
  rw [hm]
  simp only [fiberH, push, Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : g b = g a
  · simp only [if_pos hb, repeated_posterior]
    ring
  · simp only [if_neg hb]
    ring

private theorem fiber_ratio (g : R → B) (k : Kernel Bool R) (a : R) :
    fiberH g (repeated k) a / push g (reportMass k) (g a) =
      reportMass k a + 4 * (reportMass k a * (posterior k a - 1 / 2)) *
        (mean g (reportMass k) (posterior k) (g a) - 1 / 2) := by
  rw [fiberH_repeated]
  by_cases hz : push g (reportMass k) (g a) = 0
  · have ha := weight_zero g (reportMass k) (reportMass_nonneg k) a hz
    simp [ha]
  · field_simp

private theorem score_repeated [Fintype B] (g : R → B) (k : Kernel Bool R) :
    atomScore g (repeated k) =
      4 * ∑ z, push g (reportMass k) z *
        (mean g (reportMass k) (posterior k) z - 1 / 2)^2 := by
  have hg :
      ∑ a, (reportMass k a * (posterior k a - 1 / 2)) *
          (mean g (reportMass k) (posterior k) (g a) - 1 / 2) =
        ∑ z, push g (reportMass k) z *
          (mean g (reportMass k) (posterior k) z - 1 / 2)^2 := by
    rw [← push_mul g (fun a => reportMass k a * (posterior k a - 1 / 2))
      (fun z => mean g (reportMass k) (posterior k) z - 1 / 2)]
    apply Finset.sum_congr rfl
    intro z _
    have hm := mass_mul_mean g (reportMass k) (posterior k) (reportMass_nonneg k) z
    have hp :
        push g (fun a => reportMass k a * (posterior k a - 1 / 2)) z =
          push g (reportMass k) z * (mean g (reportMass k) (posterior k) z - 1 / 2) := by
      rw [mul_sub, hm]
      simp only [push, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> ring
    rw [hp]
    ring
  have hm : mass ((repeated k).map Prod.fst) = reportMass k := by
    funext a
    exact repeated_marginal k a
  unfold atomScore
  rw [hm]
  simp only [fiber_ratio, Finset.sum_add_distrib]
  simp only [mul_assoc] at hg ⊢
  rw [← Finset.mul_sum, reportMass_sum, hg]
  ring

private theorem information_sub_score [Fintype B] (g : R → B) (k : Kernel Bool R) :
    information k - atomScore g (repeated k) =
      4 * ∑ a, reportMass k a *
        (posterior k a - mean g (reportMass k) (posterior k) (g a))^2 := by
  rw [information, score_repeated,
    decomposition g (reportMass k) (posterior k) (reportMass_nonneg k) (1 / 2)]
  ring

/-- The score retained by any finite annotation, regardless of its class labels. -/
theorem annotation_score [Fintype B] (g : R → B) (k : Kernel Bool R) :
    agreement (rp_Binary_annotate g) (repeated k) =
      4 * ∑ z, push g (reportMass k) z *
        (mean g (reportMass k) (posterior k) z - 1 / 2)^2 := by
  rw [annotation_atom, score_repeated]

theorem agreement_information (k : Kernel Bool R) :
    agreement (rp_Binary_annotate id) (repeated k) = information k := by
  rw [annotation_atom]
  have hz : (∑ a, reportMass k a *
      (posterior k a - mean id (reportMass k) (posterior k) a)^2) = 0 := by
    apply (loss_zero_iff id _ _ (reportMass_nonneg k)).2
    intro a b hab _ _
    exact congrArg (posterior k) hab
  have h := information_sub_score id k
  simp only [id_eq, hz, mul_zero] at h
  linarith

/-- This is the future game's normalized regret once its envelope is identified. -/
theorem agreement_regret (k : Kernel Bool R) (c : Critic R) (hc : rp_Binary_Valid c) :
    information k - agreement c (repeated k) =
      4 * ∑ a, reportMass k a * (posterior k a - classPosterior c hc k a)^2 := by
  rw [agreement_atom c hc, information_sub_score]
  rfl

end MutualEvaluation.Self
end