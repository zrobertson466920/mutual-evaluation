import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.FiniteTaskInformation
import MutualEvaluation.Internal.FiniteLogDivergence

/-!
INTERNAL / DRAFT — Shannon information for general finite tasks.
This module uses the manuscript's finite joint-mass formula and natural logarithm.
It does not define or replace Replication.u_KL, the expected harmonic payment.
No full-support hypothesis is imposed on the prior or reported channel.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.FiniteTask
open Probability

variable {X R B : Type} (P : PMF X) (k : Kernel X R)

/- Shannon task information, with zero-mass terms contributing zero.
The joint is dominated by its product reference by reference_dominated. -/


/- The conditional-information expression for a deterministic annotation.
Its properties are finite-information targets, not identities for loop regret. -/


/-- Posterior divergence from the prior, averaged over reported returns. -/
theorem shannon_eq_posterior [Fintype X] [Fintype R] :
    rp_FiniteTask_shannon P k =
      ∑ a, rp_FiniteTask_reportMass P k a * rp_FiniteLog_divergence (rp_FiniteTask_posterior P k a) (mass P) := by
  dsimp only
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hr : rp_FiniteTask_jointMass P k x a / (mass P x * rp_FiniteTask_reportMass P k a) =
      rp_FiniteTask_posterior P k a x / mass P x := by
    simp only [ div_div, mul_comm]
  rw [hr, ← mul_assoc, weighted_posterior]

theorem shannon_nonneg [Fintype X] [Fintype R] : 0 ≤ rp_FiniteTask_shannon P k := by
  rw [shannon_eq_posterior]
  apply Finset.sum_nonneg
  intro a _
  by_cases ha : rp_FiniteTask_reportMass P k a = 0
  · simp [ha]
  · have ha' : 0 < rp_FiniteTask_reportMass P k a :=
      lt_of_le_of_ne (reportMass_nonneg P k a) (Ne.symm ha)
    apply mul_nonneg (reportMass_nonneg P k a)
    exact FiniteLog.divergence_nonneg (rp_FiniteTask_posterior P k a) (mass P)
      (posterior_nonneg P k a) (mass_nonneg P)
      (fun x hx => posterior_prior_zero P k a x hx)
      ((posterior_sum P k a ha').trans (mass_sum P).symm)

/-- A positive-mass report belongs to a positive-mass annotation class. -/
theorem annotated_reportMass_pos [Fintype R] (g : R → B) (a : R)
    (ha : 0 < rp_FiniteTask_reportMass P k a) :
    0 < rp_FiniteTask_reportMass P (rp_FiniteTask_annotated k g) (g a) := by
  rw [annotated_reportMass]
  exact ha.trans_le (_root_.MutualEvaluation.Fiber.weight_le_push g
    (rp_FiniteTask_reportMass P k) (reportMass_nonneg P k) a)

/-- The report posterior is dominated by its class posterior, including null
reports. Thus the conditional-information sum hides no singular KL terms. -/
theorem annotated_posterior_dominated [Fintype X] [Fintype R]
    (g : R → B) (a : R) (x : X)
    (hz : rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) x = 0) :
    rp_FiniteTask_posterior P k a x = 0 := by
  have hj : rp_FiniteTask_jointMass P (rp_FiniteTask_annotated k g) x (g a) = 0 := by
    rw [← weighted_posterior, hz, mul_zero]
  have hl : rp_FiniteTask_jointMass P k x a ≤ rp_FiniteTask_jointMass P (rp_FiniteTask_annotated k g) x (g a) := by
    rw [annotated_jointMass]
    exact _root_.MutualEvaluation.Fiber.weight_le_push g
      (rp_FiniteTask_jointMass P k x) (jointMass_nonneg P k x) a
  have hja : rp_FiniteTask_jointMass P k x a = 0 :=
    le_antisymm (hj ▸ hl) (jointMass_nonneg P k x a)
  simp only [ hja, zero_div]

private theorem shannon_eq_log_posterior [Fintype X] [Fintype R] :
    rp_FiniteTask_shannon P k =
      (∑ a, ∑ x, rp_FiniteTask_jointMass P k x a * Real.log (rp_FiniteTask_posterior P k a x)) -
        ∑ x, mass P x * Real.log (mass P x) := by
  have hd (a : R) :
      rp_FiniteLog_divergence (rp_FiniteTask_posterior P k a) (mass P) =
        ∑ x, rp_FiniteTask_posterior P k a x *
          (Real.log (rp_FiniteTask_posterior P k a x) - Real.log (mass P x)) :=
    FiniteLog.divergence_eq_sub _ _
      (fun x hx => posterior_prior_zero P k a x hx)
  have hc :
      (∑ a, ∑ x, rp_FiniteTask_jointMass P k x a * Real.log (mass P x)) =
        ∑ x, mass P x * Real.log (mass P x) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, jointMass_sum_report]
  rw [shannon_eq_posterior]
  simp only [hd, Finset.mul_sum, ← mul_assoc, weighted_posterior,
    mul_sub, Finset.sum_sub_distrib, hc]

private theorem annotation_log_cross [Fintype X] [Fintype R] [Fintype B]
    (g : R → B) :
    (∑ a, ∑ x, rp_FiniteTask_jointMass P k x a *
      Real.log (rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) x)) =
        ∑ b, ∑ x, rp_FiniteTask_jointMass P (rp_FiniteTask_annotated k g) x b *
          Real.log (rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) b x) := by
  calc
    _ = ∑ x, ∑ a, rp_FiniteTask_jointMass P k x a *
        Real.log (rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) x) := Finset.sum_comm
    _ = ∑ x, ∑ b, rp_FiniteTask_jointMass P (rp_FiniteTask_annotated k g) x b *
        Real.log (rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) b x) := by
      apply Finset.sum_congr rfl
      intro x _
      simpa only [annotated_jointMass] using
        (_root_.MutualEvaluation.Fiber.push_mul g (rp_FiniteTask_jointMass P k x)
          (fun b => Real.log (rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) b x))).symm
    _ = _ := Finset.sum_comm

/-- Exact Shannon information lost by deterministic annotation.
The right side is the manuscript's posterior conditional-information sum,
not yet the regret of the expected harmonic payment. -/
theorem shannon_annotation_loss [Fintype X] [Fintype R] [Fintype B]
    (g : R → B) :
    rp_FiniteTask_shannon P k - rp_FiniteTask_shannon P (rp_FiniteTask_annotated k g) = rp_FiniteTask_conditionalInformation P k g := by
  have hd (a : R) :
      rp_FiniteLog_divergence (rp_FiniteTask_posterior P k a)
        (rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a)) =
          ∑ x, rp_FiniteTask_posterior P k a x *
            (Real.log (rp_FiniteTask_posterior P k a x) -
              Real.log (rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) x)) :=
    FiniteLog.divergence_eq_sub _ _
      (fun x hx => annotated_posterior_dominated P k g a x hx)
  rw [shannon_eq_log_posterior, shannon_eq_log_posterior]
  simp only [ hd, Finset.mul_sum, ← mul_assoc,
    weighted_posterior, mul_sub, Finset.sum_sub_distrib, annotation_log_cross]
  ring

private theorem annotation_divergence_nonneg [Fintype X] [Fintype R]
    (g : R → B) (a : R) :
    0 ≤ rp_FiniteLog_divergence (rp_FiniteTask_posterior P k a)
      (rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a)) := by
  by_cases ha : rp_FiniteTask_reportMass P k a = 0
  · simp [ ha]
  · have ha' : 0 < rp_FiniteTask_reportMass P k a :=
      lt_of_le_of_ne (reportMass_nonneg P k a) (Ne.symm ha)
    exact FiniteLog.divergence_nonneg _ _
      (posterior_nonneg P k a) (posterior_nonneg P (rp_FiniteTask_annotated k g) (g a))
      (fun x hx => annotated_posterior_dominated P k g a x hx)
      ((posterior_sum P k a ha').trans
        (posterior_sum P (rp_FiniteTask_annotated k g) (g a)
          (annotated_reportMass_pos P k g a ha')).symm)

theorem conditionalInformation_nonneg [Fintype X] [Fintype R] (g : R → B) :
    0 ≤ rp_FiniteTask_conditionalInformation P k g := by
  exact Finset.sum_nonneg (fun a _ =>
    mul_nonneg (reportMass_nonneg P k a) (annotation_divergence_nonneg P k g a))

theorem shannon_annotation_mono [Fintype X] [Fintype R] [Fintype B] (g : R → B) :
    rp_FiniteTask_shannon P (rp_FiniteTask_annotated k g) ≤ rp_FiniteTask_shannon P k := by
  apply sub_nonneg.mp
  rw [shannon_annotation_loss]
  exact conditionalInformation_nonneg P k g

/-- Conditional information vanishes exactly when annotation preserves the
entire task posterior at every positive-mass report. -/
theorem conditionalInformation_zero_iff [Fintype X] [Fintype R] (g : R → B) :
    rp_FiniteTask_conditionalInformation P k g = 0 ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a = rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) := by
  rw [ Finset.sum_eq_zero_iff_of_nonneg
    (fun a (_ : a ∈ Finset.univ) =>
      mul_nonneg (reportMass_nonneg P k a) (annotation_divergence_nonneg P k g a))]
  constructor
  · intro h a ha
    have hz := (mul_eq_zero.mp (h a (Finset.mem_univ a))).resolve_left (ne_of_gt ha)
    exact (FiniteLog.divergence_zero_iff _ _
      (posterior_nonneg P k a) (posterior_nonneg P (rp_FiniteTask_annotated k g) (g a))
      (fun x hx => annotated_posterior_dominated P k g a x hx)
      ((posterior_sum P k a ha).trans
        (posterior_sum P (rp_FiniteTask_annotated k g) (g a)
          (annotated_reportMass_pos P k g a ha)).symm)).1 hz
  · intro h a _
    by_cases ha : rp_FiniteTask_reportMass P k a = 0
    · simp [ha]
    · rw [h a (lt_of_le_of_ne (reportMass_nonneg P k a) (Ne.symm ha)),
        FiniteLog.divergence_self, mul_zero]

theorem shannon_annotation_eq_iff [Fintype X] [Fintype R] [Fintype B]
    (g : R → B) :
    rp_FiniteTask_shannon P k = rp_FiniteTask_shannon P (rp_FiniteTask_annotated k g) ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a = rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) := by
  rw [← sub_eq_zero, shannon_annotation_loss]
  exact conditionalInformation_zero_iff P k g

/-- Injective annotations preserve Shannon information. Posterior sufficiency
is shared with the Pearson characterization; no full support is required. -/
theorem shannon_annotation_injective [Fintype X] [Fintype R] [Fintype B]
    (g : R → B) (hg : Function.Injective g) :
    rp_FiniteTask_shannon P (rp_FiniteTask_annotated k g) = rp_FiniteTask_shannon P k := by
  symm
  apply (shannon_annotation_eq_iff P k g).2
  exact (pearson_annotation_eq_iff P k g).1
    (pearson_annotation_injective P k g hg).symm

/-- Only the full-table annotation classes matter, not their labels. -/
theorem shannon_annotation_eq_of_fibers [Fintype X] [Fintype R] [Fintype B]
    {C : Type} [Fintype C] (g : R → B) (h : R → C)
    (he : ∀ a b, g a = g b ↔ h a = h b) :
    rp_FiniteTask_shannon P (rp_FiniteTask_annotated k g) = rp_FiniteTask_shannon P (rp_FiniteTask_annotated k h) := by
  have hg := shannon_annotation_loss P k g
  have hh := shannon_annotation_loss P k h
  dsimp only at hg hh
  simp_rw [annotated_posterior_eq_of_fibers P k g h he] at hg
  linarith

end MutualEvaluation.FiniteTask
end