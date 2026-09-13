import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.CriticQuotient
import MutualEvaluation.Internal.ReplicationPaths

/-!
Internal support for replication clocks and payments.

Public declarations and author annotations live in Public/Replication. This
module supplies implementation results, not an additional annotated interface.

This file covers pathwise clocks and payments. ReplicationLaw supplies the
sampling law and scores; ReplicationTermination supplies measurability and
almost-sure termination. Integrability and unbiasedness remain separate
obligations.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open Binary
open Internal.ReplicationPaths

attribute [local instance] Classical.propDecidable

/-! ## The replication interface -/

/- Report-only potential transcript: anchor, same-task stream, fresh-task stream.
Entry 0 of either stream is call 1 in the manuscript. Unused potential calls
are not requests made by the mechanism. No task or annotation is exposed here. -/


/- The specific type-replication count, including the successful call. -/


/- The null type-replication count, including the successful call. -/


/-- The first-hit event is a success preceded by failures, not a chosen count law. -/
theorem specific_first_hit {R : Type} (c : Critic R) (t : rp_Replication_Transcript R) (n : ℕ) :
    rp_Replication_R_specific c t = ((n + 1 : ℕ) : ℕ∞) ↔
      rp_Binary_Rel c t.1 (t.2.1 n) ∧ ∀ m < n, ¬ rp_Binary_Rel c t.1 (t.2.1 m) :=
  firstHit_eq_succ_iff _ n

theorem null_first_hit {R : Type} (c : Critic R) (t : rp_Replication_Transcript R) (n : ℕ) :
    rp_Replication_R_null c t = ((n + 1 : ℕ) : ℕ∞) ↔
      rp_Binary_Rel c t.1 (t.2.2 n) ∧ ∀ m < n, ¬ rp_Binary_Rel c t.1 (t.2.2 m) :=
  firstHit_eq_succ_iff _ n

/-- The annotation map is used for analysis, not supplied to either search. -/
theorem annotation_clocks_impl {R B : Type} (g : R → B) (t : rp_Replication_Transcript R) :
    rp_Replication_R_specific (rp_Binary_annotate g) t = rp_Replication_firstHit (fun n => g t.1 = g (t.2.1 n)) ∧
      rp_Replication_R_null (rp_Binary_annotate g) t = rp_Replication_firstHit (fun n => g t.1 = g (t.2.2 n)) :=
  ⟨firstHit_congr (fun n => annotate_rel g t.1 (t.2.1 n)),
    firstHit_congr (fun n => annotate_rel g t.1 (t.2.2 n))⟩

/-! ## The Pearson collision payment -/

/- Invalid critics do not run. A mismatch uses no null-search result.
Only a nonterminating invoked search receives the zero extension. -/


theorem pearson_mismatch {R : Type} (c : Critic R) (hc : rp_Binary_Valid c)
    (t : rp_Replication_Transcript R) (h : ¬ rp_Binary_Rel c t.1 (t.2.1 0)) :
    rp_Replication_W_chiSquared c t = -1 := by
  simp [ hc, h]

theorem pearson_match {R : Type} (c : Critic R) (hc : rp_Binary_Valid c)
    (t : rp_Replication_Transcript R) (h : rp_Binary_Rel c t.1 (t.2.1 0))
    (hn : rp_Replication_R_null c t ≠ ⊤) :
    rp_Replication_W_chiSquared c t = (rp_Replication_R_null c t).toNat - 1 := by
  simp only [if_pos hc, if_pos h, if_neg hn]

/-! ## The KL two-clock payment -/



theorem H_zero : rp_Replication_H 0 = 0 := by simp []

/- Both invoked clocks must terminate. H uses the number of failures,
whereas the clocks themselves count calls including the success. -/


theorem invalid_payments {R : Type} (c : Critic R) (hc : ¬ rp_Binary_Valid c)
    (t : rp_Replication_Transcript R) :
    rp_Replication_W_chiSquared c t = 0 ∧ rp_Replication_W_KL c t = 0 := by
  simp [ hc]

/-- Relabeling types without changing their equality relation changes neither
critic nor clock nor payment. This is equality on all potential transcripts. -/
theorem representation_independent {R B C : Type}
    (g : R → B) (h : R → C) (he : rp_Binary_annotate g = rp_Binary_annotate h) (t : rp_Replication_Transcript R) :
    rp_Replication_R_specific (rp_Binary_annotate g) t = rp_Replication_R_specific (rp_Binary_annotate h) t ∧
      rp_Replication_R_null (rp_Binary_annotate g) t = rp_Replication_R_null (rp_Binary_annotate h) t ∧
      rp_Replication_W_chiSquared (rp_Binary_annotate g) t = rp_Replication_W_chiSquared (rp_Binary_annotate h) t ∧
      rp_Replication_W_KL (rp_Binary_annotate g) t = rp_Replication_W_KL (rp_Binary_annotate h) t := by
  rw [he]
  exact ⟨rfl, rfl, rfl, rfl⟩

end MutualEvaluation.Replication
end