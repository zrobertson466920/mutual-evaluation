import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.Replication
import Mathlib.Probability.ProductMeasure

/-!
DRAFT — probability law for the authored replication experiment.
Not author-certified. No public declaration or manuscript passage is changed.

A fixed reported channel is used for every call. Infinite products describe
potential calls; the payment still uses only its invoked searches. Fresh tasks
are integrated out through P.bind k. Measures, rather than PMFs on streams,
are needed because the space of infinite transcripts need not be countable.

Measurable-space parameters are technical: on a finite report alphabet with
measurable singletons, every subset is measurable. No full-support assumption
is imposed.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open MeasureTheory
open Binary

variable {X R : Type} [MeasurableSpace R]

/- An independent stream of calls from one fixed report distribution. -/


instance iid_probability (p : PMF R) : IsProbabilityMeasure (rp_Replication_iid p) := by
  dsimp only
  infer_instance

/- Conditional on the anchored task, the anchor and the two streams are
independent. The null stream uses fresh tasks, already marginalized out. -/


instance conditionalTranscriptLaw_probability
    (P : PMF X) (k : Kernel X R) (x : X) :
    IsProbabilityMeasure (rp_Replication_conditionalTranscriptLaw P k x) := by
  dsimp only
  infer_instance

/- Sample x ∼ P, then the anchor and potential calls for that task.
Only reports, not the latent task or annotation labels, enter the transcript. -/


instance transcriptLaw_probability [Fintype X] (P : PMF X) (k : Kernel X R) :
    IsProbabilityMeasure (rp_Replication_transcriptLaw P k) := by
  constructor
  simp only [ Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one]
  simpa only [tsum_fintype] using P.tsum_coe

/-- Finite-prefix probabilities come from the actual independent call stream. -/
theorem iid_prefix (p : PMF R) (s : Finset ℕ) (E : ℕ → Set R)
    (hE : ∀ n ∈ s, MeasurableSet (E n)) :
    rp_Replication_iid p (Set.pi (s : Set ℕ) E) = ∏ n ∈ s, p.toMeasure (E n) :=
  Measure.infinitePi_pi _ hE

/-! ## Channel-level evaluation scores

These are definitions of expectations, not integrability or unbiasedness
theorems. The latter remain separate proof obligations.
-/





/- The full binary critic space is retained; validity is handled by payment. -/












theorem invalid_scores_impl [Fintype X] (c : Critic R) (hc : ¬ rp_Binary_Valid c)
    (P : PMF X) (k : Kernel X R) :
    rp_Replication_u_chiSquared c P k = 0 ∧ rp_Replication_u_KL c P k = 0 := by
  simp [ hc]

end MutualEvaluation.Replication
end