import MutualEvaluation.Internal.TimingInstanceProofs
import MutualEvaluation.Internal.TimingPayoffs

/-!
INTERNAL — downstream timing-instance entry point.
The sample-payoff and fair-bit calculations are in TimingInstanceProofs,
upstream of the public interface. This module retains the existing truthful
Nash consequence, using the downstream transfer results.
-/

noncomputable section
namespace MutualEvaluation.Timing
open Binary Boolean Probability Abstract
namespace Example

/-- The same critic supports truth in both games before the reporting change. -/
theorem truthful_nash : nash bonus truth agree ∧ nash mediated truth agree := by
  constructor
  · exact Abstract.truthful_nash_of_value_maximal bonus
      (Timing.truth_value_maximal prior workers).1 agree
      (payoff_table.1.trans value_table.1.symm)
  · exact Abstract.truthful_nash_of_value_maximal mediated
      (Timing.truth_value_maximal prior workers).2 agree
      (payoff_table.2.2.1.trans value_table.2.2.1.symm)

end Example
end MutualEvaluation.Timing
end
