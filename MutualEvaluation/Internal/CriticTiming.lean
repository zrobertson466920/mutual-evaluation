import MutualEvaluation.Public.CriticTiming
import MutualEvaluation.Internal.Transfer

/-!
INTERNAL — supporting timing consequences.
The selected definitions and theorem declarations now live as Lean code in
Public/CriticTiming. This module imports it and downstream transfer support;
it does not redeclare them or maintain a second copy of their annotations.
-/

noncomputable section
namespace MutualEvaluation.Timing
open Abstract Binary Probability

section General
variable {X R : Type} (G : Game X R)

/-- Actual-law attainment, as an immediate consequence of public regret attainment. -/
theorem reoptimized_attained [Fintype R] (ν : PMF (Outcome R)) :
    ∃ d : R × R → G.S, CA G d ν = VPP G ν ∧ regret G d ν = 0 := by
  obtain ⟨d, hd⟩ := regret_attained G ν
  exact ⟨d, (regret_zero_iff G d ν).1 hd, hd⟩

/-- The public committed-loss identity specialized to the truthful reference law. -/
theorem timing_loss (c : R × R → G.S)
    (hc : G.u c (truthLaw G) = V G (truthLaw G)) (ν : PMF (Outcome R)) :
    CA G c (truthLaw G) - CA G c ν =
      (VPP G (truthLaw G) - VPP G ν) + regret G c ν :=
  committed_loss G c (truthLaw G) ν hc

end General

namespace CAVPP.Example

/-- The public table's agreement critic satisfies truthful-law optimality. -/
theorem agreement_optimal :
    G.u agreement (truthLaw G) = V G (truthLaw G) :=
  timing_table.1.trans timing_table.2.2.1.symm

theorem truthful_nash : nash G truth agreement :=
  truthful_nash_of_value_maximal G (guarantees prior workers).2 agreement
    agreement_optimal

end CAVPP.Example
end MutualEvaluation.Timing
end
