import MutualEvaluation.Internal.TimingPayoffProofs
import MutualEvaluation.Internal.Transfer
import MutualEvaluation.Internal.CriticQuotient

/-!
INTERNAL — downstream payoff entry point and equilibrium consequence.
TimingPayoffProofs supplies the calculations using expanded Core expressions,
without depending on Public/CriticTiming. This downstream module preserves the
existing entry point and adds the equilibrium corollary through public transfer.
No annotation or primitive definition is duplicated here.
-/

noncomputable section
namespace MutualEvaluation.Timing
open Binary Boolean Probability Abstract
variable {X : Type} (P : PMF X) (f : Fin 2 → Kernel X Bool)

theorem truthful_equilibria :
    (∃ c, nash (bonusGame P f) truth c) ∧
      ∃ c, nash (mediatedGame P f) truth c :=
  ⟨Abstract.exists_truthful_nash _ (truth_value_maximal P f).1,
    Abstract.exists_truthful_nash _ (truth_value_maximal P f).2⟩

end MutualEvaluation.Timing
end
