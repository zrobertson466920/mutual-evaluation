import MutualEvaluation.Internal.SelfGame
import MutualEvaluation.Internal.SelfProcessing

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-!
# Truthful equilibrium for the fair-binary self game

Value maximality follows from stochastic task-information data processing.
The unused peer is indifferent. These results concern a fixed reporting kernel,
not strategies that change across calls in a sampling procedure.
-/

noncomputable section
namespace MutualEvaluation.Self
open Binary

variable {R : Type} [Fintype R] (f : Fin 2 → Kernel Bool R)

omit [Fintype R] in
private theorem reported_truth : reported f truth = f 0 := by
  funext x
  simp [reported, truth, PMF.bind_pure]

theorem truth_value_maximal : Abstract.truthValueMaximal (game f) := by
  intro σ
  rw [value f σ, value f truth, reported_truth f]
  exact information_data_processing (f 0) (σ 0)

/-- Any critic optimal at truth bounds all simultaneous critic/reporting changes. -/
theorem truthful_global_optimal (c : Critic R)
    (hc : (game f).u c (law (game f) truth) = V (game f) (law (game f) truth))
    (d : Critic R) (σ : Fin 2 → Kernel R R) :
    (game f).u d (law (game f) σ) ≤ (game f).u c (law (game f) truth) :=
  Abstract.truthful_global_optimal (game f) (truth_value_maximal f) c hc d σ

/-- Literal agreement is always optimal at truth; validity alone is not enough. -/
theorem truthful_nash (c : Critic R)
    (hc : (game f).u c (law (game f) truth) = V (game f) (law (game f) truth)) :
    nash (game f) truth c :=
  Abstract.truthful_nash_of_value_maximal (game f) (truth_value_maximal f) c hc

end MutualEvaluation.Self
end