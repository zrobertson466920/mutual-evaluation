import MutualEvaluation.Public.Core

/-! Technical inspection of the annotated Core. This file is not an annotation. -/
open MutualEvaluation

#print Kernel
#print Outcome
#print pair
#print Score
#print Score.envelope
#print Game
#print Game.toScore
#print law
#print truth
#print deviate
#print garble
#print V
#print independent
#print cross
#print robustAt
#print robust
#print robustBoth
#print nash
#print Model

#print axioms Kernel
#print axioms Outcome
#print axioms pair
#print axioms Score
#print axioms Score.envelope
#print axioms Game
#print axioms Game.toScore
#print axioms law
#print axioms truth
#print axioms deviate
#print axioms garble
#print axioms V
#print axioms independent
#print axioms cross
#print axioms robustAt
#print axioms robust
#print axioms robustBoth
#print axioms nash
#print axioms Model

/-! Definitional compatibility with the original Core formulations.
These regression checks are technical tests, not new public declarations. -/
noncomputable section
namespace MutualEvaluation.CoreCompatibility
variable {X R : Type} (G : Game X R)

example (ρ : PMF (Outcome R)) :
    V G ρ = sSup (Set.range fun c => G.u c ρ) := rfl

example :
    robust G ↔
      ∀ (σ : Fin 2 → Kernel R R) (τ : Kernel R R),
        let ν := law G (Function.update σ 0 (fun a => (σ 0 a).bind τ))
        let ρ := law G σ
        V G ν ≤ V G ρ ∧
          (¬ independent (cross ρ) → independent (cross ν) → V G ν < V G ρ) :=
  Iff.rfl

example (σ : Fin 2 → Kernel R R) (c : R × R → G.S) :
    nash G σ c ↔
      (∀ d, G.u d (law G σ) ≤ G.u c (law G σ)) ∧
        ∀ i τ, G.u c (law G (Function.update σ i τ)) ≤ G.u c (law G σ) :=
  Iff.rfl

example (h : robustBoth G) : robust G := h 0

end MutualEvaluation.CoreCompatibility
end
