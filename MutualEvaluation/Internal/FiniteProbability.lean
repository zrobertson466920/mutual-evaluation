import MutualEvaluation.Internal.FiniteProbabilityProofs
import MutualEvaluation.Public.CriticTiming

/-!
INTERNAL — downstream probability entry point.
The original mass-lemma signatures are preserved here, stated using the public
Probability.mass definition. Their proofs use the expanded-expression helpers
in FiniteProbabilityProofs, which has no dependency on Public/CriticTiming.
Pair post-processing and law identities retain their original upstream names.
No primitive probability definition is duplicated.
-/

noncomputable section
namespace MutualEvaluation.Probability

theorem mass_nonneg {A : Type} (p : PMF A) (a : A) : 0 ≤ mass p a :=
  Proofs.mass_nonneg p a

theorem mass_le_one {A : Type} (p : PMF A) (a : A) : mass p a ≤ 1 :=
  Proofs.mass_le_one p a

theorem mass_sum {A : Type} [Fintype A] (p : PMF A) : ∑ a, mass p a = 1 :=
  Proofs.mass_sum p

theorem mass_bind {A B : Type} [Fintype A] (p : PMF A) (k : Kernel A B) (b : B) :
    mass (p.bind k) b = ∑ a, mass p a * mass (k a) b :=
  Proofs.mass_bind p k b

theorem mass_pure {A : Type} [DecidableEq A] (a b : A) :
    mass (PMF.pure a) b = if b = a then 1 else 0 :=
  Proofs.mass_pure a b

theorem mass_pair {A B : Type} [Fintype A] [Fintype B]
    (p : PMF A) (q : PMF B) (a : A) (b : B) :
    mass (pair p q) (a, b) = mass p a * mass q b :=
  Proofs.mass_pair p q a b

theorem independent_iff_mass {A B : Type} (μ : PMF (A × B)) :
    independent μ ↔ ∀ a b,
      mass μ (a, b) = mass (μ.map Prod.fst) a * mass (μ.map Prod.snd) b :=
  Proofs.independent_iff_mass μ

theorem mass_post {A B C D : Type} [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] (μ : PMF (A × B)) (κ : Kernel A C) (η : Kernel B D)
    (c : C) (d : D) :
    mass (post μ κ η) (c, d) =
      ∑ a, ∑ b, mass μ (a, b) * mass (κ a) c * mass (η b) d :=
  Proofs.mass_post μ κ η c d

end MutualEvaluation.Probability
end
