import Mathlib
noncomputable section -- needed for sSup
namespace MutualEvaluation

/- The kernel of a belief is an affect. A kernel affects a belief over return values.
The shape of an outcome is two pairs of returns. -/
abbrev Kernel (A B : Type) := A → PMF B
abbrev Outcome (R : Type) := (R × R) × (R × R)

/- We can independently sample from two beliefs to obtain a belief over pairs. -/
def pair {A B : Type} (p : PMF A) (q : PMF B) : PMF (A × B) :=
  p.bind fun a => q.map fun b => (a, b)

/- Expected evaluation score. -/
structure Score (R Θ : Type) where
  S : Finset ℝ
  nonempty : S.Nonempty
  u : (R × R → S) → Θ → ℝ

def Score.envelope {R Θ : Type} (U : Score R Θ) (θ : Θ) : ℝ :=
  sSup (Set.range fun c => U.u c θ)

/- A mutual evaluation game has an evaluation type `X` and a return type `R`.
The game has a belief `P` over evaluations. Each evaluation affects two return
beliefs through the kernels `w 0` and `w 1`. Two workers interface with the game
through those kernels.
The game also has a non-empty finite set `S` of possible values. A critic rule
`c : R × R → S` assigns one of these values to each pair of returns. Finally,
the game has an evaluation score `u` that assigns a real-valued score using the rule
and an outcome law. One evaluator interfaces with the game through
a critic rule. -/
structure Game (X R : Type) where
  P : PMF X
  w : Fin 2 → Kernel X R
  S : Finset ℝ
  nonempty : S.Nonempty
  u : (R × R → S) → PMF (Outcome R) → ℝ

/- We make the evaluation and return type available when subsequent declarations
depend on them. -/
variable {X R : Type} (G : Game X R)

def Game.toScore (G : Game X R) : Score R (PMF (Outcome R)) :=
  ⟨G.S, G.nonempty, G.u⟩

/- How are outcomes generated? The workers have a strategy profile `σ` that
consists of two additional kernels that affect returns. Each `σ i` affects a raw
return to a return belief. -/
def law (σ : Fin 2 → Kernel R R) : PMF (Outcome R) :=
  G.P.bind fun x =>
    let p := (G.w 0 x).bind (σ 0)
    let q := (G.w 1 x).bind (σ 1)
    pair (pair p p) (pair q q)

/- We `bind` the raw return through the strategy kernel to obtain the return
beliefs, i.e. what workers believe they will return. We then independently sample
twice from each belief and return an outcome. A truthful strategy returns a
point mass at the raw return. -/
def truth : Fin 2 → Kernel R R := fun _ => PMF.pure

/- A deviation replaces a kernel; garbling post-processes it. -/
def deviate (σ : Fin 2 → Kernel R R) (i : Fin 2) (τ : Kernel R R) :=
  Function.update σ i τ

def garble (σ : Fin 2 → Kernel R R) (i : Fin 2) (τ : Kernel R R) :=
  deviate σ i (fun a => (σ i a).bind τ)

/- Given an outcome belief, we may calculate the critic envelope. -/
def V (ρ : PMF (Outcome R)) : ℝ :=
  G.toScore.envelope ρ

/- A joint belief is independent if it factors into its parts. -/
def independent {A B : Type} (p : PMF (A × B)) : Prop :=
  ∀ a b, p (a, b) = (p.map Prod.fst) a * (p.map Prod.snd) b

/- We declare a joint marginal of the outcome, pairing one replica from each worker. -/
def cross (ρ : PMF (Outcome R)) : PMF (R × R) :=
  ρ.map fun r => (r.1.1, r.2.2)

/- Given an outcome belief, we may ask what happens if the first worker applies
a further strategy. This produces a new outcome belief `ν`.
We say the game is robust at worker `i` if further garbling of that worker's
reporting kernel weakly decreases the envelope. Moreover, if the cross marginal
is dependent and becomes independent, the envelope must strictly decrease. -/
def robustAt (i : Fin 2) : Prop :=
  ∀ (σ : Fin 2 → Kernel R R) (τ : Kernel R R),
    let ν := law G (garble σ i τ)
    let ρ := law G σ
    V G ν ≤ V G ρ ∧
      (¬ independent (cross ρ) → independent (cross ν) → V G ν < V G ρ)

/- The original robustness condition concerns worker `0`. -/
def robust : Prop :=
  robustAt G 0

/- Both workers satisfy the robustness condition. -/
def robustBoth : Prop :=
  ∀ i, robustAt G i

/- We say a game with strategy profile `(σ,c)` satisfies Nash equilibrium if for
all evaluator rules `d` the evaluation score is no greater than under `c`,
and for all workers `i` and return kernels `τ` the evaluation score after the unilateral
deviation `τ` is no greater than without it. -/
def nash (σ : Fin 2 → Kernel R R) (c : R × R → G.S) : Prop :=
  (∀ d, G.u d (law G σ) ≤ G.u c (law G σ)) ∧
    ∀ i τ, G.u c (law G (deviate σ i τ)) ≤ G.u c (law G σ)

/- The game model we are interested in has a finite set of evaluations and return
values. This is an extension of the game above. The joint alphabet is assumed to
have finite cardinality greater than two and at most `K`. The robust property
must hold. -/
structure Model (X R : Type) [Fintype X] [Fintype R] (K : ℕ) extends Game X R where
  alphabet : 3 ≤ Fintype.card (R × R) ∧ Fintype.card (R × R) ≤ K
  robustness : robust toGame

/- The term `toGame` is the automatically generated projection from a `Model`
to the `Game` that it extends. -/
end MutualEvaluation
end