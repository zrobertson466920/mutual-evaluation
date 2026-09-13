import MutualEvaluation.Internal.TimingInstanceProofs

/-! # Critic timing: CA and VPP -/

noncomputable section
namespace MutualEvaluation

/-! ## D1 — Truthful-law selection, timing scores, and transfer -/

namespace Timing
open Abstract
section General

/- AUTHOR-PROSE-01
The correlated agreement (CA) and variational peer-prediction (VPP) mechanisms illustrate how in the mutual evaluation game they have the same evaluation task type and envelope, but different critic regrets. The comparison assumes perfect access to the outcome law to illustrate timing effects in a simple setting. Other mutual evaluation mechanisms with a sample-aware implementation are considered in the following section.
-/

/- AUTHOR-PROSE-02
In the **CA timing**, the critic rule is selected assuming truthful reporting and then held fixed. In the **VPP timing**, the critic rule is reoptimized based on the actual outcome law. Write $\rho_* := \text{law}_G(\text{truth})$. For finite $R$, it is possible to choose a critic $c_*$ that is optimal at $\rho_*$.
-/

variable {X R : Type} (G : Game X R)

def truthLaw : PMF (Outcome R) := law G truth

theorem truth_attained [Fintype R] :
    ∃ c : R × R → G.S, G.u c (truthLaw G) = V G (truthLaw G) := by
  obtain ⟨c, hc⟩ := regret_attained G (truthLaw G)
  exact ⟨c, (regret_zero_iff G c (truthLaw G)).1 hc⟩

def CA (c : R × R → G.S) (ν : PMF (Outcome R)) : ℝ := G.u c ν
def VPP (ν : PMF (Outcome R)) : ℝ := V G ν


/- AUTHOR-PROSE-03
If the actual outcome law shifts to $\nu$ then the two timings generate evaluation scores that agree at truth.
-/

theorem at_truth (c : R × R → G.S)
    (hc : G.u c (truthLaw G) = V G (truthLaw G)) :
    CA G c (truthLaw G) = VPP G (truthLaw G) := hc


/- AUTHOR-PROSE-04
We can write this as:
$$
U_{\text{CA}}(\nu) := u(c_*, \nu), \quad U_{\text{VPP}}(\nu) := V(\nu).
$$
They agree at truth. In general, the payoff difference is the critic regret of CA.
-/

theorem timing_gap (c : R × R → G.S) (ν : PMF (Outcome R)) :
    VPP G ν - CA G c ν = regret G c ν := rfl


end General
end Timing

namespace Abstract
variable {X R : Type} (G : Game X R)

/- AUTHOR-PROSE-05
The committed-loss identity makes critic timing relevant. Suppose the critic starts as optimal. Robustness says additional garbling of the primary worker's completion belief induces a weak evaluation score loss. If we have robustness for both workers the payoffs also (weakly) decrease. The global comparison below assumes truthful value maximality.
-/

def truthValueMaximal : Prop :=
  ∀ σ, V G (law G σ) ≤ V G (law G truth)

theorem truthful_global_optimal [Fintype R] (h : truthValueMaximal G)
    (c : R × R → G.S) (hc : G.u c (law G truth) = V G (law G truth))
    (d : R × R → G.S) (σ : Fin 2 → Kernel R R) :
    G.u d (law G σ) ≤ G.u c (law G truth) := by
  rw [hc]
  exact (sub_nonneg.mp (regret_nonneg G d (law G σ))).trans (h σ)


/- AUTHOR-PROSE-06
So $(\text{truth}, c)$ jointly maximizes common payoff and is Nash.
-/

end Abstract

/-! ## D2 — Shared Boolean objective, envelope, and regret -/

/- AUTHOR-PROSE-07
**A simple Boolean objective.** For a concrete comparison we take $R = \lbrace 0, 1 \rbrace$ and specialize to CA and VPP with Total Variation divergence where it is known an optimal critic exists with $S = \lbrace 0, 1 \rbrace.$
-/

namespace Binary

def scores : Finset ℝ := {0, 1}
abbrev Critic (R : Type) := R × R → scores

end Binary

namespace Probability

def mass {A : Type} (p : PMF A) (a : A) : ℝ := (p a).toReal

end Probability

open Abstract Binary Probability

namespace Timing.CAVPP

/- AUTHOR-PROSE-08
Intuitively, the CA mechanism's critic regret can change when the outcome law shifts. However, the VPP mechanism allows ex post reoptimization which removes the regret term.
-/

/- AUTHOR-PROSE-09
The CA mechanism is then instantiated using the cross outcome law; the objective $J$ is a joint-minus-product score.
-/

def μ (ρ : PMF (Outcome Bool)) : PMF (Bool × Bool) := cross ρ
def π (ρ : PMF (Outcome Bool)) : PMF (Bool × Bool) :=
  pair ((μ ρ).map Prod.fst) ((μ ρ).map Prod.snd)

def T (ρ : PMF (Outcome Bool)) : ℝ :=
  (1 / 2) * ∑ p, |mass (μ ρ) p - mass (π ρ) p|

def J (c : Critic Bool) (ρ : PMF (Outcome Bool)) : ℝ :=
  (∑ p, mass (μ ρ) p * (c p : ℝ)) -
    ∑ p, mass (π ρ) p * (c p : ℝ)


/- AUTHOR-PROSE-10
The VPP mechanism, because the optimal critic is an element of the set of all binary critics, can be instantiated with:
-/

theorem variational_TV (ρ : PMF (Outcome Bool)) :
    (∀ c : Critic Bool, J c ρ ≤ T ρ) ∧ ∃ c : Critic Bool, J c ρ = T ρ := by
  have J_eq (c : Critic Bool) (ν : PMF (Outcome Bool)) :
      J c ν = Timing.J c (cross ν) := by
    simp only [J, π, μ, Timing.J, mass, Fintype.sum_prod_type, Probability.Proofs.mass_pair]
  have T_eq (ν : PMF (Outcome Bool)) :
      T ν = Boolean.TV (cross ν) := by
    simp only [T, π, μ, mass, Probability.Proofs.mass_pair, Boolean.TV, Fintype.sum_prod_type]
  obtain ⟨hu, ha⟩ := Timing.variational_TV (cross ρ)
  constructor
  · intro c
    exact (J_eq c ρ).trans_le ((hu c).trans_eq (T_eq ρ).symm)
  · obtain ⟨c, hc⟩ := ha
    refine ⟨c, ?_⟩
    exact (J_eq c ρ).trans (hc.trans (T_eq ρ).symm)


/- AUTHOR-PROSE-11
The conclusion is that the maximum of the shared objective $J$ equals the total variation distance $T$.
-/

/- AUTHOR-PROSE-12
**A worked example.** The game is instantiated using the critic rule and the shared objective $J$ for any task prior $P$ and two Boolean-report worker completion channels $f$.
-/

variable {X : Type} (P : PMF X) (f : Fin 2 → Kernel X Bool)

def game : Game X Bool where
  P := P
  w := f
  S := scores
  nonempty := by simp [scores]
  u := fun c ρ => 1 + J c ρ / 2


/- AUTHOR-PROSE-13
The VPP score is $1+T/2$, and the CA score is this value minus critic regret $(T-J)/2$. This holds for any outcome law. The game is an instance of mutual evaluation: it satisfies robustness. Finally, truth maximizes its value over all reporting profiles.
-/

theorem value (ρ : PMF (Outcome Bool)) :
    VPP (game P f) ρ = 1 + T ρ / 2 := by
  have game_eq_mediated : game P f = mediatedGame P f := by
    unfold game mediatedGame bonusGame scores
    simp only [J, π, μ, Timing.J, mass, Fintype.sum_prod_type, Probability.Proofs.mass_pair]
  have T_eq : T ρ = Boolean.TV (cross ρ) := by
    simp only [T, π, μ, mass, Probability.Proofs.mass_pair, Boolean.TV, Fintype.sum_prod_type]
  simpa only [VPP, game_eq_mediated, T_eq] using (Timing.values P f ρ).2

theorem regret_formula (c : Critic Bool) (ρ : PMF (Outcome Bool)) :
    regret (game P f) c ρ = (T ρ - J c ρ) / 2 := by
  change VPP (game P f) ρ - (1 + J c ρ / 2) = _
  rw [value]
  ring

theorem guarantees : robust (game P f) ∧ truthValueMaximal (game P f) := by
  have game_eq_mediated : game P f = mediatedGame P f := by
    unfold game mediatedGame bonusGame scores
    simp only [J, π, μ, Timing.J, mass, Fintype.sum_prod_type, Probability.Proofs.mass_pair]
  rw [game_eq_mediated]
  exact ⟨(Timing.robust_games P f).2, (Timing.truth_value_maximal P f).2⟩


/-! ## D3 — Fair-bit timing table -/

namespace Example

/- AUTHOR-PROSE-14
In this instance, sample a uniform Boolean bit and consider two truthful workers generating the outcome law $\rho_*$. Now let $\nu$ denote the outcome law when only the first worker flips its bit. Choose the agreement critic
$$
c_{=}(a,b) := \mathbf{1} \lbrace a = b \rbrace.
$$
-/

def prior : PMF Bool := PMF.uniformOfFintype Bool
def workers : Fin 2 → Kernel Bool Bool := fun _ => PMF.pure
abbrev G : Game Bool Bool := game prior workers
def agreement : Critic Bool := fun p =>
  if p.1 = p.2 then ⟨1, by simp [scores]⟩ else ⟨0, by simp [scores]⟩
def flip : Kernel Bool Bool := fun b => PMF.pure (!b)
def changed : PMF (Outcome Bool) := law G (Function.update truth 0 flip)


/- AUTHOR-PROSE-15
The score and valuation calculation yields
-/

theorem timing_table :
    CA G agreement (truthLaw G) = 5 / 4 ∧ CA G agreement changed = 3 / 4 ∧
      VPP G (truthLaw G) = 5 / 4 ∧ VPP G changed = 5 / 4 := by
  have J_eq (c : Critic Bool) (ν : PMF (Outcome Bool)) :
      J c ν = Timing.J c (cross ν) := by
    simp only [J, π, μ, Timing.J, mass, Fintype.sum_prod_type, Probability.Proofs.mass_pair]
  have game_eq_mediated (P : PMF Bool) (f : Fin 2 → Kernel Bool Bool) :
      game P f = mediatedGame P f := by
    unfold game mediatedGame bonusGame scores
    simp only [J, π, μ, Timing.J, mass, Fintype.sum_prod_type, Probability.Proofs.mass_pair]
  have hagree : agreement = Timing.agree := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 1 + J agreement (truthLaw G) / 2 = _
    rw [J_eq, hagree]
    exact Timing.Example.payoff_table.2.2.1
  · change 1 + J agreement changed / 2 = _
    rw [J_eq, hagree]
    exact Timing.Example.payoff_table.2.2.2
  · change V (game prior workers) (truthLaw G) = _
    rw [game_eq_mediated]
    exact Timing.Example.value_table.2.2.1
  · change V (game prior workers) changed = _
    rw [game_eq_mediated]
    exact Timing.Example.value_table.2.2.2


/- AUTHOR-PROSE-16
So the same critic is initially optimal under both payoffs. However, the bit flip preserves the envelope not the evaluation score. The payoff under CA falls from $5/4$ to $3/4$ while only reoptimized VPP maintains the envelope.
-/

end Example
end Timing.CAVPP
end MutualEvaluation
end
