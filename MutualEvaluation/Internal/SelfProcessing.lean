import MutualEvaluation.Internal.SelfInformation
import MutualEvaluation.Internal.FiberVariance

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-!
# Fair-binary information under stochastic reporting

The report alphabets may differ and need not have full support. The exact
information loss is a weighted posterior variance under the reporting kernel.
This is finite-channel algebra, not a replication-loop or Core robustness proof.
-/

noncomputable section
namespace MutualEvaluation.Self
open Probability _root_.MutualEvaluation.Fiber
attribute [local instance] Classical.propDecidable

variable {R B : Type} [Fintype R] [Fintype B]
  (k : Kernel Bool R) (τ : Kernel R B)

private def transport (ab : R × B) : ℝ :=
  reportMass k ab.1 * mass (τ ab.1) ab.2

omit [Fintype R] [Fintype B] in
private theorem transport_nonneg (ab : R × B) : 0 ≤ transport k τ ab :=
  mul_nonneg (reportMass_nonneg k ab.1) (mass_nonneg (τ ab.1) ab.2)

private theorem push_snd (w : R × B → ℝ) (b : B) :
    push Prod.snd w b = ∑ a, w (a, b) := by
  simp [push, Fintype.sum_prod_type]

private theorem transport_sum (h : R → ℝ) :
    ∑ ab, transport k τ ab * h ab.1 = ∑ a, reportMass k a * h a := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ b, reportMass k a * mass (τ a) b * h a) = _
  calc
    _ = (reportMass k a * h a) * ∑ b, mass (τ a) b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [mass_sum, mul_one]

private theorem transport_push (b : B) :
    push Prod.snd (transport k τ) b = reportMass (fun x => (k x).bind τ) b := by
  rw [push_snd]
  simp only [transport, reportMass, mass_bind, add_div, add_mul,
    div_mul_eq_mul_div, Finset.sum_add_distrib, Finset.sum_div]

private theorem transport_mean (b : B) :
    mean Prod.snd (transport k τ) (fun ab => posterior k ab.1) b =
      posterior (fun x => (k x).bind τ) b := by
  have hn :
      push Prod.snd (fun ab : R × B => transport k τ ab * posterior k ab.1) b =
        mass ((k true).bind τ) b / 2 := by
    rw [push_snd, mass_bind, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    dsimp [transport]
    rw [mul_right_comm, weighted_posterior]
    ring
  rw [mean, hn, transport_push]
  dsimp [posterior, reportMass]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Posterior variance lost by any stochastic reporting channel.
Null input/output atoms contribute zero, without a support assumption. -/
theorem information_loss :
    information k - information (fun x => (k x).bind τ) =
      4 * ∑ a, ∑ b, reportMass k a * mass (τ a) b *
        (posterior k a - posterior (fun x => (k x).bind τ) b)^2 := by
  have h := decomposition Prod.snd (transport k τ) (fun ab => posterior k ab.1)
    (transport_nonneg k τ) (1 / 2)
  rw [transport_sum k τ (fun a => (posterior k a - 1 / 2)^2)] at h
  simp only [transport_push, transport_mean, Fintype.sum_prod_type, transport] at h
  unfold information
  linarith

theorem information_data_processing :
    information (fun x => (k x).bind τ) ≤ information k := by
  have h := information_loss k τ
  have hn := loss_nonneg Prod.snd (transport k τ) (fun ab => posterior k ab.1)
    (transport_nonneg k τ)
  simp only [transport_mean, Fintype.sum_prod_type, transport] at hn
  linarith

end MutualEvaluation.Self
end