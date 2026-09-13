import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.FiniteTaskInformation

/-!
INTERNAL / DRAFT — finite-task Pearson information under stochastic reporting.
Exact loss follows from weighted posterior variance. No replication law,
expected-payment identity, or full-support assumption is used.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.FiniteTask
open Probability _root_.MutualEvaluation.Fiber
attribute [local instance] Classical.propDecidable

variable {X R B : Type}

theorem annotated_comp {C : Type} (k : Kernel X R) (g : R → B) (h : B → C) :
    rp_FiniteTask_annotated (rp_FiniteTask_annotated k g) h = rp_FiniteTask_annotated k (h ∘ g) := by
  funext x
  simp only [ PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

variable (P : PMF X) (k : Kernel X R) (τ : Kernel R B)

private def transport (ab : R × B) : ℝ :=
  rp_FiniteTask_reportMass P k ab.1 * mass (τ ab.1) ab.2

private theorem transport_nonneg (ab : R × B) : 0 ≤ transport P k τ ab :=
  mul_nonneg (reportMass_nonneg P k ab.1) (mass_nonneg (τ ab.1) ab.2)

variable [Fintype X] [Fintype R] [Fintype B]

private theorem push_snd (w : R × B → ℝ) (b : B) :
    push Prod.snd w b = ∑ a, w (a, b) := by
  simp [push, Fintype.sum_prod_type]

omit [Fintype X] in
private theorem transport_sum (h : R → ℝ) :
    ∑ ab, transport P k τ ab * h ab.1 = ∑ a, rp_FiniteTask_reportMass P k a * h a := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ b, rp_FiniteTask_reportMass P k a * mass (τ a) b * h a) = _
  calc
    _ = (rp_FiniteTask_reportMass P k a * h a) * ∑ b, mass (τ a) b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [mass_sum, mul_one]

omit [Fintype X] in
private theorem transport_push (b : B) :
    push Prod.snd (transport P k τ) b =
      rp_FiniteTask_reportMass P (fun x => (k x).bind τ) b := by
  rw [push_snd]
  change (∑ a, mass (P.bind k) a * mass (τ a) b) = _
  simpa only [ PMF.bind_bind] using
    (mass_bind (P.bind k) τ b).symm

private theorem transport_mean (b : B) (x : X) :
    mean Prod.snd (transport P k τ) (fun ab => rp_FiniteTask_posterior P k ab.1 x) b =
      rp_FiniteTask_posterior P (fun z => (k z).bind τ) b x := by
  have hn :
      push Prod.snd (fun ab : R × B =>
        transport P k τ ab * rp_FiniteTask_posterior P k ab.1 x) b =
          rp_FiniteTask_jointMass P (fun z => (k z).bind τ) x b := by
    rw [push_snd]
    calc
      _ = ∑ a, rp_FiniteTask_jointMass P k x a * mass (τ a) b := by
        apply Finset.sum_congr rfl
        intro a _
        dsimp only [transport]
        rw [mul_right_comm, weighted_posterior]
      _ = _ := by
        simp only [ mass_bind, Finset.mul_sum, mul_assoc]
  rw [mean, hn, transport_push]

/-- Exact loss under a stochastic channel, with possibly different alphabets.
Zero-mass tasks, inputs, and outputs require no separate support hypothesis. -/
theorem pearson_processing_loss :
    rp_FiniteTask_pearson P k - rp_FiniteTask_pearson P (fun x => (k x).bind τ) =
      ∑ x, (∑ a, ∑ b, rp_FiniteTask_reportMass P k a * mass (τ a) b *
        (rp_FiniteTask_posterior P k a x - rp_FiniteTask_posterior P (fun z => (k z).bind τ) b x)^2) /
          mass P x := by
  rw [pearson_eq_posterior, pearson_eq_posterior, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have h := decomposition Prod.snd (transport P k τ)
    (fun ab => rp_FiniteTask_posterior P k ab.1 x) (transport_nonneg P k τ) (mass P x)
  rw [transport_sum P k τ (fun a => (rp_FiniteTask_posterior P k a x - mass P x)^2)] at h
  simp only [transport_push, transport_mean, Fintype.sum_prod_type, transport] at h
  rw [h, add_div]
  ring

theorem pearson_data_processing :
    rp_FiniteTask_pearson P (fun x => (k x).bind τ) ≤ rp_FiniteTask_pearson P k := by
  apply sub_nonneg.mp
  rw [pearson_processing_loss]
  apply Finset.sum_nonneg
  intro x _
  apply div_nonneg _ (mass_nonneg P x)
  apply Finset.sum_nonneg
  intro a _
  exact Finset.sum_nonneg (fun b _ =>
    mul_nonneg
      (mul_nonneg (reportMass_nonneg P k a) (mass_nonneg (τ a) b))
      (sq_nonneg _))

omit [Fintype R] in
/-- Deterministic coarsening of the critic's annotation classes. -/
theorem pearson_annotation_coarsen {C : Type} [Fintype C]
    (g : R → B) (h : B → C) :
    rp_FiniteTask_pearson P (rp_FiniteTask_annotated k (h ∘ g)) ≤ rp_FiniteTask_pearson P (rp_FiniteTask_annotated k g) := by
  rw [← annotated_comp]
  exact pearson_annotation_mono P (rp_FiniteTask_annotated k g) h

end MutualEvaluation.FiniteTask
end