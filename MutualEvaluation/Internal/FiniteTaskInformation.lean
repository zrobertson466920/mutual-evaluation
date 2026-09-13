import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.FiniteProbability
import MutualEvaluation.Internal.FiberVariance

/-!
INTERNAL / DRAFT — finite-task information algebra.
No replication experiment, expected payment, or unbiasedness assumption occurs
in this module. In particular, pearson is not Replication.u_chiSquared.

The prior and report alphabet need not have full support. Real division assigns
zero to null-denominator terms; the required joint-mass domination is proved.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.FiniteTask
open Probability _root_.MutualEvaluation.Fiber
attribute [local instance] Classical.propDecidable

variable {X R B : Type}

/- Deterministic annotation of the reported channel, not a new worker strategy. -/


variable (P : PMF X) (k : Kernel X R)

/- Joint task/report mass under x ∼ P and a ∼ k x. -/




/- Task posterior at a report; zero at a null report. -/


/- The manuscript's Pearson information convention, as a finite sum.
This is a target information functional, not an expected loop payment. -/


theorem jointMass_nonneg (x : X) (a : R) : 0 ≤ rp_FiniteTask_jointMass P k x a :=
  mul_nonneg (mass_nonneg P x) (mass_nonneg (k x) a)

theorem reportMass_nonneg (a : R) : 0 ≤ rp_FiniteTask_reportMass P k a :=
  mass_nonneg (P.bind k) a

theorem reportMass_sum [Fintype R] : ∑ a, rp_FiniteTask_reportMass P k a = 1 :=
  mass_sum (P.bind k)

theorem reportMass_eq_sum [Fintype X] (a : R) :
    rp_FiniteTask_reportMass P k a = ∑ x, rp_FiniteTask_jointMass P k x a :=
  mass_bind P k a

theorem jointMass_sum_report [Fintype R] (x : X) :
    ∑ a, rp_FiniteTask_jointMass P k x a = mass P x := by
  simp only [ ← Finset.mul_sum, mass_sum, mul_one]

theorem jointMass_le_reportMass [Fintype X] (x : X) (a : R) :
    rp_FiniteTask_jointMass P k x a ≤ rp_FiniteTask_reportMass P k a := by
  rw [reportMass_eq_sum]
  exact Finset.single_le_sum (fun y _ => jointMass_nonneg P k y a)
    (Finset.mem_univ x)

theorem jointMass_zero_of_reportMass_zero [Fintype X]
    (x : X) (a : R) (ha : rp_FiniteTask_reportMass P k a = 0) :
    rp_FiniteTask_jointMass P k x a = 0 :=
  le_antisymm (ha ▸ jointMass_le_reportMass P k x a)
    (jointMass_nonneg P k x a)

/-- Null product-reference atoms have null joint mass. -/
theorem reference_dominated [Fintype X] (x : X) (a : R)
    (hz : mass P x * rp_FiniteTask_reportMass P k a = 0) :
    rp_FiniteTask_jointMass P k x a = 0 := by
  rcases mul_eq_zero.mp hz with hx | ha
  · simp [ hx]
  · exact jointMass_zero_of_reportMass_zero P k x a ha

theorem posterior_nonneg (a : R) (x : X) : 0 ≤ rp_FiniteTask_posterior P k a x :=
  div_nonneg (jointMass_nonneg P k x a) (reportMass_nonneg P k a)

theorem posterior_prior_zero (a : R) (x : X) (hx : mass P x = 0) :
    rp_FiniteTask_posterior P k a x = 0 := by
  simp [ hx]

/-- Bayes' multiplication identity, including null reports. -/
theorem weighted_posterior [Fintype X] (a : R) (x : X) :
    rp_FiniteTask_reportMass P k a * rp_FiniteTask_posterior P k a x = rp_FiniteTask_jointMass P k x a := by
  by_cases ha : rp_FiniteTask_reportMass P k a = 0
  · have hj := jointMass_zero_of_reportMass_zero P k x a ha
    simp [ha, hj]
  · dsimp only []
    field_simp

theorem posterior_sum [Fintype X] (a : R) (ha : 0 < rp_FiniteTask_reportMass P k a) :
    ∑ x, rp_FiniteTask_posterior P k a x = 1 := by
  simp only [ ← Finset.sum_div]
  rw [← reportMass_eq_sum, div_self (ne_of_gt ha)]

theorem weighted_posterior_sum [Fintype X] [Fintype R] (x : X) :
    ∑ a, rp_FiniteTask_reportMass P k a * rp_FiniteTask_posterior P k a x = mass P x := by
  simp_rw [weighted_posterior]
  exact jointMass_sum_report P k x

private theorem pearson_atom [Fintype X] (x : X) (a : R) :
    (rp_FiniteTask_jointMass P k x a)^2 / (mass P x * rp_FiniteTask_reportMass P k a) =
      rp_FiniteTask_reportMass P k a * (rp_FiniteTask_posterior P k a x - mass P x)^2 / mass P x +
        2 * rp_FiniteTask_jointMass P k x a - mass P x * rp_FiniteTask_reportMass P k a := by
  by_cases hx : mass P x = 0
  · simp [ hx]
  · by_cases ha : rp_FiniteTask_reportMass P k a = 0
    · have hj := jointMass_zero_of_reportMass_zero P k x a ha
      simp [ ha, hj]
    · dsimp only []
      field_simp
      ring

private theorem pearson_row [Fintype X] [Fintype R] (x : X) :
    (∑ a, (rp_FiniteTask_jointMass P k x a)^2 / (mass P x * rp_FiniteTask_reportMass P k a)) =
      (∑ a, rp_FiniteTask_reportMass P k a * (rp_FiniteTask_posterior P k a x - mass P x)^2) /
        mass P x + mass P x := by
  simp_rw [pearson_atom]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.mul_sum, mass_sum, mul_one]
  ring

/-- Pearson information is the prior-weighted posterior variation.
Null prior coordinates contribute zero, consistently with domination above. -/
theorem pearson_eq_posterior [Fintype X] [Fintype R] :
    rp_FiniteTask_pearson P k =
      ∑ x, (∑ a, rp_FiniteTask_reportMass P k a * (rp_FiniteTask_posterior P k a x - mass P x)^2) /
        mass P x := by
  dsimp only
  simp_rw [pearson_row]
  rw [Finset.sum_add_distrib, mass_sum]
  ring

theorem pearson_nonneg [Fintype X] [Fintype R] : 0 ≤ rp_FiniteTask_pearson P k := by
  rw [pearson_eq_posterior]
  apply Finset.sum_nonneg
  intro x _
  exact div_nonneg
    (Finset.sum_nonneg (fun a _ =>
      mul_nonneg (reportMass_nonneg P k a) (sq_nonneg _)))
    (mass_nonneg P x)

private theorem mass_map [Fintype R] (p : PMF R) (g : R → B) (b : B) :
    mass (p.map g) b = push g (mass p) b := by
  classical
  change mass (p.bind fun a => PMF.pure (g a)) b = _
  simp [mass_bind, mass_pure, push, mul_ite, eq_comm]

theorem annotated_reportMass [Fintype R] (g : R → B) (b : B) :
    rp_FiniteTask_reportMass P (rp_FiniteTask_annotated k g) b = push g (rp_FiniteTask_reportMass P k) b := by
  change mass (P.bind fun x => (k x).map g) b = _
  rw [← PMF.map_bind]
  exact mass_map (P.bind k) g b

theorem annotated_jointMass [Fintype R] (g : R → B) (x : X) (b : B) :
    rp_FiniteTask_jointMass P (rp_FiniteTask_annotated k g) x b = push g (rp_FiniteTask_jointMass P k x) b := by
  simp only [ mass_map, push, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

/-- Annotation posteriors are weighted means of the report posteriors.
This identity also holds on empty and zero-mass annotation classes. -/
theorem annotated_posterior [Fintype X] [Fintype R] (g : R → B) (b : B) (x : X) :
    rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) b x =
      mean g (rp_FiniteTask_reportMass P k) (fun a => rp_FiniteTask_posterior P k a x) b := by
  have hn : (fun a => rp_FiniteTask_reportMass P k a * rp_FiniteTask_posterior P k a x) =
      rp_FiniteTask_jointMass P k x := by
    funext a
    exact weighted_posterior P k a x
  change rp_FiniteTask_jointMass P (rp_FiniteTask_annotated k g) x b /
      rp_FiniteTask_reportMass P (rp_FiniteTask_annotated k g) b = _
  rw [annotated_jointMass, annotated_reportMass, mean, hn]

/-- Exact information lost by deterministic annotation.
This is a finite-sum identity, not yet a formula for replication-score regret. -/
theorem pearson_annotation_loss [Fintype X] [Fintype R] [Fintype B] (g : R → B) :
    rp_FiniteTask_pearson P k - rp_FiniteTask_pearson P (rp_FiniteTask_annotated k g) =
      ∑ x, (∑ a, rp_FiniteTask_reportMass P k a *
        (rp_FiniteTask_posterior P k a x - rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) x)^2) /
          mass P x := by
  rw [pearson_eq_posterior, pearson_eq_posterior, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have h := decomposition g (rp_FiniteTask_reportMass P k) (fun a => rp_FiniteTask_posterior P k a x)
    (reportMass_nonneg P k) (mass P x)
  simp_rw [annotated_posterior]
  simp_rw [annotated_reportMass]
  rw [h, add_div]
  ring

theorem pearson_annotation_mono [Fintype X] [Fintype R] [Fintype B] (g : R → B) :
    rp_FiniteTask_pearson P (rp_FiniteTask_annotated k g) ≤ rp_FiniteTask_pearson P k := by
  apply sub_nonneg.mp
  rw [pearson_annotation_loss]
  apply Finset.sum_nonneg
  intro x _
  exact div_nonneg
    (Finset.sum_nonneg (fun a _ =>
      mul_nonneg (reportMass_nonneg P k a) (sq_nonneg _)))
    (mass_nonneg P x)

/-- Zero annotation loss is exactly preservation of the whole task posterior
at every positive-mass report. Null prior coordinates need no extra assumption. -/
theorem pearson_annotation_eq_iff [Fintype X] [Fintype R] [Fintype B]
    (g : R → B) :
    rp_FiniteTask_pearson P k = rp_FiniteTask_pearson P (rp_FiniteTask_annotated k g) ↔
      ∀ a, 0 < rp_FiniteTask_reportMass P k a →
        rp_FiniteTask_posterior P k a = rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) := by
  rw [← sub_eq_zero, pearson_annotation_loss]
  have hn (x : X) :
      0 ≤ (∑ a, rp_FiniteTask_reportMass P k a *
        (rp_FiniteTask_posterior P k a x - rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) x)^2) /
          mass P x :=
    div_nonneg
      (Finset.sum_nonneg (fun a _ =>
        mul_nonneg (reportMass_nonneg P k a) (sq_nonneg _)))
      (mass_nonneg P x)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hn x)]
  constructor
  · intro h a ha
    funext x
    by_cases hx : mass P x = 0
    · rw [posterior_prior_zero P k a x hx,
        posterior_prior_zero P (rp_FiniteTask_annotated k g) (g a) x hx]
    · have hrow := (div_eq_zero_iff.mp (h x (Finset.mem_univ x))).resolve_right hx
      have hatom :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun b (_ : b ∈ Finset.univ) =>
            mul_nonneg (reportMass_nonneg P k b) (sq_nonneg _))).mp
              hrow a (Finset.mem_univ a)
      have hsq := (mul_eq_zero.mp hatom).resolve_left (ne_of_gt ha)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro h x _
    apply (div_eq_zero_iff).mpr
    left
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : rp_FiniteTask_reportMass P k a = 0
    · rw [ha, zero_mul]
    · have he := congrFun
        (h a (lt_of_le_of_ne (reportMass_nonneg P k a) (Ne.symm ha))) x
      simp only [he, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]

/-- Injective annotations lose no information, including when some reports
have zero mass. Surjectivity onto the annotation alphabet is unnecessary. -/
theorem pearson_annotation_injective [Fintype X] [Fintype R] [Fintype B]
    (g : R → B) (hg : Function.Injective g) :
    rp_FiniteTask_pearson P (rp_FiniteTask_annotated k g) = rp_FiniteTask_pearson P k := by
  have hl := pearson_annotation_loss P k g
  simp only [annotated_posterior] at hl
  have hz (x : X) :
      (∑ a, rp_FiniteTask_reportMass P k a *
        (rp_FiniteTask_posterior P k a x -
          mean g (rp_FiniteTask_reportMass P k) (fun b => rp_FiniteTask_posterior P k b x) (g a))^2) = 0 := by
    apply (loss_zero_iff g _ _ (reportMass_nonneg P k)).2
    intro a b hab _ _
    exact congrArg (fun z => rp_FiniteTask_posterior P k z x) (hg hab)
  simp only [hz, zero_div, Finset.sum_const_zero] at hl
  exact (sub_eq_zero.mp hl).symm

/-- Only equality of annotation classes matters to their posterior.
The representing alphabets need not be the same. -/
theorem annotated_posterior_eq_of_fibers [Fintype X] [Fintype R] {C : Type}
    (g : R → B) (h : R → C)
    (he : ∀ a b, g a = g b ↔ h a = h b) (a : R) (x : X) :
    rp_FiniteTask_posterior P (rp_FiniteTask_annotated k g) (g a) x =
      rp_FiniteTask_posterior P (rp_FiniteTask_annotated k h) (h a) x := by
  simp only [annotated_posterior, mean, push, he]

/-- Equal full-table annotation relations retain the same Pearson information.
This will identify a valid critic's quotient with any finite representation. -/
theorem pearson_annotation_eq_of_fibers [Fintype X] [Fintype R] [Fintype B]
    {C : Type} [Fintype C] (g : R → B) (h : R → C)
    (he : ∀ a b, g a = g b ↔ h a = h b) :
    rp_FiniteTask_pearson P (rp_FiniteTask_annotated k g) = rp_FiniteTask_pearson P (rp_FiniteTask_annotated k h) := by
  have hg := pearson_annotation_loss P k g
  have hh := pearson_annotation_loss P k h
  simp_rw [annotated_posterior_eq_of_fibers P k g h he] at hg
  linarith

end MutualEvaluation.FiniteTask
end