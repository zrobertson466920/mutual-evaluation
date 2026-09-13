import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ReplicationPaymentMoments
import MutualEvaluation.Internal.PearsonTarget
import MutualEvaluation.Internal.ShannonTarget

/-!
INTERNAL — unbiasedness bridge from actual replication payments to information.

The starting point is the class-probability expectation calculation for the
original Bochner integrals. Finite aggregation identifies these expectations
with the existing information functionals. Null prior/report atoms are handled
without a full-support assumption. Invalid critics are included in the final
equalities with the separate target scores.

No payment, sampling law, information functional, or target payoff is redefined.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open MeasureTheory Binary Probability FiniteTask
attribute [local instance] Classical.propDecidable

section FiniteAlgebra
variable {X R B : Type} [Fintype X] [Fintype R]

/-- Channel-probability form of the existing Pearson convention. -/
theorem pearson_channel_sum (P : PMF X) (k : Kernel X R) :
    rp_FiniteTask_pearson P k =
      (∑ x, mass P x * ∑ a, (mass (k x) a)^2 / rp_FiniteTask_reportMass P k a) - 1 := by
  dsimp only
  apply congrArg (fun z : ℝ => z - 1)
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hx : mass P x = 0
  · simp [ hx]
  · by_cases ha : rp_FiniteTask_reportMass P k a = 0
    · simp [ha]
    · field_simp

/-- Channel-log form of Shannon information, including null coordinates. -/
theorem shannon_channel_sum (P : PMF X) (k : Kernel X R) :
    rp_FiniteTask_shannon P k =
      ∑ x, mass P x * ∑ a, mass (k x) a *
        (Real.log (mass (k x) a) - Real.log (rp_FiniteTask_reportMass P k a)) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hx : mass P x = 0
  · simp [ hx]
  · by_cases ha : mass (k x) a = 0
    · simp [ ha]
    · have hq : rp_FiniteTask_reportMass P k a ≠ 0 := by
        intro hq
        have hj := jointMass_zero_of_reportMass_zero P k x a hq
        exact (mul_ne_zero hx ha) hj
      have hr : rp_FiniteTask_jointMass P k x a / (mass P x * rp_FiniteTask_reportMass P k a) =
          mass (k x) a / rp_FiniteTask_reportMass P k a := by
        dsimp only []
        field_simp
      rw [hr, Real.log_div ha hq]
      simp only [ mul_assoc]

omit [Fintype X] in
theorem mass_map_fiber (p : PMF R) (g : R → B) (b : B) :
    mass (p.map g) b = _root_.MutualEvaluation.Fiber.push g (mass p) b := by
  classical
  change mass (p.bind fun a => PMF.pure (g a)) b = _
  simp [mass_bind, mass_pure, _root_.MutualEvaluation.Fiber.push, mul_ite, eq_comm]

omit [Fintype X] in
theorem mass_map_weighted_sum [Fintype B] (p : PMF R) (g : R → B) (f : B → ℝ) :
    (∑ a, mass p a * f (g a)) = ∑ b, mass (p.map g) b * f b := by
  simp only [mass_map_fiber]
  exact (_root_.MutualEvaluation.Fiber.push_mul g (mass p) f).symm

end FiniteAlgebra

section ClassMass
variable {R B : Type} [MeasurableSpace R] [Fintype R]
  [MeasurableSingletonClass R]

theorem toMeasure_real_sum (p : PMF R) (E : Set R) :
    (p.toMeasure E).toReal = ∑ a, if a ∈ E then mass p a else 0 := by
  rw [p.toMeasure_apply_fintype]
  rw [ENNReal.toReal_sum (fun a _ => by
    simp only [Set.indicator_apply]
    split_ifs
    · exact p.apply_ne_top a
    · exact ENNReal.zero_ne_top)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ E <;> simp [ha, mass]

/-- A comparison class's success probability is its annotation mass.
No measurable-space structure on the annotation alphabet is needed. -/
theorem annotation_class_mass (p : PMF R) (g : R → B) (a : R) :
    (p.toMeasure {b | rp_Binary_Rel (rp_Binary_annotate g) a b}).toReal =
      mass (p.map g) (g a) := by
  rw [toMeasure_real_sum, mass_map_fiber]
  simp only [Set.mem_ofPred_eq, annotate_rel, _root_.MutualEvaluation.Fiber.push]
  apply Finset.sum_congr rfl
  intro b _
  simp only [eq_comm]

end ClassMass

section Unbiasedness
variable {X R B : Type} [Fintype X] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  [Fintype B]

omit [Fintype X] [Fintype R] [MeasurableSpace R]
  [MeasurableSingletonClass R] [Fintype B] in
private theorem mapped_report_mass (P : PMF X) (k : Kernel X R)
    (g : R → B) (b : B) :
    mass ((P.bind k).map g) b = rp_FiniteTask_reportMass P (rp_FiniteTask_annotated k g) b := by
  rw [PMF.map_bind]

/-- The actual collision-gated Pearson payment is unbiased for the information
retained by any finite annotation. The gate has not been replaced by a clock. -/
theorem u_chiSquared_annotation_impl (P : PMF X) (k : Kernel X R) (g : R → B) :
    rp_Replication_u_chiSquared (rp_Binary_annotate g) P k = rp_FiniteTask_pearson P (rp_FiniteTask_annotated k g) := by
  refine Eq.trans ?_ (pearson_channel_sum P (rp_FiniteTask_annotated k g)).symm
  rw [u_chiSquared_class_sum _ (MutualEvaluation.Binary.annotate_valid_impl g)]
  simp_rw [annotation_class_mass, mapped_report_mass]
  have hrow (x : X) :
      (∑ a, mass (k x) a * mass ((k x).map g) (g a) *
        (rp_FiniteTask_reportMass P (rp_FiniteTask_annotated k g) (g a))⁻¹) =
      ∑ b, (mass (rp_FiniteTask_annotated k g x) b)^2 / rp_FiniteTask_reportMass P (rp_FiniteTask_annotated k g) b := by
    calc
      _ = ∑ a, mass (k x) a *
          (mass ((k x).map g) (g a) *
            (rp_FiniteTask_reportMass P (rp_FiniteTask_annotated k g) (g a))⁻¹) := by
        simp only [mul_assoc]
      _ = ∑ b, mass ((k x).map g) b *
          (mass ((k x).map g) b * (rp_FiniteTask_reportMass P (rp_FiniteTask_annotated k g) b)⁻¹) :=
        mass_map_weighted_sum (k x) g
          (fun b => mass ((k x).map g) b *
            (rp_FiniteTask_reportMass P (rp_FiniteTask_annotated k g) b)⁻¹)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro b _
        dsimp only []
        ring
  simp_rw [hrow]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, mass_sum]

/-- The original harmonic two-clock integral is unbiased for retained Shannon
information, in nats. No factorization through a fixed-length record is used. -/
theorem u_KL_annotation_impl (P : PMF X) (k : Kernel X R) (g : R → B) :
    rp_Replication_u_KL (rp_Binary_annotate g) P k = rp_FiniteTask_shannon P (rp_FiniteTask_annotated k g) := by
  refine Eq.trans ?_ (shannon_channel_sum P (rp_FiniteTask_annotated k g)).symm
  rw [u_KL_class_sum _ (MutualEvaluation.Binary.annotate_valid_impl g)]
  simp_rw [annotation_class_mass, mapped_report_mass]
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg (fun z : ℝ => mass P x * z)
  exact mass_map_weighted_sum (k x) g
    (fun b => Real.log (mass ((k x).map g) b) -
      Real.log (rp_FiniteTask_reportMass P (rp_FiniteTask_annotated k g) b))

end Unbiasedness

section AllCritics
variable {X R : Type} [Fintype X] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]

/-- Equality of the actual loop score and the separate Pearson target for
every binary critic, not merely globally valid ones. -/
theorem u_chiSquared_eq_target (c : Critic R) (P : PMF X) (k : Kernel X R) :
    rp_Replication_u_chiSquared c P k = PearsonTarget.payoff c P k := by
  by_cases hc : rp_Binary_Valid c
  · obtain ⟨n, _, g, hg⟩ := (MutualEvaluation.Binary.valid_iff_annotation_impl c).1 hc
    rw [hg, MutualEvaluation.Replication.u_chiSquared_annotation_impl, PearsonTarget.payoff_annotation]
  · rw [(MutualEvaluation.Replication.invalid_scores_impl c hc P k).1, PearsonTarget.payoff_invalid P k c hc]

/-- Equality of the actual loop score and the separate Shannon target on
the full binary critic space. Invalid critics give zero on both sides. -/
theorem u_KL_eq_target (c : Critic R) (P : PMF X) (k : Kernel X R) :
    rp_Replication_u_KL c P k = ShannonTarget.payoff c P k := by
  by_cases hc : rp_Binary_Valid c
  · obtain ⟨n, _, g, hg⟩ := (MutualEvaluation.Binary.valid_iff_annotation_impl c).1 hc
    rw [hg, MutualEvaluation.Replication.u_KL_annotation_impl, ShannonTarget.payoff_annotation]
  · rw [(MutualEvaluation.Replication.invalid_scores_impl c hc P k).2, ShannonTarget.payoff_invalid P k c hc]

end AllCritics
end MutualEvaluation.Replication
end