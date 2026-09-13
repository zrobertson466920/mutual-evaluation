import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.ReplicationMoments

/-!
INTERNAL — harmonic expectation for the actual stream-defined first-hit clock.

Integrability is proved by domination by the integrable call count. The mean
then follows from the harmonic recurrence and logarithm power series, using
the pushforward law already derived from actual stream events.
The success-one boundary is included; success-zero events are not assigned a
fictitious finite waiting-time law.

These single-stream results do not yet establish either payment's integrability
or unbiasedness under the full anchored-task experiment.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Replication
open MeasureTheory ProbabilityTheory
open Internal.ReplicationPaths

theorem H_succ (n : ℕ) : rp_Replication_H (n + 1) = rp_Replication_H n + ((n : ℝ) + 1)⁻¹ := by
  simp only [ Finset.sum_range_succ]

theorem H_nonneg (n : ℕ) : 0 ≤ rp_Replication_H n := by
  dsimp only
  exact Finset.sum_nonneg (fun j _ => inv_nonneg.mpr (by positivity))

theorem H_le (n : ℕ) : rp_Replication_H n ≤ (n : ℝ) := by
  calc
    rp_Replication_H n ≤ ∑ j ∈ Finset.range n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      exact (inv_le_one₀ (by positivity : 0 < (j : ℝ) + 1)).2
        (by linarith [Nat.cast_nonneg (α := ℝ) j])
    _ = (n : ℝ) := by simp

theorem geometric_harmonic_integrable (q : unitInterval) (hq : q ≠ 0) :
    Integrable rp_Replication_H (geometricMeasure q) := by
  apply (geometric_calls_integrable q hq).mono'
    (measurable_of_countable rp_Replication_H).aestronglyMeasurable
  filter_upwards [] with n
  rw [Real.norm_eq_abs, abs_of_nonneg (H_nonneg n)]
  exact (H_le n).trans (by linarith)

/-- The shifted harmonic recurrence identifies the mean without exchanging
an unjustified double sum. Integrability precedes the integral calculation. -/
theorem geometric_harmonic_integral (q : unitInterval) (hq : q ≠ 0) :
    (∫ n : ℕ, rp_Replication_H n ∂geometricMeasure q) = -Real.log (q : ℝ) := by
  have hq0 : (q : ℝ) ≠ 0 := by
    intro h
    exact hq (Subtype.ext h)
  have hpos : 0 < (q : ℝ) :=
    lt_of_le_of_ne q.property.1 (Ne.symm hq0)
  have hr : |1 - (q : ℝ)| < 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr q.property.2)]
    linarith
  let L : ℝ := ∫ n : ℕ, rp_Replication_H n ∂geometricMeasure q
  have hf : HasSum (fun n : ℕ => (1 - (q : ℝ))^n * (q : ℝ) * rp_Replication_H n) L := by
    simpa only [smul_eq_mul] using
      hasSum_integral_geometricMeasure hq (geometric_harmonic_integrable q hq)
  have ht : HasSum
      (fun n : ℕ => (1 - (q : ℝ))^(n + 1) * (q : ℝ) * rp_Replication_H (n + 1)) L := by
    simpa only [Finset.sum_range_one, H_zero, mul_zero, sub_zero] using
      (hasSum_nat_add_iff' 1).2 hf
  have hd := ht.sub (hf.mul_left (1 - (q : ℝ)))
  have he :
      (fun n : ℕ =>
        (1 - (q : ℝ))^(n + 1) * (q : ℝ) * rp_Replication_H (n + 1) -
          (1 - (q : ℝ)) * ((1 - (q : ℝ))^n * (q : ℝ) * rp_Replication_H n)) =
      (fun n : ℕ =>
        (q : ℝ) * ((1 - (q : ℝ))^(n + 1) / ((n : ℝ) + 1))) := by
    funext n
    rw [H_succ, pow_succ]
    ring
  rw [he] at hd
  have hl : HasSum
      (fun n : ℕ => (q : ℝ) * ((1 - (q : ℝ))^(n + 1) / ((n : ℝ) + 1)))
      ((q : ℝ) * (-Real.log (q : ℝ))) := by
    simpa only [sub_sub_cancel] using
      (Real.hasSum_pow_div_log_of_abs_lt_one hr).mul_left (q : ℝ)
  have hi : L = -Real.log (q : ℝ) := by
    apply mul_left_cancel₀ hq0
    nlinarith [hd.unique hl]
  exact hi

variable {R : Type} [MeasurableSpace R]

/-- Integrability of the harmonic payment coordinate on the actual stream.
The value at infinity is H 0 = 0, matching the zero extension. -/
theorem iid_harmonic_integrable (p : PMF R) (E : Set R)
    (hE : MeasurableSet E) (hp : 0 < p.toMeasure E) :
    Integrable (fun ω => rp_Replication_H ((rp_Replication_firstHit (fun n => ω n ∈ E)).toNat - 1))
      (rp_Replication_iid p) := by
  have hg := geometric_harmonic_integrable
    (hitParameter p E) (hitParameter_ne_zero p E hp)
  rw [← iid_hitFailures_map p E hE hp] at hg
  exact (integrable_map_measure
    (measurable_of_countable rp_Replication_H).aestronglyMeasurable
    (measurable_hitFailures E hE).aemeasurable).1 hg

/-- Harmonic inverse-binomial identity derived for the existing first-hit
clock, not assumed as a sampling oracle. Natural logarithms are used. -/
theorem iid_harmonic_integral (p : PMF R) (E : Set R)
    (hE : MeasurableSet E) (hp : 0 < p.toMeasure E) :
    (∫ ω, rp_Replication_H ((rp_Replication_firstHit (fun n => ω n ∈ E)).toNat - 1) ∂rp_Replication_iid p) =
      -Real.log (p.toMeasure E).toReal := by
  calc
    _ = ∫ n : ℕ, rp_Replication_H n ∂(rp_Replication_iid p).map (hitFailures E) :=
      (integral_map_of_stronglyMeasurable (measurable_hitFailures E hE)
        (measurable_of_countable rp_Replication_H).stronglyMeasurable).symm
    _ = -Real.log (p.toMeasure E).toReal := by
      rw [iid_hitFailures_map p E hE hp,
        geometric_harmonic_integral _ (hitParameter_ne_zero p E hp)]
      rfl

end MutualEvaluation.Replication
end