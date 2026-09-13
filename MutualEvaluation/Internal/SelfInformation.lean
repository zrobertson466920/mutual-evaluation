import MutualEvaluation.Internal.ReplicationExpressions
import MutualEvaluation.Internal.FiniteProbability

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-!
# Fair-binary task information from conditionally independent replications

Finite report alphabets, with no full-support hypothesis. These identities
concern repeated-channel laws, not arbitrary pair or outcome laws.
Real division is zero at null atoms; domination is proved for the Pearson formula.
No replication search, stopping time, or robustness certificate is defined here.
-/

noncomputable section
open scoped MutualEvaluation.Internal.ReplicationExpressions
attribute [local instance] Classical.propDecidable
namespace MutualEvaluation.Self
open Probability


variable {R : Type}

def repeated (k : Kernel Bool R) : PMF (R × R) :=
  (rp_Self_fair).bind fun x => pair (k x) (k x)

def reportMass (k : Kernel Bool R) (a : R) : ℝ :=
  (mass (k false) a + mass (k true) a) / 2

def posterior (k : Kernel Bool R) (a : R) : ℝ :=
  mass (k true) a / (mass (k false) a + mass (k true) a)

def information [Fintype R] (k : Kernel Bool R) : ℝ :=
  4 * ∑ a, reportMass k a * (posterior k a - 1 / 2)^2

def joint (k : Kernel Bool R) : PMF (Bool × R) :=
  (rp_Self_fair).bind fun x => (k x).map fun a => (x, a)

def reference (k : Kernel Bool R) : PMF (Bool × R) :=
  pair rp_Self_fair ((joint k).map Prod.snd)

/-- Used as Pearson divergence only with domination, proved below. -/
def chiSquared {T : Type} [Fintype T] (μ ν : PMF T) : ℝ :=
  ∑ a, (mass μ a - mass ν a)^2 / mass ν a

theorem reportMass_nonneg (k : Kernel Bool R) (a : R) : 0 ≤ reportMass k a :=
  div_nonneg (add_nonneg (mass_nonneg _ _) (mass_nonneg _ _)) (by norm_num)

theorem reportMass_sum [Fintype R] (k : Kernel Bool R) : ∑ a, reportMass k a = 1 := by
  unfold reportMass
  rw [← Finset.sum_div, Finset.sum_add_distrib, mass_sum, mass_sum]
  norm_num

theorem weighted_posterior (k : Kernel Bool R) (a : R) :
    reportMass k a * posterior k a = mass (k true) a / 2 := by
  have h₀ := mass_nonneg (k false) a
  have h₁ := mass_nonneg (k true) a
  by_cases hz : mass (k false) a + mass (k true) a = 0
  · have ht : mass (k true) a = 0 := by linarith
    simp [reportMass, posterior, ht]
  · dsimp [reportMass, posterior]
    field_simp

private theorem mass_fair_bind (k : Kernel Bool R) (a : R) :
    mass ((rp_Self_fair).bind k) a = (mass (k false) a + mass (k true) a) / 2 := by
  rw [mass_bind]
  have hf (x : Bool) : mass rp_Self_fair x = 1 / 2 := by
    norm_num [mass, PMF.uniformOfFintype_apply]
  simp only [Fintype.sum_bool, hf]
  ring

theorem repeated_marginal (k : Kernel Bool R) (a : R) :
    mass ((repeated k).map Prod.fst) a = reportMass k a := by
  have hm : (repeated k).map Prod.fst = (rp_Self_fair).bind k := by
    simp only [repeated, pair, PMF.map, Function.comp_def,
      PMF.bind_bind, PMF.pure_bind, PMF.bind_const, PMF.bind_pure]
  rw [hm, mass_fair_bind]
  rfl

private theorem mass_joint [Fintype R] (k : Kernel Bool R) (x : Bool) (a : R) :
    mass (joint k) (x, a) = mass (k x) a / 2 := by
  classical
  change mass ((rp_Self_fair).bind fun z => (k z).bind fun b => PMF.pure (z, b)) (x, a) = _
  rw [mass_fair_bind]
  simp only [mass_bind, mass_pure, Prod.mk.injEq]
  cases x <;> simp [eq_comm]

private theorem joint_marginal (k : Kernel Bool R) (a : R) :
    mass ((joint k).map Prod.snd) a = reportMass k a := by
  have hm : (joint k).map Prod.snd = (rp_Self_fair).bind k := by
    simp only [joint, PMF.map, Function.comp_def,
      PMF.bind_bind, PMF.pure_bind, PMF.bind_pure]
  rw [hm, mass_fair_bind]
  rfl

/-- The formula really is Bayes' posterior for the latent/report experiment. -/
theorem posterior_bayes [Fintype R] (k : Kernel Bool R) (a : R) :
    posterior k a = mass (joint k) (true, a) / mass ((joint k).map Prod.snd) a := by
  rw [mass_joint, joint_marginal]
  dsimp [posterior, reportMass]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- Fair-binary repeated observations: independence part plus posterior covariance. -/
theorem repeated_posterior [Fintype R] (k : Kernel Bool R) (a b : R) :
    mass (repeated k) (a, b) =
      reportMass k a * reportMass k b +
        4 * (reportMass k a * (posterior k a - 1 / 2)) *
          (reportMass k b * (posterior k b - 1 / 2)) := by
  have hm : mass (repeated k) (a, b) =
      (mass (k false) a * mass (k false) b +
        mass (k true) a * mass (k true) b) / 2 := by
    rw [repeated, mass_fair_bind, mass_pair, mass_pair]
  rw [hm]
  have h (a : R) : reportMass k a * (posterior k a - 1 / 2) =
      (mass (k true) a - mass (k false) a) / 4 := by
    rw [mul_sub, weighted_posterior]
    dsimp [reportMass]
    ring
  rw [h, h]
  dsimp [reportMass]
  ring

private theorem mass_reference [Fintype R] (k : Kernel Bool R) (x : Bool) (a : R) :
    mass (reference k) (x, a) = reportMass k a / 2 := by
  rw [reference, mass_pair, joint_marginal]
  have hf : mass rp_Self_fair x = 1 / 2 := by
    norm_num [mass, PMF.uniformOfFintype_apply]
  rw [hf]
  ring

/-- Null reference atoms have null joint mass: division by zero hides no singular part. -/
theorem reference_dominated [Fintype R] (k : Kernel Bool R) (x : Bool) (a : R)
    (hz : mass (reference k) (x, a) = 0) : mass (joint k) (x, a) = 0 := by
  rw [mass_reference] at hz
  have hp : reportMass k a = 0 := by linarith
  have h₀ := mass_nonneg (k false) a
  have h₁ := mass_nonneg (k true) a
  dsimp [reportMass] at hp
  rw [mass_joint]
  cases x <;> linarith

private theorem chiSquared_atom [Fintype R] (k : Kernel Bool R) (a : R) :
    (mass (joint k) (false, a) - mass (reference k) (false, a))^2 /
        mass (reference k) (false, a) +
      (mass (joint k) (true, a) - mass (reference k) (true, a))^2 /
        mass (reference k) (true, a) =
      4 * reportMass k a * (posterior k a - 1 / 2)^2 := by
  simp only [mass_joint, mass_reference]
  have ht := weighted_posterior k a
  have hf : mass (k false) a / 2 = reportMass k a - reportMass k a * posterior k a := by
    rw [ht]
    dsimp [reportMass]
    ring
  rw [hf, ← ht]
  by_cases hp : reportMass k a = 0
  · simp [hp]
  · field_simp
    ring

theorem information_eq_chiSquared [Fintype R] (k : Kernel Bool R) :
    information k = chiSquared (joint k) (reference k) := by
  unfold chiSquared information
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  simp only [add_comm, chiSquared_atom]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem information_nonneg [Fintype R] (k : Kernel Bool R) : 0 ≤ information k := by
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (reportMass_nonneg k a) (sq_nonneg _))

private theorem posterior_bounds (k : Kernel Bool R) (a : R) :
    0 ≤ posterior k a ∧ posterior k a ≤ 1 := by
  have h₀ := mass_nonneg (k false) a
  have h₁ := mass_nonneg (k true) a
  constructor
  · exact div_nonneg h₁ (add_nonneg h₀ h₁)
  · by_cases hz : mass (k false) a + mass (k true) a = 0
    · simp [posterior, hz]
    · have hp := lt_of_le_of_ne (add_nonneg h₀ h₁) (Ne.symm hz)
      apply (div_le_iff₀ hp).2
      linarith

theorem information_le_one [Fintype R] (k : Kernel Bool R) : information k ≤ 1 := by
  have hb (a : R) : (posterior k a - 1 / 2)^2 ≤ 1 / 4 := by
    have h := posterior_bounds k a
    nlinarith
  have hs : (∑ a, reportMass k a * (posterior k a - 1 / 2)^2) ≤
      ∑ a, reportMass k a * (1 / 4) :=
    Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hb a) (reportMass_nonneg k a))
  rw [← Finset.sum_mul, reportMass_sum] at hs
  unfold information
  linarith

end MutualEvaluation.Self
end