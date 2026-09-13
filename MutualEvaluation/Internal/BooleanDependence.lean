import MutualEvaluation.Internal.FiniteProbabilityProofs

/-! INTERNAL — implementation and proof support; not an author-certified annotation file. -/

/-!
Boolean dependence algebra for the timing example. Arbitrary stochastic
channels are permitted. The determinant formula is not asserted for larger alphabets.
-/
noncomputable section
namespace MutualEvaluation.Boolean
open Probability Probability.Proofs

local notation "mass" => (fun {A : Type} (p : PMF A) (a : A) => ENNReal.toReal (p a))

def determinant (μ : PMF (Bool × Bool)) : ℝ :=
  mass μ (false, false) * mass μ (true, true) -
    mass μ (false, true) * mass μ (true, false)

def D (μ : PMF (Bool × Bool)) : ℝ := |determinant μ|

theorem D_nonneg (μ : PMF (Bool × Bool)) : 0 ≤ D μ := abs_nonneg _

private theorem mass_fst (μ : PMF (Bool × Bool)) (a : Bool) :
    mass (μ.map Prod.fst) a = mass μ (a, false) + mass μ (a, true) := by
  cases a <;>
    simp [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
      ENNReal.toReal_add, PMF.apply_ne_top, add_comm]

private theorem mass_snd (μ : PMF (Bool × Bool)) (b : Bool) :
    mass (μ.map Prod.snd) b = mass μ (false, b) + mass μ (true, b) := by
  cases b <;>
    simp [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type,
      ENNReal.toReal_add, PMF.apply_ne_top, add_comm]

private theorem mass_total (μ : PMF (Bool × Bool)) :
    mass μ (false, false) + mass μ (false, true) +
      mass μ (true, false) + mass μ (true, true) = 1 := by
  simpa [Fintype.sum_prod_type, Fintype.sum_bool, add_comm, add_left_comm, add_assoc]
    using mass_sum μ

theorem residual (μ : PMF (Bool × Bool)) (a b : Bool) :
    mass μ (a, b) - mass (μ.map Prod.fst) a * mass (μ.map Prod.snd) b =
      if a = b then determinant μ else -determinant μ := by
  rw [mass_fst, mass_snd]
  have hm := congrArg (fun t : ℝ => mass μ (a, b) * t) (mass_total μ)
  cases a <;> cases b <;> simp [determinant] at * <;> nlinarith

theorem D_zero_iff (μ : PMF (Bool × Bool)) : D μ = 0 ↔ independent μ := by
  rw [D, abs_eq_zero, independent_iff_mass]
  constructor
  · intro h a b
    have hr := residual μ a b
    rw [h] at hr
    split_ifs at hr <;> linarith
  · intro h
    simpa [h false false] using (residual μ false false).symm

theorem D_pos_iff (μ : PMF (Bool × Bool)) : 0 < D μ ↔ ¬ independent μ := by
  rw [← D_zero_iff]
  exact lt_iff_le_and_ne.trans (by simp [D_nonneg μ, ne_comm])

/-- TV distance between the joint law and the product of its marginals. -/
def TV (μ : PMF (Bool × Bool)) : ℝ :=
  (1 / 2) * ∑ a : Bool, ∑ b : Bool,
    |mass μ (a, b) - mass (μ.map Prod.fst) a * mass (μ.map Prod.snd) b|

theorem TV_eq (μ : PMF (Bool × Bool)) : TV μ = 2 * D μ := by
  unfold TV
  simp_rw [residual]
  simp [D]
  ring

def factor (κ : Kernel Bool Bool) : ℝ :=
  mass (κ false) false - mass (κ true) false

theorem factor_abs_le (κ : Kernel Bool Bool) : |factor κ| ≤ 1 := by
  have h₀ := mass_nonneg (κ false) false
  have h₁ := mass_nonneg (κ true) false
  have h₂ := mass_le_one (κ false) false
  have h₃ := mass_le_one (κ true) false
  rw [abs_le]
  dsimp [factor]
  constructor <;> linarith

private theorem mass_true (p : PMF Bool) : mass p true = 1 - mass p false := by
  have h := mass_sum p
  simp only [Fintype.sum_bool] at h
  linarith

theorem determinant_post (μ : PMF (Bool × Bool)) (κ η : Kernel Bool Bool) :
    determinant (post μ κ η) = determinant μ * factor κ * factor η := by
  simp only [determinant, mass_post, Fintype.sum_bool, mass_true, factor]
  ring

theorem D_post (μ : PMF (Bool × Bool)) (κ η : Kernel Bool Bool) :
    D (post μ κ η) = D μ * |factor κ| * |factor η| := by
  simp only [D, determinant_post, abs_mul]

/-- Joint local data processing. Reporter-1 robustness will use η = PMF.pure;
the second-coordinate bound is proved here, not assumed in Core. -/
theorem data_processing (μ : PMF (Bool × Bool)) (κ η : Kernel Bool Bool) :
    D (post μ κ η) ≤ D μ := by
  calc
    D (post μ κ η) = (D μ * |factor κ|) * |factor η| := D_post μ κ η
    _ ≤ (D μ * |factor κ|) * 1 :=
      mul_le_mul_of_nonneg_left (factor_abs_le η)
        (mul_nonneg (D_nonneg μ) (abs_nonneg _))
    _ ≤ D μ := by
      simpa using mul_le_mul_of_nonneg_left (factor_abs_le κ) (D_nonneg μ)

end MutualEvaluation.Boolean
end