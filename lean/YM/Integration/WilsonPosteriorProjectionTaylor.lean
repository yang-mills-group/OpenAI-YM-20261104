import YM.Integration.WilsonPosteriorProjectionRay
import YM.Integration.WilsonPosteriorProjectionStencil

/-! Price the Taylor rows of the actual Wilson coarse exponential curve.
The compared polynomial is sampled whole. Only the physical posterior's
own next derivative, on the actual coarse link fields, enters the error. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionTaylor
open Lattice Wilson RG Precision Tree Exterior Push.Uniform Finset Set
open LocalLTE.Weft WilsonPosteriorProjectionRay WilsonPosteriorProjectionStencil
open scoped BigOperators Classical
variable {G : Gauge} {c : Side}

def ray (F : Config G c → ℝ) (g : ℝ) (z : Positions (Primary c G)) (t : ℝ) :=
  F (represent (tint G _ (g • (t • z))))

def row (f : ℝ → ℝ) (j : ℕ) := iteratedDeriv j f 0 / j.factorial

private theorem remainder (f : ℝ → ℝ) (m : ℕ) (t x B : ℝ) (ht : 0 < t) (hx : x ∈ Icc 0 t)
    (smooth : ContDiff ℝ (2*m+1) f) (hB : 0 ≤ B)
    (higher : ∀ u ∈ Icc 0 t, ‖iteratedDeriv (2*m+1) f u‖ ≤ B) :
    |f x - ∑ i : J m, row f i.val * x^i.val| ≤ B*t^(2*m+1) := by
  have same (u : ℝ) (hu : u ∈ Icc 0 t) (k : ℕ) (hk : k ≤ 2*m+1) :
      iteratedDerivWithin k f (Icc 0 t) u = iteratedDeriv k f u :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
      ((smooth.of_le (by exact_mod_cast hk)).contDiffAt) hu
  have regular : ContDiffOn ℝ ((2*m:ℕ)+1) f (Icc 0 t) := smooth.contDiffOn
  have bound := taylor_mean_remainder_bound (n := 2*m) ht.le regular hx
    (fun u hu => (same u hu _ le_rfl) ▸ higher u hu)
  have tay : taylorWithinEval f (2*m) (Icc 0 t) 0 x =
      ∑ i : J m, row f i.val * x^i.val := by
    rw [taylor_within_apply, ← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    rw [same 0 ⟨le_rfl,ht.le⟩ i.val (by omega)]
    unfold row
    simp only [smul_eq_mul, sub_zero, div_eq_mul_inv]
    ring
  rw [tay,Real.norm_eq_abs,sub_zero] at bound
  apply bound.trans
  have pos := mul_nonneg hB (pow_nonneg hx.1 (2*m+1))
  have fac : (1:ℝ) ≤ ((2*m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (2*m)
  exact (div_le_self pos fac).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hx.2 _) hB)

theorem projected (F : Config G c → ℝ) (g : ℝ) (z : Positions (Primary c G))
    (m : ℕ) (a : J m → ℝ) (j : J m) (t ε B : ℝ) (ht : 0 < t)
    (smooth : ContDiff ℝ (2*m+1) (ray F g z)) (hB : 0 ≤ B)
    (higher : ∀ u ∈ Icc 0 t, ‖leftDerivs F (List.replicate (2*m+1) (direction g z))
      (represent (tint G _ (g • (u • z))))‖ ≤ B)
    (samples : ∀ i : J m, |ray F g z (t * probe m i) -
      ∑ n : J m, a n * (t * probe m i)^n.val| ≤ ε) :
    |(row (ray F g z) j.val-a j)*t^j.val| ≤ cost m j * (ε + B*t^(2*m+1)) := by
  apply price m (fun n => row (ray F g z) n.val - a n) j t
  intro i
  have cell : t * probe m i ∈ Icc 0 t :=
    ⟨mul_nonneg ht.le (probes m i).1.le, mul_le_of_le_one_right ht.le (probes m i).2⟩
  have rem := remainder (ray F g z) m t _ B ht cell smooth hB
    (fun u hu => (derivative F g z (2*m+1) u) ▸ higher u hu)
  simp_rw [sub_mul, sum_sub_distrib]
  have both := abs_sub_le (∑ n : J m, row (ray F g z) n.val * (t*probe m i)^n.val)
    (ray F g z (t*probe m i)) (∑ n : J m, a n * (t*probe m i)^n.val)
  rw [abs_sub_comm (∑ n : J m, row (ray F g z) n.val * (t*probe m i)^n.val)
    (ray F g z (t*probe m i))] at both
  linarith only [both,rem,samples i]

end YM.Integration.WilsonPosteriorProjectionTaylor

