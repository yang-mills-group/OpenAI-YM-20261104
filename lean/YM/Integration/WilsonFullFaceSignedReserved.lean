import YM.Integration.WilsonOlderSignedOneMarkRate
import YM.Integration.WilsonJointAxialClock

/-! Pay both of the physical exceptional terms at the actual upper
temperature, uniformly in the top cutoff and admitted period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFullFaceSignedReserved
open Filter RG Wilson Lattice Push.Local Pert.Asymptotics PhysicalNext.Repeat.Legato
open scoped Topology
variable {G : Gauge}

theorem original (R : Run G) (simple : G.Simple) (q : ℕ) :
    ∀ᶠ i:ℕ in atTop,∀N per:ℕ,i<N→
      let g:=regulatorRun R.family N per (i+1)
      let p:=R.family.path.levels.budget i
      let rel:=R.family.path.levels.clock.forcedAllowance i
      let κ:=LocalComparison.forcedDivisor R.family i
      (R.family.path.levels.clock.hatBeta (i+1))^(-(q:ℝ))+hitWidth p*rel/κ ≤ (4^q+1)*g^q :=by
  have price:=WilsonOlderSignedOneMarkRate.paid R simple 0 q (C:=1) (ε:=(3^q)⁻¹)
    (by norm_num) (by positivity)
  filter_upwards [WilsonJointAxialClock.original R simple,price] with i ages paid N per cut
  let g:=regulatorRun R.family N per (i+1)
  let b:=regulatorRun R.family N per i
  let H:=R.family.path.levels.clock.hatBeta (i+1)
  obtain ⟨gp,small,ratio,quarter⟩:=ages N per cut
  have old:=paid N per cut.le i le_rfl 1 zero_le_one (by simp)
  rw [mul_one] at old
  have weak : hitWidth (R.family.path.levels.budget i)*R.family.path.levels.clock.forcedAllowance i/
      LocalComparison.forcedDivisor R.family i ≤ g^q :=by
    refine old.trans ?_
    calc
      (3^q)⁻¹*b^q ≤ (3^q)⁻¹*(3*g)^q :=mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) ratio _) (by positivity)
      _ = _:=by rw [mul_pow,←mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]
  have lower : 1≤R.family.path.levels.clock.hatBeta i := (R.family.path.levels.fits.delayed i).le
  have monotone:=WilsonStartup.Timing.hat_mono R.family.path.levels (Gauge.slopeConstant_pos simple).le (Nat.le_succ i)
  have hp : 0<H:=(zero_lt_one.trans_le lower).trans_le monotone
  have inv : H⁻¹≤4*g^2:=(inv_anti₀ (zero_lt_one.trans_le lower) monotone).trans quarter
  have exempt : H^(-(q:ℝ))≤4^q*g^q :=by
    rw [Real.rpow_neg hp.le,Real.rpow_natCast,←inv_pow]
    calc _ ≤ (4*g^2)^q:=pow_le_pow_left₀ (inv_nonneg.mpr hp.le) inv _
         _ = 4^q*(g^2)^q :=mul_pow .. 
         _ ≤ _:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) (by
           rw [pow_two];exact mul_le_of_le_one_right gp.le small) _) (by positivity)
  exact (add_le_add exempt weak).trans_eq (by ring)

end YM.Integration.WilsonFullFaceSignedReserved
