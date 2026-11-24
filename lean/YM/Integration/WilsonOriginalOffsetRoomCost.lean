import YM.Integration.WilsonOriginalOffsetSourceAperture
import YM.Integration.WilsonReportLampForecast
import YM.Integration.WilsonThermometerOffsetLedger

/-! The original reporting-room price also pays the full moved derivative
test at the occupied source. Both the stage order and the cover can vary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOffsetRoomCost
open Function Filter Set Lattice Wilson RG Source Labels
open PhysicalNext.Repeat.Legato WilsonReportRetainedAnchor
open WilsonRetainedMarkedInletRegular WilsonReportLampForecast
open scoped Classical Topology

private theorem fac (k : ℕ) : k.factorial ≤ k^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ,pow_succ,Nat.mul_comm (k+1)]
    exact Nat.mul_le_mul_right _ (ih.trans (Nat.pow_le_pow_left (Nat.le_succ k) k))

private theorem table (P : BudgetPoint) :
    reprice P P.B = (1+2*(P.B:ℝ))^(2*(P.power*P.order)) := by
  unfold reprice
  push_cast
  rw [show 1+((P.B:ℝ)*(4*P.B+2)+2*P.B)=(1+2*(P.B:ℝ))^2 by ring,←pow_mul,←pow_mul]

private theorem costed (P : BudgetPoint) (x : ℝ) (hx : 0<x)
    (room : (Real.log x)^2 ≤ (P.B:ℝ)) (late : max 2 (Real.exp 1) ≤ Real.log x)
    (earned : reprice P P.B ≤ x) : cost P ≤ Real.exp 1*reprice P P.B := by
  let k := P.power*P.order
  let b := 1+2*(P.B:ℝ)
  have hl := (le_max_left (2:ℝ) (Real.exp 1)).trans late
  have hc := (le_max_right (2:ℝ) (Real.exp 1)).trans late
  have bn : 0≤b := by dsimp [b]; positivity
  have base : Real.exp 1 ≤ b := by dsimp [b]; nlinarith [Real.exp_pos 1,sq_nonneg (Real.log x-1)]
  rw [table] at earned ⊢
  have klog : (2*k:ℕ) ≤ Real.log x := by
    apply Real.exp_le_exp.mp
    calc
      Real.exp ((2*k:ℕ):ℝ) = (Real.exp 1)^(2*k) := by rw [←Real.exp_nat_mul]; simp
      _ ≤ b^(2*k) := pow_le_pow_left₀ (Real.exp_pos _).le base _
      _ ≤ Real.exp (Real.log x) := (Real.exp_log hx).symm ▸ earned
  have kb : 3*(k:ℝ) ≤ b := by
    dsimp [b]
    push_cast at klog
    nlinarith [sq_nonneg (Real.log x-1), Nat.cast_nonneg (α:=ℝ) P.B]
  have fac' : (k.factorial:ℝ) ≤ (k:ℝ)^k := by exact_mod_cast fac k
  unfold cost
  change (6*(P.B:ℝ)+3)^k * (k.factorial:ℝ) * Real.exp 1 ≤ Real.exp 1 * b^(2*k)
  rw [mul_comm (Real.exp 1)]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  calc
    _ ≤ (6*(P.B:ℝ)+3)^k * (k:ℝ)^k := mul_le_mul_of_nonneg_left fac' (by positivity)
    _ = (b * (3*k))^k := by rw [←mul_pow]; congr 1; dsimp [b]; ring
    _ ≤ (b*b)^k := pow_le_pow_left₀ (mul_nonneg bn (by positivity)) (mul_le_mul_of_nonneg_left kb bn) _
    _ = b^(2*k) := by rw [←sq,←pow_mul]

theorem original {G : Gauge} (R : Run G) (simple : G.Simple) (book : Ready R.family.path.levels) (j : ℕ) :
    ∀ᶠ i in atTop, ∀ N p : ℕ, i≤N →
      cost (R.family.path.rep N p i).p ≤ Real.exp 1*(R.alloy.B.a.clock.hatBeta i)^(part j) := by
  let A := R.alloy.B.a
  have rise : Tendsto A.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [book 0,book j,(Real.tendsto_log_atTop.comp rise).eventually_ge_atTop
    (max 2 (Real.exp 1))] with i large target late N p live
  have same : (R.family.path.rep N p i).p = A.budget i := (R.makes.wilson.represents N p i live).vac
  rw [same]
  change cost (A.budget i) ≤ Real.exp 1*(A.clock.hatBeta i)^(part j)
  change reprice (A.budget i) (A.budget i).B ≤ (A.clock.hatBeta i)^(part 0) at large
  change reprice (A.budget i) (A.budget i).B ≤ (A.clock.hatBeta i)^(part j) at target
  have cap : reprice (A.budget i) (A.budget i).B ≤ A.clock.hatBeta i := by simpa [part] using large
  exact (costed _ (A.clock.hatBeta i) (zero_lt_one.trans (A.fits.delayed i))
    (Nat.le_ceil _) late cap).trans (mul_le_mul_of_nonneg_left target (Real.exp_pos _).le)

end YM.Integration.WilsonOriginalOffsetRoomCost
end
