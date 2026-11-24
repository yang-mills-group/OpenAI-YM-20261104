import YM.Integration.WilsonIndependentCapturedCalendar
import YM.Integration.WilsonPositionProgramReporterBand
import YM.RG01.Slack

/-! Original clock cost of the older scalar estimate on the actual cofinal
independent reporter. The period and the count of physical copies cancel. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedBand
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open WilsonPositionProgramCommonWindow WilsonPositionProgramReporterBand WilsonIndependentCapturedCalendar
open scoped BigOperators Classical
variable {G : Gauge} (C : Run G) (D : XSpace.Run)
local notation "A" => C.family.path.levels
local notation "H" => C.family.path.levels.clock.hatBeta
local notation "Λ" => RG16.Lambda C.family.path.levels

def factor : ℝ := 1 + Real.log D.ratio + (D.reserve+1:ℝ)*(Real.log 2 + Real.log D.ratio)

/-- The whole IR meter on the voted circuit has quadratic cost in its
reported index, on every selected date and independently of the period. -/
theorem paid (simple : G.Simple) : ∃ first : ℕ, ∀ stage ≥ first, ∀ B : Band C D stage, ∀ t,
      fare C D B.lower B.span B.powers t ≤ factor D * (1+(B.index t:ℝ))^2 := by
  obtain ⟨first,pace⟩ := eventually_atTop.mp (RG01.Physical.nextHat simple C.alloy.B.a)
  refine ⟨first,?_⟩
  intro stage hstage B t
  let b := B.lower t
  let i := B.index t
  have hbase : first ≤ b := hstage.trans (B.ready t)
  have hot (k : ℕ) : 0 < H k := zero_lt_one.trans (Extension.UV.hat_positive simple C.alloy.B.a k)
  have watts (k : ℕ) : Λ (b+k) ≤ Λ b + (k:ℝ)*Real.log 2 := by
    induction k with
    | zero => simp
    | succ k ih =>
      have step : H (b+k+1) ≤ 2*H (b+k) := pace (b+k) (hbase.trans (Nat.le_add_right ..))
      have bound := Real.log_le_log (hot _) step
      rw [Real.log_mul (by norm_num) (hot _).ne'] at bound
      unfold RG16.Lambda at ih ⊢
      simp only [Nat.cast_succ,Nat.add_succ]
      change 2+Real.log (H (b+k+1)) ≤ 2+Real.log (H b)+((k:ℝ)+1)*Real.log 2
      linarith
  have digits (k : ℕ) : 1 ≤ B.powers t k := by
    by_contra! low
    have hz : B.powers t k = 0 := by omega
    have step := B.blocks t k
    rw [hz,pow_zero] at step
    have large := C.family.S.block_large (B.lower t+k)
    omega
  have count : B.span t ≤ elapsed (B.powers t) (B.span t) := by
    unfold elapsed
    simpa using (Finset.sum_le_sum (s:=Finset.range (B.span t)) (fun k _ => digits k))
  let a := elapsed (B.powers t) (B.span t)
  have index : (a:ℝ) = (D.reserve:ℝ)*(i:ℝ)*(i:ℝ)+(i:ℝ) := by exact_mod_cast B.extent t
  have logDen : Real.log (D.den a : ℝ) = (a:ℝ)*Real.log D.ratio := by
    simp only [XSpace.Run.den,Nat.cast_pow,Real.log_pow]
  have nonneg : 0 ≤ Real.log (D.ratio:ℝ) := Real.log_nonneg (by exact_mod_cast ((by decide : 1 ≤ 3).trans D.large))
  have nonneg2 : 0 ≤ Real.log (2:ℝ) := Real.log_nonneg (by norm_num)
  have i0 : 0 ≤ (i:ℝ) := Nat.cast_nonneg _
  have mi : (i:ℝ) ≤ (1+(i:ℝ))^2 := by nlinarith [sq_nonneg (i:ℝ)]
  have ri : (i:ℝ)^2 ≤ (1+(i:ℝ))^2 := by nlinarith
  have ai : (a:ℝ) ≤ ((D.reserve:ℝ)+1)*(1+(i:ℝ))^2 := by
    rw [index]
    nlinarith only [mul_le_mul_of_nonneg_left ri (Nat.cast_nonneg D.reserve), mi]
  have charge (h : 0 ≤ Real.log 2 + Real.log (D.ratio:ℝ)) := mul_le_mul_of_nonneg_right ai h
  change 1+Λ (b+B.span t)+Real.log (D.den a : ℝ) ≤ factor D*(1+(i:ℝ))^2
  rw [logDen]
  calc
    _ ≤ 1 + (i:ℝ)*Real.log D.ratio + (a:ℝ)*(Real.log 2+Real.log D.ratio) := by
      have span : (B.span t:ℝ) ≤ a := by exact_mod_cast count
      nlinarith only [watts (B.span t), B.age t, mul_le_mul_of_nonneg_right span nonneg2]
    _ ≤ factor D*(1+(i:ℝ))^2 := by
      unfold factor
      nlinarith only [charge (add_nonneg nonneg2 nonneg),mul_le_mul_of_nonneg_right mi nonneg,i0,sq_nonneg (i:ℝ)]

end YM.Integration.WilsonIndependentCapturedBand

