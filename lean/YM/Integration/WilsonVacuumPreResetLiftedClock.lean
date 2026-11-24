import YM.Integration.WilsonVacuumPreResetPeriodTail
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMeasured
import YM.RG01.Slack

/-! One reporting threshold before all finite cutoffs and periods buys the
actual covering-series width at the incoming date from the measured original
block calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetLiftedClock
open Filter RG Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Ticket PhysicalNext.Repeat.Legato
open scoped Topology
variable {G:Gauge}

theorem original (R:Run G)(simple:G.Simple)(K:ℝ)(non:0≤K):
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop, 2≤(V.budget m).B ∧
      ∀σ:ℝ,0<σ → σ⁻¹≤zz V (m+1) →
        ∀ e:ℝ,e≤K → e/(V.budget m).B≤σ/4:=by
  intro V
  let β:=V.clock.hatBeta
  have growth:=Real.tendsto_log_atTop.comp (RG01.Physical.hats simple V)
  filter_upwards [growth.eventually_ge_atTop (max 2 (8*K)),RG01.Physical.nextHat simple V] with m room next
  let x:=Real.log (β m)
  let B:=((V.budget m).B:ℝ)
  have xx:2≤x:= (le_max_left _ _).trans room
  have fee:8*K≤x:=(le_max_right _ _).trans room
  have grid:x^2≤B:=Nat.le_ceil _
  have bpos:0<B:=Nat.cast_pos.mpr (V.budget m).B_pos
  have pos:0<β m:=lt_trans zero_lt_one (V.fits.delayed m)
  have posNext:1<β (m+1):=V.fits.delayed _
  have logNext:Real.log (β (m+1))≤2*x:=calc
    _ ≤ Real.log (2*β m):=Real.log_le_log (lt_trans zero_lt_one posNext) next
    _ = Real.log 2+x:= Real.log_mul (by norm_num) pos.ne'
    _ ≤ 2*x:=by have h:=Real.log_le_sub_one_of_pos (show 0<(2:ℝ) by norm_num); linarith
  have fuzz:zz V (m+1)≤2*x:=by
    have bound:=Real.log_le_sub_one_of_pos (Real.log_pos posNext)
    change 1+Real.log (Real.log (β (m+1))) ≤2*x
    linarith
  constructor
  · have lower:2≤B:=by nlinarith [sq_nonneg (x-1)]
    have lower':(2:ℝ)≤((V.budget m).B:ℝ):=lower
    exact_mod_cast lower'
  intro σ sp credit e limit
  have room':4*K*σ⁻¹≤B:=calc
    _ ≤ 4*K*(2*x):=mul_le_mul_of_nonneg_left (credit.trans fuzz) (by positivity)
    _ ≤ x^2:=by nlinarith [mul_le_mul_of_nonneg_right fee (show 0≤x by linarith)]
    _ ≤ B:=grid
  have cleared:=mul_le_mul_of_nonneg_left room' sp.le
  have unit:σ*(4*K*σ⁻¹)=4*K:=by field_simp
  change e/B≤σ/4
  apply (div_le_div_iff₀ bpos (by norm_num : (0:ℝ)<4)).2
  linarith [show 4*K≤σ*B by simpa only [unit] using cleared]

end YM.Integration.WilsonVacuumPreResetLiftedClock
