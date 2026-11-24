import YM.OPE.Therm.Rite
import YM.MSbar.Atlas.Apex

/-! The original AngularFare scalar receipt and adjacent two-site room on their genuine numerical and reflection inputs. The before-run choice in the physical gate is the same cutoff for the same eventual inequality. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingForestAngularFare
open Filter Lattice RG Next.Rank MSbar.Heath.Stock
open scoped Topology

def angularCut (x:ℝ) : ℝ := cue x * Real.log x * Real.sqrt (Real.sqrt (Real.log x))

theorem angular_fare (G:Gauge) (B:Stage) (L:Side) (K:ℕ) :
    ∀ᶠ x:ℝ in atTop,∀ g:ℝ,0<g → g ≤ 2*cue x →
      Real.exp ((L.val:ℝ)^4*(Vac.fiat G B x+Fintype.card PlaqAxes) -
        angularCut x/(g/strength B.clip)) ≤ (x⁻¹)^K := by
  let A:=Vac.fiat G B 1+(Fintype.card PlaqAxes:ℝ)
  let c:=(L.val:ℝ)^4*(|A|+2*Module.finrank ℝ G.Mat)+(K:ℝ)
  let b:=strength B.clip
  have c0:0 ≤ c := by dsimp only [c]; positivity
  have bp:0<b:=strength_pos _
  have grow:=Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,grow.eventually_ge_atTop (2*c/b),
    eventually_gt_atTop (0:ℝ)] with x hlog far hx g hg high
  let t:=Real.log x
  let u:=Real.sqrt (Real.sqrt t)
  have t0:0 ≤ t := zero_le_one.trans hlog
  have lin:Vac.fiat G B x+Fintype.card PlaqAxes=A+2*Module.finrank ℝ G.Mat*t:=by
    dsimp only [A,t,Vac.fiat];rw [Real.log_one];ring
  have hA:A≤|A| *t:=(le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hlog)
  have cost:(L.val:ℝ)^4*(Vac.fiat G B x+Fintype.card PlaqAxes)+(K:ℝ)*t ≤ c*t:=by
    rw [lin];dsimp only [c];calc
      _ ≤ (L.val:ℝ)^4*(|A| *t+2*Module.finrank ℝ G.Mat*t)+(K:ℝ)*t := by
        nlinarith only [mul_le_mul_of_nonneg_left hA (show 0 ≤ (L.val:ℝ)^4 by positivity)]
      _ = _ := by ring
  have power:2*c ≤ u*b := (div_le_iff₀ bp).mp far
  have paid:c*t ≤ angularCut x/(g/b):=by
    rw [div_div_eq_mul_div,le_div_iff₀ hg]
    calc
      _ ≤ c*t*(2*cue x):=mul_le_mul_of_nonneg_left high (mul_nonneg c0 t0)
      _ = cue x*t*(2*c):=by ring
      _ ≤ cue x*t*(u*b):=mul_le_mul_of_nonneg_left power
        (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) t0)
      _ = angularCut x*b:=by unfold angularCut;dsimp only [t,u];ring
  calc
    _ ≤ Real.exp (-((K:ℝ)*t)):=Real.exp_monotone (by linarith only [cost,paid])
    _ = _:=by rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log hx,inv_pow]

open YM.Wilson Push.GridApprox
theorem adjacent_room {G:Gauge} (A:Levels G) : ∀ᶠ j:ℕ in atTop, room A j (j+1) 2 := by
  have pos:=Real.log_pos (one_lt_two (α:=ℝ))
  filter_upwards [((tendsto_natCast_atTop_atTop (R:=ℝ)).comp (A.fits.deep.comp (tendsto_add_atTop_nat 1))).eventually_ge_atTop (370/Real.log 2)] with j due
  let p:=A.params (j+1)
  let L:ℝ:=(A.S.block j).val
  have large:1<L:=by have h:=A.S.block_large j;unfold L;exact_mod_cast (show 1<(A.S.block j).val from lt_of_lt_of_le (by decide) h)
  let K:=(A.clock.J (j+1):ℝ)
  have order:1≤K:=by have hz:=A.clock.adm (j+1);unfold K;exact_mod_cast (by omega : 1 ≤ A.clock.J (j+1))
  let x:=1+p.paths+p.width⁻¹+p.columns+p.clip.relaxation+p.supportExponent
  have wide:2≤x:=by unfold x;linarith only [p.paths_pos,p.clip.radius_pos,p.columns_ge,p.price_pos,inv_pos.mpr p.width_pos]
  have bound:=(div_le_iff₀ (Real.log_pos large)).mp (show Real.log x / Real.log L ≤ (K^2)⁻¹ from A.fits.logCost j)
  rw [inv_mul_eq_div] at bound
  have growth:=(le_div_iff₀ (show 0<K^2 by positivity)).mp ((Real.log_le_log two_pos wide).trans bound)
  have slack:370*K≤L-1:=calc
    _ ≤ Real.log 2*K^2 := by change 370/Real.log 2 ≤ K at due;nlinarith only [mul_le_mul_of_nonneg_right ((div_le_iff₀ pos).mp due) (zero_le_one.trans order)]
    _ ≤ Real.log L:=growth
    _ ≤ L-1:= Real.log_le_sub_one_of_pos (zero_lt_one.trans large)
  let t:=A.S.a j
  have t0:0<t:=A.S.a_pos _
  have enough:2*((2:ℝ)+30*(K+5))<L:=by linarith only [slack,order]
  unfold Push.GridApprox.room Push.GridApprox.tail
  rw [A.S.a_step];push_cast
  change 2*(t/L*2+30*(t/L)*(K+5))<t
  field_simp;linarith [mul_lt_mul_of_pos_left enough t0]

end YM.Integration.WilsonReportingForestAngularFare
