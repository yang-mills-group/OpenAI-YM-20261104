import YM.Integration.WilsonReportHarvestSourceReach
import YM.Integration.WilsonMarkedUltravioletReportingReserve

/-! Dated distance and forfeit on the full admitted roster, with the original running beta and scale gap. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestResidentCalendar
open Filter Real Lattice RG Wilson PhysicalNext.Repeat.Legato
open WilsonMeasuredAdmission WilsonReportHarvestSourceReach
open scoped Topology
variable {G:Gauge} (R:Run G)(simple:G.Simple)
local notation "A"=>R.family.path.levels
local notation "S"=>R.family.S
local notation "H"=>(A).clock.hatBeta

private theorem cubic (e:ℝ)(ep:0 ≤ e):(1+e)^3 ≤ 27*Real.exp e:=by
  have a:1+e ≤ 3*Real.exp (e/3):=by linarith only [Real.add_one_le_exp (e/3)]
  have exp3:(Real.exp (e/3))^3=Real.exp e:=by rw [←Real.exp_nat_mul]; congr 1;ring
  calc (1+e)^3 ≤ (3*Real.exp (e/3))^3:=pow_le_pow_left₀ (by linarith) a 3
       _=27*Real.exp e:=by rw [mul_pow,exp3];norm_num

include simple in
/-- Every preassigned logarithmic wallet and scale-gap debit fits ALL the actual masts over every larger date. -/
theorem housing {c t:ℝ}(cp:0 ≤ c)(tp:0 ≤ t):
    ∀ᶠm:ℕ in atTop,∀j:ℕ,∀mj:m ≤ j,∀per:ℕ,
      let B:=((A).budget j).B
      reach A c t m j*(4*B+2)+2*B ≤ 
        ((S).toDepth mj per).count.val*((A).budget m).B^2:=by
  let K:=50*(c+t+1)
  have kp:0<K:=by dsimp [K];positivity
  have hot:=Next.Rank.Station.hat_rate A simple
  have loghot:=Real.tendsto_log_atTop.comp hot
  filter_upwards [hot.eventually_ge_atTop G.slopeConstant,loghot.eventually_ge_atTop (max 2 (216*K))]
    with m slope tall j mj per B
  let z:=Real.log (H m)
  let e:=elapsed S m j
  let x:=mast A j
  let X:=mast A m
  let Bm:=((A).budget m).B
  let F:=depth A c 1 j
  let Hh:=depth A (t*e) 0 j
  have e0:0 ≤ e:=sub_nonneg.mpr ((OPE.scale_mono S).monotone mj)
  have x1:1 ≤ x:=(mast_gt_one A j).le
  have X1:1 ≤ X:=(mast_gt_one A m).le
  have z2:2 ≤ z:=(le_max_left ..).trans tall
  have z0:0 ≤ z:=by linarith only [z2]
  have zspace:216*K ≤ z:=(le_max_right ..).trans tall
  have hm:0<H m:=zero_lt_one.trans ((A).fits.delayed m)
  have hj:0<H j:=zero_lt_one.trans ((A).fits.delayed j)
  have logdiff:=Real.log_le_sub_one_of_pos (div_pos hj hm)
  rw [Real.log_div hj.ne' hm.ne'] at logdiff
  have clock:H j-H m=G.slopeConstant*e:=by
    unfold Calendar.hatBeta
    change _+_*((S).scale j)-(_+_*((S).scale m))=_*((S).scale j-(S).scale m)
    ring
  have step:H j/H m-1 ≤ e:=by
    rw [div_sub_one hm.ne',(div_le_iff₀ hm),clock,mul_comm e]
    exact mul_le_mul_of_nonneg_right slope e0
  have grow:x ≤ X*(1+e):=by
    have v:Real.log (H j)-Real.log (H m) ≤ e:=logdiff.trans step
    calc x ≤ X+e:=by change 2+Real.log (H j) ≤ (2+Real.log (H m))+e;linarith only [v]
         _ ≤ X*(1+e):=by nlinarith only [mul_nonneg (sub_nonneg.mpr X1) e0]
  have Xz:X ≤ 2*z:=by change 2+z ≤ 2*z;linarith
  have bm:z^2 ≤ (Bm:ℝ):=Nat.le_ceil _
  have area:27*K*X^3 ≤ (Bm:ℝ)^2:=calc
    _ ≤ 27*K*(2*z)^3:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans X1) Xz 3) (by positivity)
    _=(216*K)*z^3:=by ring
    _ ≤ z*z^3:=mul_le_mul_of_nonneg_right zspace (pow_nonneg z0 _)
    _=(z^2)^2:=by ring
    _ ≤ _:=pow_le_pow_left₀ (sq_nonneg _) bm 2
  have fcost:=cost A j 1 cp
  have hcost:=cost A j 0 (mul_nonneg tp e0)
  change ((F*(4*B+2)+2*B+1:ℕ):ℝ) ≤ (10*(c+1)+5)*x^3 at fcost
  change ((Hh*(4*B+2)+2*B+1:ℕ):ℝ) ≤ (10*(t*e+1)+5)*x^2 at hcost
  have sum:reach A c t m j*(4*B+2)+2*B ≤ 
      (F*(4*B+2)+2*B+1)+(Hh*(4*B+2)+2*B+1):=by
    change (F+Hh)*(4*B+2)+2*B ≤ _
    rw [Nat.add_mul];omega
  have two:10*(t*e+1)+5 ≤ (10*(t+1)+5)*(1+e):=by nlinarith only [tp,e0]
  have x2:0 ≤ x^2:=sq_nonneg _
  have tcost:(10*(t*e+1)+5)*x^2 ≤ (10*(t+1)+5)*(X^3*(1+e)^3):=calc
    _ ≤ ((10*(t+1)+5)*(1+e))*(X*(1+e))^2:=mul_le_mul two
      (pow_le_pow_left₀ (zero_le_one.trans x1) grow 2) x2 (by positivity)
    _=(10*(t+1)+5)*(X^2*(1+e)^3):=by ring
    _ ≤ _:=by
      gcongr
      norm_num
  have ccost:(10*(c+1)+5)*x^3 ≤ (10*(c+1)+5)*(X^3*(1+e)^3):=by
    rw [←mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans x1) grow 3) (by positivity)
  have costK:(10*(c+1)+5)+(10*(t+1)+5) ≤ K:=by dsimp only [K];linarith only [cp,tp]
  have ratio:(Real.exp e)=((S).toDepth mj per).count.val:=by
    rw [mesh]
    apply (div_eq_iff ((S).a_pos _).ne').mpr
    simpa [mul_comm] using ((S).embeds_scale ((S).toDepth mj per)).symm
  have achieved:((reach A c t m j*(4*B+2)+2*B:ℕ):ℝ) ≤ (((S).toDepth mj per).count.val:ℝ)*(Bm:ℝ)^2:=calc
    _ ≤ ((F*(4*B+2)+2*B+1:ℕ):ℝ)+((Hh*(4*B+2)+2*B+1:ℕ):ℝ):=by exact_mod_cast sum
    _ ≤ (10*(c+1)+5)*(X^3*(1+e)^3)+(10*(t+1)+5)*(X^3*(1+e)^3):=
      add_le_add (fcost.trans ccost) (hcost.trans tcost)
    _ ≤ K*(X^3*(1+e)^3):=by rw [←add_mul];exact mul_le_mul_of_nonneg_right costK (by positivity)
    _ ≤ K*(X^3*(27*Real.exp e)):=by gcongr;exact cubic e e0
    _=(27*K*X^3)*Real.exp e:=by ring
    _ ≤ (Bm:ℝ)^2*Real.exp e:=mul_le_mul_of_nonneg_right area (Real.exp_pos _).le
    _=_:=by rw [ratio,mul_comm]
  exact_mod_cast achieved

include simple in
/-- The same traversal removes one unit of exponential support, with all three string tolls and the engineering scale included. -/
theorem forfeit (p T h:ℕ){ε:ℝ}(ep:0<ε):
    ∀ᶠj:ℕ in atTop,∀m:ℕ,m ≤ j → ∀N:ℕ,j ≤ N → ∀per:ℕ,
      let d:=elapsed S m j
      let D:=reach A ((T:ℝ)+p+1) ((h:ℝ)+3) m j
      ((S).a m/(S).a j)^h*(H j)^T*Real.exp (3*d)*Real.exp (-(D:ℝ)) ≤ 
        ε*((Real.sqrt (R.family.path.rep N per j).beta)⁻¹)^p:=by
  have grown:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate A simple)
  filter_upwards [grown.eventually_ge_atTop (max (Real.log 2) (-Real.log ε))] with j funded m mj N live per e D
  let z:=Real.log (H j)
  let y:=(R.family.path.rep N per j).beta
  let c:ℝ:=(T:ℝ)+p+1
  have jp:0<H j:=zero_lt_one.trans ((A).fits.delayed j)
  have zp:0 ≤ z:=Real.log_nonneg ((A).fits.delayed j).le
  have two:Real.log 2 ≤ z:=(le_max_left ..).trans funded
  have eps:-Real.log ε ≤ z:=(le_max_right ..).trans funded
  have low: c*(mast A j) ≤ (depth A c 1 j:ℝ):=by
    change c*(mast A j) ≤ (⌈c*(mast A j)^1⌉₊:ℝ)
    rw [pow_one];exact Nat.le_ceil _
  have later:((h:ℝ)+3)*e ≤ (depth A (((h:ℝ)+3)*e) 0 j:ℝ):=by
    change _ ≤ (⌈(((h:ℝ)+3)*e)*(mast A j)^0⌉₊:ℝ);rw [pow_zero,mul_one];exact Nat.le_ceil _
  have total:c*z+((h:ℝ)+3)*e ≤ (D:ℝ):=by
    change c*z+_ ≤ ((depth A c 1 j+depth A (((h:ℝ)+3)*e) 0 j:ℕ):ℝ)
    push_cast
    apply add_le_add _ later
    exact (mul_le_mul_of_nonneg_left (by change z ≤ 2+z;linarith) (by dsimp [c];positivity)).trans low
  have band:=(R.makes.wilson.represents N per j live).band
  have yp:0<y:=(half_pos jp).trans_le band.1
  have yl:Real.log y ≤ Real.log (2*H j):=Real.log_le_log yp band.2
  rw [Real.log_mul (by norm_num:(2:ℝ)≠0) jp.ne'] at yl
  have py:(p:ℝ)*Real.log y ≤ (p:ℝ)*(2*z):=mul_le_mul_of_nonneg_left
    (by change Real.log y ≤ Real.log 2+z at yl;linarith only [yl,two]) (Nat.cast_nonneg _)
  have gp:0<(Real.sqrt y)⁻¹:=inv_pos.mpr (Real.sqrt_pos.2 yp)
  have glog:Real.log (Real.sqrt y)⁻¹=-(Real.log y)/2:=by rw [Real.log_inv,Real.log_sqrt yp.le];ring
  have fx:(H j)^T=Real.exp ((T:ℝ)*z):=by
    change (H j)^T=Real.exp ((T:ℝ)*Real.log (H j))
    rw [←Real.log_pow,Real.exp_log (pow_pos jp T)]
  rw [←mesh,←Real.exp_nat_mul,fx,←Real.exp_add,←Real.exp_add,←Real.exp_add]
  calc _ ≤ Real.exp (Real.log ε+(p:ℝ)*Real.log (Real.sqrt y)⁻¹):=by
          rw [Real.exp_le_exp,glog]
          dsimp only [c] at total
          linarith only [total,eps,py]
       _=ε*((Real.sqrt y)⁻¹)^p:=by rw [Real.exp_add,Real.exp_log ep,←Real.log_pow,Real.exp_log (pow_pos gp _)]

end YM.Integration.WilsonReportHarvestResidentCalendar
