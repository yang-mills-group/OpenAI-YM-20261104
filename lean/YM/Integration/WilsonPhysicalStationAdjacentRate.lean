import YM.Integration.WilsonPhysicalStationRegisteredFiling
import YM.Integration.WilsonPhysicalStationAdjacentBank
import YM.Integration.WilsonIndependentRegisteredThermalRatios
import YM.Planned.CALIBRATED_MIXED_HISTORY.Bridge

/-! Uniform decay of the signed adjacent payment on the genuinely housed
original blocks and the two original threshold currencies. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationAdjacentRate
open Function Filter Finset RG Labels Source Lattice Wilson Next.Rank Next.Rank.East Next.Rank.Price
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Work.G08 Next.Foundations Bid
open WilsonPhysicalStationRegisteredDiagonal (ratio ceiling ceiling_nonneg)
open WilsonPhysicalStationAdjacentFare (fare)
open WilsonPhysicalStationRegisteredFiling (rate)
open WilsonPhysicalStationAdjacentBank (stock)
open WilsonPhysicalStationRawReading (err)
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G)
local notation "C" => R.family
local notation "A" => R.family.path.levels

private theorem estimate {a c w cm ck em ek δ:ℝ}
    (hc:0 ≤ c)(cap:c ≤ a)(large:1 ≤ a)(bank:1 ≤ w)(old:1+cm ≤ w)(next:1+ck ≤ w)
    (_cmpos:0 ≤ cm)(ckpos:0 ≤ ck)(empos:0 ≤ em)(ekpos:0 ≤ ek)(emax:em ≤ 1)(kmax:ek ≤ 1)
    (light:(1+ck)*ek ≤ 1)(dpos:0 ≤ δ)(dmax:δ ≤ 1) :
    (1+2*cm*(1+em))*fare c δ em ek ck  ≤ 
      30*a*(w*em)+15*(w*δ)+5*a*(w^2*ek) := by
  have aw:0 ≤ a:=zero_le_one.trans large
  have wc:0 ≤ w:=zero_le_one.trans bank
  have coarse:1+2*cm*(1+em) ≤ 5*w:=by
    have half:=mul_le_mul (show 2*cm ≤ 2*w by linarith only [old]) (show 1+em ≤ 2 by linarith only [emax])
      (add_nonneg zero_le_one empos) (mul_nonneg (by norm_num) wc)
    linarith only [half,bank]
  have x:c+δ ≤ 2*a:=by linarith only [cap,large,dmax]
  have u:1+ek+(1+ck)*ek ≤ 3:=by linarith only [kmax,light]
  have positive:0 ≤ 1+ek+(1+ck)*ek:=by positivity
  have y:=mul_le_mul (add_le_add (mul_le_mul_of_nonneg_left x empos) (le_refl δ)) u positive
    (show 0 ≤ em*(2*a)+δ by positivity)
  have y₁:=mul_le_mul cap (mul_le_mul_of_nonneg_right next ekpos)
    (mul_nonneg (add_nonneg zero_le_one ckpos) ekpos) aw
  have pay:fare c δ em ek ck ≤ (em*(2*a)+δ)*3+a*(w*ek):=add_le_add y y₁
  have nonneg:0 ≤ fare c δ em ek ck:=by unfold fare;positivity
  exact (mul_le_mul coarse pay nonneg (by positivity)).trans_eq (by ring)

def grade (h:ℕ):ℝ:=max 1 (ceiling ((C).labels.level h) 2)
def tab (m h:ℕ):ℝ:=
  30*grade R h*((A).clock.monitor m)^(-(7:ℝ)/16)+15*(((C).S.block m).val:ℝ)^(-(5:ℝ)/16)+
    5*grade R h*((A).clock.monitor (m+1))^(-(3:ℝ)/8)

theorem paid (m h:ℕ) (early:0 < m)
    (fine:((C).S.block m).val  ≤  (A).clock.monitor (m+1))
    (coarse:((C).S.block m).val  ≤  (A).clock.monitor m)
    (θ:(A).clock.threshold m  ≤  2*(A).clock.threshold (m+1)):
    rate R m (m+1) h ≤ tab R m h := by
  let l:=(((C).S.block m).val:ℝ)
  let w:=stock R m
  let a:=grade R h
  have hl:1 ≤ l:=by dsimp [l];exact_mod_cast ((C).S.block m).property
  have large:1 ≤ a:=le_max_left .. 
  have aw:0 ≤ a:=zero_le_one.trans large
  have bank:1 ≤ w:=Real.one_le_rpow hl (by norm_num)
  have cash:=WilsonPhysicalStationAdjacentBank.both R m early
  have geo:=WilsonPhysicalStationAdjacentBank.brick R m
  have em:=WilsonPhysicalStationAdjacentBank.heat R m m coarse
  have ek:=WilsonPhysicalStationAdjacentBank.heat R m (m+1) fine
  have eq1:(1+((A).params (m+1)).columns)*err R (m+1)  ≤  1:=by
    have pot:= (mul_le_mul_of_nonneg_right cash.2 (Real.exp_pos _).le).trans ek.1
    exact pot.trans (Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_exp (sq_nonneg _)) (by norm_num))
  have θ₀:0 ≤ ratio R m:=div_nonneg ((A).budget m).threshold_pos.le ((A).budget (m+1)).threshold_pos.le
  have θ₁:ratio R m ≤ 2:=(div_le_iff₀ ((A).budget (m+1)).threshold_pos).mpr θ
  have cap:ceiling ((C).labels.level h) (ratio R m) ≤ a:=by
    apply le_trans _ (le_max_right ..)
    unfold ceiling;apply sum_le_sum;intro i _
    rw [abs_of_nonneg θ₀,abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]
    exact pow_le_pow_left₀ θ₀ θ₁ _
  have refund (i:ℕ):err R i ≤ 1:=Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (Perch.boil_pos _) (by norm_num))
  have bar:barunit ((C).S.block m) ≤ 1:=pow_le_one₀ (inv_nonneg.mpr (Real.rpow_nonneg (zero_le_one.trans hl) _))
      (inv_le_one_of_one_le₀ (Real.one_le_rpow hl (by norm_num : 0 ≤ (1:ℝ)/8)))
  have bill:=estimate (ceiling_nonneg ..) cap large bank cash.1 cash.2
    (zero_le_one.trans ((A).params m).columns_ge) (zero_le_one.trans ((A).params (m+1)).columns_ge)
    (Real.exp_pos _).le (Real.exp_pos _).le (refund m) (refund (m+1)) eq1
    (show 0 ≤ barunit ((C).S.block m) by unfold barunit puffs; positivity) bar
  change rate R m (m+1) h ≤ 30*a*(w*err R m)+15*(w*barunit ((C).S.block m))+5*a*(w^2*err R (m+1)) at bill
  change w*barunit ((C).S.block m)=_ at geo
  rw [geo] at bill
  exact bill.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left em.1 (by positivity)) le_rfl)
    (mul_le_mul_of_nonneg_left ek.2 (by positivity)))

theorem tends (hg:G.Simple) (h:ℕ) : Tendsto (fun m=>tab R m h) atTop (𝓝 0) := by
  have heat:Tendsto (A).clock.monitor atTop atTop :=
    (Station.mag_rate (A) hg (show (0:ℝ) < 1 from zero_lt_one)).congr (fun i=>Real.rpow_one _)
  have wall:=Planned.CalibratedMixedHistory.Bridge.reach (A)
  have a: Tendsto (fun m=>((A).clock.monitor m)^(-(7:ℝ)/16)) atTop (𝓝 0):=by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 7/16)).comp heat using 1
    ext i; simp [neg_div]
  have b: Tendsto (fun m=>(((C).S.block m).val:ℝ)^(-(5:ℝ)/16)) atTop (𝓝 0):=by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/16)).comp wall using 1
    ext i; simp [neg_div]
  have c: Tendsto (fun m=>((A).clock.monitor (m+1))^(-(3:ℝ)/8)) atTop (𝓝 0):=by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 3/8)).comp (heat.comp (tendsto_add_atTop_nat 1)) using 1
    ext i; simp [neg_div]
  simpa [tab] using (((a.const_mul (30*grade R h)).add (b.const_mul 15)).add (c.const_mul (5*grade R h)))

theorem original (hg:G.Simple) (h:ℕ) {ε:ℝ} (goal:0 < ε):
    ∀ᶠ m:ℕ in atTop,
      ((C).S.block m).val  ≤  (A).clock.monitor m →
      ((C).S.block m).val  ≤  (A).clock.monitor (m+1) →
      rate R m (m+1) h  <  ε :=by
  filter_upwards [eventually_ge_atTop 1,(tends R hg h).eventually_lt_const goal,
    WilsonIndependentRegisteredThermalRatios.appointed R hg] with m pos small ratioOK big bigger
  exact (paid R m h pos bigger big ratioOK.1).trans_lt small

end YM.Integration.WilsonPhysicalStationAdjacentRate
end
