import YM.Integration.WilsonPhysicalStationAdjacentRate
import YM.Integration.WilsonPhysicalStationCoincidentRate
import YM.Integration.WilsonPhysicalPositionWeakRoofCrossings
/-! The previous and current paid block on the true reporter clock. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationDatedWidth
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

open WilsonPhysicalStationAdjacentRate (grade tab)
open MergeProof.East (topL)
lemma block (k:ℕ):(((C).S.block k).val:ℝ) ≤ topL (A) (k+1):=by
  rw [←(A).fits.sameFactor]
  exact le_max_left ..
lemma earlier (m:ℕ)(early:0 < m):
    1+((A).params m).columns ≤ stock R (m-1):=by
  simpa only [show (m-1)+1=m by omega] using WilsonPhysicalStationAdjacentBank.first R (m-1)
lemma sheltered (m:ℕ)(early:0 < m)(home:topL (A) m ≤ (A).clock.monitor m):
    (((C).S.block (m-1)).val:ℝ) ≤ (A).clock.monitor m:=by
  apply le_trans _ home
  simpa only [show (m-1)+1=m by omega] using block R (m-1)
private theorem estimate {a c v w cm ck em ek δ:ℝ}
    (hc:0  ≤  c)(cap:c  ≤  a)(large:1  ≤  a)(bank:1  ≤  v)(old:1+cm  ≤  v)(next:1+ck  ≤  w)
    (_cmpos:0  ≤  cm)(ckpos:0  ≤  ck)(empos:0  ≤  em)(ekpos:0  ≤  ek)(emax:em  ≤  1)(kmax:ek  ≤  1)
    (light:(1+ck)*ek  ≤  1)(dpos:0  ≤  δ)(dmax:δ  ≤  1) :
    (1+2*cm*(1+em))*fare c δ em ek ck   ≤  
      30*a*(v*em)+15*(v*δ)+5*a*(v*w*ek) := by
  have aw:0  ≤  a:=zero_le_one.trans large
  have wc:0  ≤  v:=zero_le_one.trans bank
  have coarse:1+2*cm*(1+em)  ≤  5*v:=by
    have half:=mul_le_mul (show 2*cm  ≤  2*v by linarith only [old]) (show 1+em  ≤  2 by linarith only [emax])
      (add_nonneg zero_le_one empos) (mul_nonneg (by norm_num) wc)
    linarith only [half,bank]
  have x:c+δ  ≤  2*a:=by linarith only [cap,large,dmax]
  have u:1+ek+(1+ck)*ek  ≤  3:=by linarith only [kmax,light]
  have positive:0  ≤  1+ek+(1+ck)*ek:=by positivity
  have y:=mul_le_mul (add_le_add (mul_le_mul_of_nonneg_left x empos) (le_refl δ)) u positive
    (show 0  ≤  em*(2*a)+δ by positivity)
  have y₁:=mul_le_mul cap (mul_le_mul_of_nonneg_right next ekpos)
    (mul_nonneg (add_nonneg zero_le_one ckpos) ekpos) aw
  have pay:fare c δ em ek ck  ≤  (em*(2*a)+δ)*3+a*(w*ek):=add_le_add y y₁
  have nonneg:0  ≤  fare c δ em ek ck:=by unfold fare;positivity
  exact (mul_le_mul coarse pay nonneg (by positivity)).trans_eq (by ring)

theorem advance (m h:ℕ) (early:0 < m)
    (high:topL (A) (m+1)  ≤  (A).clock.monitor (m+1))
    (low:topL (A) m  ≤  (A).clock.monitor m)
    (θ:(A).clock.threshold m   ≤   2*(A).clock.threshold (m+1)):
    rate R m (m+1) h  ≤  tab R m h := by
  let l:=(((C).S.block m).val:ℝ)
  let w:=stock R m
  let v:=stock R (m-1)
  let a:=grade R h
  have hl:1  ≤  l:=by dsimp [l];exact_mod_cast ((C).S.block m).property
  have large:1  ≤  a:=le_max_left .. 
  have aw:0  ≤  a:=zero_le_one.trans large
  have bank:1  ≤  v:=Real.one_le_rpow (by exact_mod_cast ((C).S.block (m-1)).property) (by norm_num)
  have vw:v ≤ w:=Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (((C).S.block (m-1)).val:ℝ)) (WilsonPhysicalStationAdjacentBank.block_mono R (Nat.sub_le m 1)) (by norm_num)
  have cash:=WilsonPhysicalStationAdjacentBank.both R m early
  have geo:=WilsonPhysicalStationAdjacentBank.brick R m
  have em:=WilsonPhysicalStationAdjacentBank.heat R (m-1) m (sheltered R m early low)
  have ek:=WilsonPhysicalStationAdjacentBank.heat R m (m+1) ((block R m).trans high)
  have eq1:(1+((A).params (m+1)).columns)*err R (m+1)   ≤   1:=by
    have pot:= (mul_le_mul_of_nonneg_right cash.2 (Real.exp_pos _).le).trans ek.1
    exact pot.trans (Real.rpow_le_one_of_one_le_of_nonpos (Real.one_le_exp (sq_nonneg _)) (by norm_num))
  have θ₀:0  ≤  ratio R m:=div_nonneg ((A).budget m).threshold_pos.le ((A).budget (m+1)).threshold_pos.le
  have θ₁:ratio R m  ≤  2:=(div_le_iff₀ ((A).budget (m+1)).threshold_pos).mpr θ
  have cap:ceiling ((C).labels.level h) (ratio R m)  ≤  a:=by
    apply le_trans _ (le_max_right ..)
    unfold ceiling;apply sum_le_sum;intro i _
    rw [abs_of_nonneg θ₀,abs_of_nonneg (by norm_num : 0  ≤  (2:ℝ))]
    exact pow_le_pow_left₀ θ₀ θ₁ _
  have refund (i:ℕ):err R i  ≤  1:=Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (Perch.boil_pos _) (by norm_num))
  have bar:barunit ((C).S.block m)  ≤  1:=pow_le_one₀ (inv_nonneg.mpr (Real.rpow_nonneg (zero_le_one.trans hl) _))
      (inv_le_one_of_one_le₀ (Real.one_le_rpow hl (by norm_num : 0  ≤  (1:ℝ)/8)))
  have bill:=estimate (ceiling_nonneg ..) cap large bank (earlier R m early) cash.2
    (zero_le_one.trans ((A).params m).columns_ge) (zero_le_one.trans ((A).params (m+1)).columns_ge)
    (Real.exp_pos _).le (Real.exp_pos _).le (refund m) (refund (m+1)) eq1
    (show 0  ≤  barunit ((C).S.block m) by unfold barunit puffs; positivity) bar
  change rate R m (m+1) h  ≤  30*a*(v*err R m)+15*(v*barunit ((C).S.block m))+5*a*(v*w*err R (m+1)) at bill
  change w*barunit ((C).S.block m)=_ at geo
  have mid:= (mul_le_mul_of_nonneg_right vw (show 0 ≤ barunit ((C).S.block m) by unfold barunit puffs; positivity)).trans_eq geo
  have top:v*w*err R (m+1) ≤ ((A).clock.monitor (m+1))^(-(3:ℝ)/8):=by
    apply le_trans _ ek.2
    rw [pow_two]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right vw (by dsimp [w,stock];positivity)) (Real.exp_pos _).le
  exact bill.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left em.1 (by positivity)) (mul_le_mul_of_nonneg_left mid (by norm_num)))
    (mul_le_mul_of_nonneg_left top (by positivity)))

open WilsonPhysicalStationCoincidentRate (tariff)
open WilsonPhysicalStationCoincidentEntry (rent)
theorem coincident (m:ℕ) (early:0 < m)(home:topL (A) m  ≤  (A).clock.monitor m):
    rent R m  ≤  tariff R m:=by
  let c:=((A).params m).columns
  let x:=err R m
  let w:=stock R (m-1)
  have cw:1+c  ≤  w:=earlier R m early
  have one:1  ≤  c:=((A).params m).columns_ge
  have xp:0  ≤  x:=(Real.exp_pos _).le
  have xmax:x  ≤  1:=by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by norm_num)
  have raw:2*c*(1+x)  ≤  2*c*2:=mul_le_mul_of_nonneg_left (by linarith only [xmax]) (by linarith only [one])
  have cap:1+2*c*(1+x)  ≤  5*w:=by linarith only [raw,cw,one]
  have heat: w*x  ≤  ((A).clock.monitor m)^(-(7:ℝ)/16):=(WilsonPhysicalStationAdjacentBank.heat R (m-1) m (sheltered R m early home)).1
  calc
    rent R m  ≤  (5*w)*(2*x):=mul_le_mul_of_nonneg_right cap (by linarith only [xp])
    _=10*(w*x):=by ring
    _ ≤ tariff R m:=mul_le_mul_of_nonneg_left heat (by norm_num)
end YM.Integration.WilsonPhysicalStationDatedWidth
end
