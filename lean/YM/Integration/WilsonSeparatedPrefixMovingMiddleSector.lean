import YM.Integration.WilsonSeparatedPrefixMovingPinController
import YM.Integration.WilsonSeparatedPrefixMovingPairSector
import YM.Integration.WilsonSeparatedPrefixMovingUnformedCash
import YM.Integration.WilsonSeparatedPrefixMovingMiddleIncome
import YM.Integration.WilsonSeparatedPrefixMovingFineDeposit

/-! First contact of the actual distant column with the complete distinct
ordinary product, uniformly in the top and at every scalar grade. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingMiddleSector
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingFineFare (unitFee)
open Finset
open WilsonSeparatedPrefixMovingPinController (Sites collected still)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e n:ℕ}{E:Credit}

open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonSeparatedPrefixMovingWages (label effort coupon)
open WilsonSeparatedPrefixMovingLocator (booked)

def joined (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N q:ℕ)(ω:Fin 0→YForest G)(i:ℕ):ℝ:=
  let ext:=current R F ψ Y t (i+1) N (y / paceT R.draws.S m t) o
  let near:=locale o (LodeStar R.draws R.paid φ X m (i+1) N y)
  (cruises R.draws R.paid N (F.h+capP Q) i older (JoinGap R.draws R.paid i N F.h (capP Q) ext near)).2 q 0 ω

def mountedRow {u:ℕ}(R:Realm G (e+1) E)(canvas:Sites G e u)(Q:Fin (n+1)→SealR G)(F:SealR G)(φ:Wilt Q)(ψ:Rarity F.D)
    (X:Herit Q)(Y:F.Rider)(o:CellR)(y:ℝ)(t m older N q:ℕ)(ω:Fin 0→YForest G)(i:ℕ):ℝ:=
  let ext:=current R F ψ Y t (i+1) N (y / paceT R.draws.S m t) o
  let near:=locale o (LodeStar R.draws R.paid φ X m (i+1) N y)
  (collected R canvas (F.h+capP Q) N i older (JoinGap R.draws R.paid i N F.h (capP Q) ext near)).2 q 0 ω

theorem mounted (H:Hol G)(Q:Fin (n+1)→SealR G)(F:SealR G)(k e u target:ℕ)(E W V S D Wo:Credit):
    let extra:=u+target+2
    let a:=F.h+extra
    ∃C:Credit,∀(R:Realm G (e+1) E)(canvas:Sites G e u)(_P:SpringD R k u a W)(_end:Dormitory R (F.h+capP Q) u Wo)
      (_near:HorizonP H R W V Q)(_far:PassportC H R F W V)
      (_spring:SpringD R (capP Q) (u+a) (capP Q+2) S)(_dorm:Dormitory R (capP Q) (u+a) D)
      (older t b m N:ℕ)(_gate:R.anchor ≤ older)(_start:older ≤ t)(_home:t ≤ b)(_fine:b ≤ m)(_top:m ≤ N)
      (_room:F.h+capP Q ≤ k)(φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)(o:CellR)
      (y g r DF:ℝ)(B:Fin (n+1)→ℝ),
      let T:=paceT R.draws.S b t
      let v:=y / paceT R.draws.S m b
      let Z:=epoch R older m
      let bill:=(16*r)^u*(g⁻¹)^a*coupon F Y e (u+a) r DF*9^(u+a)*(∏s,B s*fee (Q s) e (X s))
      0 < g → Bough Q φ y Z B → Amplitude ψ DF →
      2+2*|v| ≤ r → ψ.radius+|v/T|+1 ≤ r →
      (∀q∈tsupport ψ.ψ.val,T*g+1+|v| ≤ ‖T • q‖) →
      ∀q ≤ e,∀ω:Fin 0→YForest G,‖∑d∈range (m-b),mountedRow R canvas Q F φ ψ X Y o y t m older N q ω (b+d)‖ ≤ 
        Z*((T^target)⁻¹*bill*C.buy Z):=by
  intro extra a
  obtain ⟨near,purse⟩:=WilsonSeparatedPrefixMovingMiddleIncome.original (H:=H) Q e (u+a) E W V S D
  obtain ⟨finish,earn⟩:=WilsonSeparatedPrefixMovingPinController.earlier G (F.h+capP Q) e u E Wo
  let C:=((finish.prodC (effort G e k u a E W)).prodC (label H F e (u+a) E W V)).prodC near
  refine ⟨C,?_⟩
  intro R canvas P ender covered far spring dorm older t b m N gate start home fine top room φ ψ X Y o
    y g r DF B T v Z bill pos stocks amp nearBox farBox remote q hq ω
  have contract:=window R older b m gate (by omega) fine
  have ok:1 ≤ Z:=contract.1
  have scalar:0 ≤ ∏s,B s*fee (Q s) e (X s):=Finset.prod_nonneg fun s _=>
    mul_nonneg (stocks.lanes s).1 (Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _)
  have t1:1 ≤ T:=pace_ge R.draws.S home
  have t0:0 < T:=pace_pos ..
  have f0:0 ≤ fee F e Y:=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have r0:0 ≤ r:=by linarith only [nearBox,abs_nonneg v]
  have cp:0 ≤ C.buy Z:=zero_le_one.trans (C.purchase ok)
  have wallet:0 ≤ bill:=by
    have quote:0 ≤ coupon F Y e (u+a) r DF:=by unfold coupon;have:=amp.1;positivity
    dsimp only [bill];positivity
  have gross:0 ≤ (T^target)⁻¹*bill*C.buy Z:=by positivity
  have center:v/T=y/paceT R.draws.S m t:=by
    dsimp only [T,v,paceT];field_simp [(R.draws.S.a_pos b).ne',(R.draws.S.a_pos m).ne',(R.draws.S.a_pos t).ne']
  have one (d:ℕ)(hd:d < m-b):‖mountedRow R canvas Q F φ ψ X Y o y t m older N q ω (b+d)‖ ≤ 
      (T^target)⁻¹*bill*C.buy Z:=by
    let i:=b+d
    have base:b ≤ i:=Nat.le_add_right _ _
    have edge:i < m:=by dsimp only [i];omega
    let x:=paceT R.draws.S b (i+1)
    have xp:0 < x:=pace_pos ..
    have x1:x ≤ 1:=pace_le R.draws.S (by omega)
    let η:=paceT R.draws.S b i
    have ep:0 < η:=pace_pos ..
    have e1:η ≤ 1:=pace_le R.draws.S base
    let P₀:=locale o (LodeStar R.draws R.paid φ X m (i+1) N y)
    let E₀:=current R F ψ Y t (i+1) N (v/T) o
    let delta:=JoinGap R.draws R.paid i N F.h (capP Q) E₀ P₀
    have farDate:paceT R.draws.S t (i+1)=x/T:=by
      dsimp only [x,T,paceT];field_simp [(R.draws.S.a_pos b).ne',(R.draws.S.a_pos t).ne']
    have truth:mountedRow R canvas Q F φ ψ X Y o y t m older N q ω i=
        (collected R canvas (F.h+capP Q) N i older delta).2 q 0 ω:=by
      dsimp only [mountedRow,delta,E₀,P₀];rw [center]
    rw [truth]
    by_cases visits:(VisitsT ψ (x/T) (v/T) o).Nonempty
    · have clock:Compar R.draws.S R.y t (i+1) ≤ Z:=
        ((compar_age R.draws.S R.y t) (show i+1 ≤ m by omega)).trans (window R older t m gate start (by omega)).2.2.1
      have inner:=purse R covered spring dorm m (i+1) N φ X B Z y o (by omega) (by omega) top
        (window R older (i+1) m gate (by omega) (by omega)).2.2.2 stocks
      let prior:=near.buy Z*∏s,B s*fee (Q s) e (X s)
      have billC:=WilsonSeparatedPrefixMovingLiveDeposit.original F (capP Q) k e u a target 2 extra 0
        rfl (by dsimp only [a,extra];omega) E W V R P far t b i N (by omega) home base (by omega)
        room P₀ inner.1 (booked v o) ψ Y v g r Z prior DF o inner.2 clock amp pos
        (WilsonSeparatedPrefixMovingLocator.site x v o xp) (WilsonSeparatedPrefixMovingLocator.separated ψ T g v o remote)
        (by change radiusH (booked v o) (paceT R.draws.S b (i+1)*(R.draws.S.block i).val) v ≤ r
            rw [pace_step];exact (WilsonSeparatedPrefixMovingLocator.paid η v o ep.le e1).trans nearBox)
        (by change radiusH ψ (paceT R.draws.S b (i+1)*(R.draws.S.block i).val/T) (v/T) ≤ r
            rw [pace_step];unfold radiusH;rw [abs_of_nonneg (div_nonneg ep.le t0.le)]
            linarith only [farBox,div_le_one_of_le₀ (e1.trans t1) t0.le]) visits
      let z:=R.cash (priceWG G e k u a E W) i
      let tariff:=(16*r)^u*(((ll R.draws i).L.val:ℝ)/g)^a
      let ext:=unitFee (H:=H) (E:=E) (W:=W) (V:=V) (e:=e) (b:=u+a) F Y ψ Z (x/T) (v/T) DF
      have received:=earn R canvas ender older b i N gate (by omega) base (by omega) delta billC.2.1 _
        (by rw [←pace_step R.draws.S b i];exact billC.2.2) q hq ω
      have close:=WilsonSeparatedPrefixMovingInvoice.credit R finish older i m gate (by omega) edge.le
      have tariffed:=WilsonSeparatedPrefixMovingInvoice.salary (e:=e) (W:=W) R older i m k u a gate (by omega)
        edge.le r g r0 pos
      have tested:radiusH ψ (x/T) (v/T) ≤ r:=by
        unfold radiusH
        rw [abs_of_nonneg (div_nonneg xp.le t0.le)]
        linarith only [farBox,div_le_one_of_le₀ (x1.trans t1) t0.le]
      have ec:=WilsonSeparatedPrefixMovingInvoice.desk (H:=H) (E:=E) (W:=W) (V:=V) (e:=e)
        F Y ψ (u+a) Z (x/T) (v/T) r DF ok tested amp
      have nc:WilsonSeparatedPrefixMovingInvoice.Earned Z near prior (∏s,B s*fee (Q s) e (X s)):=
        ⟨mul_nonneg (zero_le_one.trans (near.purchase ok)) scalar,le_rfl⟩
      have quoted:=((close.mul tariffed).mul ec).mul nc
      have rates:(T^2)⁻¹*x^extra ≤ 1:=mul_le_one₀ (inv_le_one_of_one_le₀ (one_le_pow₀ t1))
        (pow_nonneg xp.le _) (pow_le_one₀ xp.le x1)
      refine received.trans ?_
      calc
        _=(T^target)⁻¹*9^(u+a)*(((T^2)⁻¹*x^extra)*
            (finish.buy (epoch R older i)*(z*tariff)*ext*prior)):=by ring
        _ ≤ (T^target)⁻¹*9^(u+a)*(1*(finish.buy (epoch R older i)*(z*tariff)*ext*prior)):=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right rates quoted.floor) (by positivity)
        _ ≤ (T^target)⁻¹*9^(u+a)*(1*(C.buy Z*(1*((16*r)^u*g⁻¹^a)*coupon F Y e (u+a) r DF*
          (∏s,B s*fee (Q s) e (X s))))):=by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left quoted.grant zero_le_one) (by positivity)
        _=_:=by dsimp only [bill];ring
    · have vacant:=WilsonSeparatedPrefixMovingPairSector.vacant R F ψ Y t (i+1) N (v/T) o
        (by simpa only [farDate] using visits)
      rw [show collected R canvas (F.h+capP Q) N i older delta=0 from
        WilsonSeparatedPrefixMovingPinController.vacant R canvas older i N F.h (capP Q) (by omega) (by omega) E₀ P₀ (Or.inl vacant)]
      exact (norm_zero (E:=ℝ)).le.trans gross
  have span:((m-b:ℕ):ℝ) ≤ Z:=by
    have duration:=days R.draws.S b m fine
    have lower:=scales R.draws.S (show older ≤ b by omega)
    have upper:=scales R.draws.S fine
    have initial:=R.depth older gate
    dsimp only [Z,WilsonSeparatedPrefixMovingCalendar.epoch];linarith
  calc
    _ ≤ ∑d∈range (m-b),‖mountedRow R canvas Q F φ ψ X Y o y t m older N q ω (b+d)‖:=norm_sum_le ..
    _ ≤ ∑_d∈range (m-b),(T^target)⁻¹*bill*C.buy Z:=sum_le_sum fun d hd=>one d (mem_range.mp hd)
    _=((m-b:ℕ):ℝ)*((T^target)⁻¹*bill*C.buy Z):=by simp
    _ ≤ _:=mul_le_mul_of_nonneg_right span gross

theorem original (H:Hol G)(Q:Fin (n+1)→SealR G)(F:SealR G)(k e u target:ℕ)(E W V S D Wo:Credit):
    let extra:=u+target+2
    let a:=F.h+extra
    ∃C:Credit,∀(R:Realm G (e+1) E)(_P:SpringD R k u a W)(_end:Dormitory R (F.h+capP Q) u Wo)
      (_near:HorizonP H R W V Q)(_far:PassportC H R F W V)
      (_spring:SpringD R (capP Q) (u+a) (capP Q+2) S)(_dorm:Dormitory R (capP Q) (u+a) D)
      (older t b m N:ℕ)(_gate:R.anchor ≤ older)(_start:older ≤ t)(_home:t ≤ b)(_fine:b ≤ m)(_top:m ≤ N)
      (_room:F.h+capP Q ≤ k)(φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)(o:CellR)
      (y g r DF:ℝ)(B:Fin (n+1)→ℝ),
      let T:=paceT R.draws.S b t
      let v:=y / paceT R.draws.S m b
      let Z:=epoch R older m
      let bill:=(16*r)^u*(g⁻¹)^a*coupon F Y e (u+a) r DF*9^(u+a)*(∏s,B s*fee (Q s) e (X s))
      0 < g → Bough Q φ y Z B → Amplitude ψ DF →
      2+2*|v| ≤ r → ψ.radius+|v/T|+1 ≤ r →
      (∀q∈tsupport ψ.ψ.val,T*g+1+|v| ≤ ‖T • q‖) →
      ∀q ≤ e,∀ω:Fin 0→YForest G,‖∑d∈range (m-b),joined R Q F φ ψ X Y o y t m older N q ω (b+d)‖ ≤ 
        Z*((T^target)⁻¹*bill*C.buy Z):=by

  intro extra a
  obtain ⟨C,paid⟩:=mounted H Q F k e u target E W V S D Wo
  refine ⟨C,?_⟩
  intro R
  exact paid R (WilsonSeparatedPrefixMovingPinController.still G e u)

end YM.Integration.WilsonSeparatedPrefixMovingMiddleSector
