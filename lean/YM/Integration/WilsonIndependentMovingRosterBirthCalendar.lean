import YM.Integration.WilsonIndependentMovingRosterBirthReceipt
import YM.Integration.WilsonSeparatedPrefixMovingCalendar

/-! The fixed near geometry pays only once throughout the fine-date sum.
The separate chronological credit is on the original two-contact calendar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterBirthCalendar
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open WilsonIndependentMovingRosterBirth (charge)
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n:ℕ}

def room (rad gap y:ℝ):ℝ:=max 1 (max rad (max |y| gap⁻¹))

theorem geometry (Q:Fin (n+1)→SealR G)(φ:Wilt Q)(B:Fin (n+1)→ℝ)(rad gap y:ℝ)
    (clear:0<gap)(billed:∀s,Amplitude (φ s) (B s))(fits:∀s,(φ s).radius ≤ rad)
    (apart:∀s t,s≠t→ClearDay (φ s) (φ t) gap):
    Bough Q φ y (room rad gap y) B:=by
  have low:1 ≤ room rad gap y:=le_max_left ..
  have ceiling:max rad (max |y| gap⁻¹) ≤ room rad gap y:=le_max_right ..
  have half:max |y| gap⁻¹ ≤ room rad gap y:=(le_max_right ..).trans ceiling
  have separated:gap⁻¹ ≤ room rad gap y:=(le_max_right ..).trans half
  have fraction:(room rad gap y)⁻¹ ≤ gap:=by
    have ordered:=inv_anti₀ (inv_pos.mpr clear) separated
    simpa only [inv_inv] using ordered
  exact ⟨low,billed,fun s=>(fits s).trans ((le_max_left ..).trans ceiling),(le_max_left ..).trans half,
    fun s t h p hp q hq=>fraction.trans (apart s t h p hp q hq)⟩

theorem original (H:Hol G)(Q:Fin (n+1)→SealR G)(E W V S U:Credit)(e u extra:ℕ):
    ∃C:Credit,∀(R:Realm G (e+1) E),HorizonP H R W V Q →
    SpringD R (capP Q) u (capP Q+(u+extra)) S → Dormitory R (capP Q) u U →
    ∀(older m i j N:ℕ)(φ:Wilt Q)(X:Herit Q)(B:Fin (n+1)→ℝ)(rad gap y:ℝ)(o:CellR),
    R.anchor ≤ older → older ≤ m → m ≤ i → i < j → j < N →
    0 < gap → (∀s,Amplitude (φ s) (B s)) → (∀s,(φ s).radius ≤ rad) →
    (∀s t,s≠t→ClearDay (φ s) (φ t) gap) →
    let w:=paceT R.draws.S m (j+1)
    let x:=paceT R.draws.S m (i+1)
    let D:=Ash R.draws R.paid φ X m j N y o
    let Y:=cruises R.draws R.paid N (capP Q) j (i+1) D
    let money:=C.buy (epoch R older (j+1))*w^extra*(C.buy (room rad gap y)*charge Q X e B)
    Auth (capP Q) Y ∧ Flush e u 1 Y money ∧
      Income Y (capP Q) e u (OrbP (ll R.draws i) (WilsonSeparatedPrefixMovingLocator.booked y o) x y o)
        ((9:ℝ)^u*money):=by
  obtain ⟨C,carry⟩:=WilsonIndependentMovingRosterBirthReceipt.carried H Q E W V S U e u extra
  refine ⟨C,?_⟩
  intro R home spring dorm older m i j N φ X B rad gap y o start floor near joined top
    positive bids fixed separate w x D Y money
  let s:=room rad gap y
  let age:=epoch R older (j+1)
  have geo:=geometry Q φ B rad gap y positive bids fixed separate
  have mx:R.anchor ≤ m:=start.trans floor
  have late:i+1 ≤ j:=joined
  have floor':older ≤ i+1:=floor.trans (near.trans (Nat.le_succ _))
  have after:m ≤ j+1:=near.trans (joined.le.trans (Nat.le_succ _))
  have clock:=window R older m (j+1) start floor after
  have stop:=window R older (i+1) (j+1) start floor' (late.trans (Nat.le_succ _))
  have medium:PadRank R (i+1) j age:=stop.2.2.2.zone le_rfl (Nat.le_succ _)
  have lower:age ≤ max s age:=le_max_right ..
  have dated:PadRank R (i+1) j (max s age):=
    ⟨fun ℓ a b=>(medium.year ℓ a b).trans lower,medium.lengthS.trans lower⟩
  have given:=carry R home spring dorm m i j N φ X B (max s age) y o mx near joined top
    (clock.2.2.1.trans lower) dated (boughRise geo (le_max_left s age))
  have hw:0 ≤ w^extra:=pow_nonneg (pace_pos ..).le _
  have cash:0 ≤ charge Q X e B:=by
    apply Finset.prod_nonneg
    intro t _
    apply mul_nonneg (bids t).1
    unfold WilsonSeparatedPrefixMovingOwnDate.fee
    positivity
  have separateCost:C.buy (max s age) ≤ C.buy age*C.buy s:=by
    rcases le_total s age with a|a
    · rw [max_eq_right a];exact le_mul_of_one_le_right (zero_le_one.trans (C.purchase clock.1)) (C.purchase geo.pos)
    · rw [max_eq_left a];exact le_mul_of_one_le_left (zero_le_one.trans (C.purchase geo.pos)) (C.purchase clock.1)
  have fee:C.buy (max s age)*w^extra*charge Q X e B ≤ money:=by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right separateCost hw) cash).trans_eq
    dsimp only [money,s,age];ring
  have priced:Flush e u 1 Y money:=⟨given.2.1.1.trans fee,fun a ha r hr=>(given.2.1.2 a ha r hr).more fee⟩
  exact ⟨given.1,priced,WilsonIndependentMovingRosterBirthReceipt.center given.1 priced (ll R.draws i) x y o (pace_pos ..)⟩

end YM.Integration.WilsonIndependentMovingRosterBirthCalendar
