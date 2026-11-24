import YM.Integration.WilsonIndependentConditionedBankWindow
import YM.Integration.WilsonIndependentConditionedShellSum
/-! The genuine funded local product at any nominated exponent below its assembled stable gain. Every fine edge uses the actually purchased chronological price. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedLocalRate
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterChronology (mass born)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonIndependentMatchedRosterPowers (profiles)
variable {G:Gauge}{e n:ℕ}{E:Credit}{dim:Fin (n+1)→ℕ}


open WilsonIndependentMatchedRosterReception (perSite)
open WilsonIndependentConditionedBankWindow (times window)


def fee (k e u b:ℕ)(l:Fin (n+1)→ℕ)(t z:ℝ)(A B:Fin (n+1)→ℝ)(budget height ζ:ℝ):ℝ:=
  let Z:=perSite u b z A B
  (coinMat (∑s,l s) e)^n*Z+budget*profiles n k e u b t z Z*WilsonIndependentConditionedShellSeries.wage b height ζ

theorem original (l d w:Fin (n+1)→ℕ)(out u b:ℕ)(W₀ U₀:Credit):
    ∃ C₀:Credit,∀(ζ:ℝ)(R:Realm G (e+1) E)(m s N:ℕ)(_hm:R.anchor ≤ m)(_top:m+s ≤ N)
      (φ:(a:Fin (n+1))→Rarity (dim a))(P:Fin (n+1)→ℕ→Era G ℝ)
      (y t z:ℝ)(o:CellR)(A B:Fin (n+1)→ℝ),
    let δ:=paceT R.draws.S m (m+s)
    let result:=cruises R.draws R.paid N (∑a,l a) (m+s) m (mass P s)
    (∑s,l s) ≤ out → ζ≤((∑s,w s:ℕ):ℝ)/4 → ((∑s,d s:ℕ):ℝ)+ζ<b →
    SpringD R out u b W₀ → Dormitory R (∑a,l a) u U₀ →
    0<t → (∀a c,a≠c→ClearDay (φ a) (φ c) t) → (∀s,radiusH (φ s) 1 y ≤ z) →
    (∀s,0 ≤ A s) → (∀s,Amplitude (φ s) (B s)) →
    (∀a,Lane R (l a) (d a) m s N u b (φ a) y o δ ((w a:ℝ)/4) (A a) (B a) (P a)) →
    Auth (∑a,l a) result ∧ Flush e u 1 result
      (fee out e u b l t z A B (C₀.buy (WilsonIndependentMatchedCoverDate.age R m (m+s))) ((∑s,d s:ℕ):ℝ) ζ*δ^ζ):=by
  obtain ⟨C,date⟩:=WilsonIndependentMatchedRosterDate.original (D:=dim) G out e u b l E W₀ U₀
  let C₀:=WilsonIndependentMatchedCoverCap.market C (priceWG G e out u b E W₀) E ((∑s,d s)+(∑s,w s))
  refine ⟨C₀,?_⟩
  intro ζ R m s N hm top φ P y t z o A B δ result room release clear spring dorm ht sep profile cash test lane
  have hd:0<δ:=pace_pos ..
  let Z:=perSite u b z A B
  let M:=C₀.buy (WilsonIndependentMatchedCoverDate.age R m (m+s))*profiles n out e u b t z Z
  have endDate:m+s  ≤  N:=top
  have hz:0  ≤  z:=(zero_le_one.trans (fieldCap (φ 0) 1 y)).trans (profile 0)
  have Zpos:0 ≤ Z:=by
    apply Finset.prod_nonneg
    intro i _
    have v₁:=cash i
    have v₂:=(test i).1
    unfold WilsonIndependentMatchedRosterTariff.factor
    positivity
  have cpos:0 ≤ C₀.buy (WilsonIndependentMatchedCoverDate.age R m (m+s)):=zero_le_one.trans (C₀.purchase (times R m s hm s le_rfl).1)
  have posM:0  ≤  M:=by have base:=coinMat_nn out e;unfold M profiles;positivity
  have own (i:ℕ)(hi:i<s):
      let r:=paceT R.draws.S m (m+i)
      Flush e u 1 (cruises R.draws R.paid N (∑s,l s) (m+i) m (born R m N l P i))
        (M*r^((b:ℝ)-((∑s,d s:ℕ):ℝ))*(δ/r)^(((∑s,w s:ℕ):ℝ)/4)):=by
    let j:=m+i
    let L:ℝ:=(ll R.draws j).L.val
    let x:=paceT R.draws.S m (j+1)
    let r:=paceT R.draws.S m j
    have live:R.anchor  ≤  j:=hm.trans (Nat.le_add_right _ _)
    have hl:1  ≤  L:=by dsimp [L];exact_mod_cast (ll R.draws j).L.pos
    have step:x*L=r:=pace_step R.draws.S m j
    have wage:=date R spring dorm m N s endDate hm room d w φ P δ t y z o A B hd ht sep profile cash test lane i hi
    have paid:=window R C (priceWG G e out u b E W₀) ((∑s,d s)+(∑s,w s)) m s N hm top i hi.le
    let J:=WilsonIndependentMatchedCoverDate.age R m j
    let S:=priceWG G e out u b E W₀
    have hC:0  ≤  C.buy J:=zero_le_one.trans (C.purchase (times R m s hm i hi.le).1)
    have hS:0  ≤  R.cash S j:=zero_le_one.trans (S.purchase (R.depth j live))
    have charge:=WilsonIndependentMatchedRosterMoney.original (k:=out) (e:=e) (u:=u) (b:=b)
      (C.buy J) (R.cash S j) (C₀.buy (WilsonIndependentMatchedCoverDate.age R m (m+s))) d w A B δ x L t z hC hS cash (fun s=>(test s).1)
      (pace_pos ..) hl hd ht hz paid
    dsimp only at wage charge ⊢
    rw [step] at charge
    exact ⟨wage.2.1.trans charge,fun j hj r hr=>(wage.2.2 j hj r hr).more charge⟩
  have home:=WilsonIndependentMatchedRosterHome.original R m s N d w l φ P δ y z o A B hd profile cash test lane
  have discount:=Real.rpow_le_rpow_of_exponent_ge hd (pace_le R.draws.S (Nat.le_add_right m s)) release
  let head:ℝ:=(coinMat (∑a,l a) e)^n*Z
  have headPos:0≤head:=mul_nonneg (pow_nonneg (coinMat_nn _ _) _) Zpos
  have cheaper:=mul_le_mul_of_nonneg_left discount headPos
  have originalHome:Flush e u 1 (mass P 0) (head*δ^ζ):=
    ⟨home.2.1.trans cheaper,fun a ha r hr=>(home.2.2 a ha r hr).more cheaper⟩
  have total:=WilsonIndependentConditionedShellSum.original R l m N s u b (∑s,d s) (∑s,w s)
    endDate P (fun s=>(lane s).accounts.head) (fun s=>(lane s).pushed) δ M _ ζ hd
    (WilsonIndependentMatchedCoverSum.spacing R.draws.S m s).ge posM release clear originalHome own
  refine ⟨total.1,?_⟩
  convert total.2 using 1
  unfold fee head M Z perSite
  ring

end YM.Integration.WilsonIndependentConditionedLocalRate
