import YM.Integration.WilsonIndependentMatchedRosterReception
/-! Nonasymptotic cost of every genuine first joint connection on an original physical collar. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedPhysicalComponent
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
variable {G:Gauge}{n e:ℕ}{dim:Fin (n+1)→ℕ}
open WilsonIndependentMatchedRosterReception (perSite)

def volume {modes:ℕ}{E:Credit}(C S:Credit)(R:Realm G (modes+1) E)(m h power:ℕ):ℝ:=
  1+∑i∈Finset.range h,let j:=m+i;|C.buy (WilsonIndependentMatchedCoverDate.age R m j)*R.cash S j*
      (((ll R.draws j).L.val:ℝ)^power)|

def price (n out e u b:ℕ)(l:Fin (n+1)→ℕ)(gross δ t z:ℝ)(A B:Fin (n+1)→ℝ)(slots:ℕ):ℝ:=
  let Z:=perSite u b z A B
  ((coinMat (∑s,l s) e)^n*Z+2*(gross*profiles n out e u b t z Z))*δ^((slots:ℝ)/4)

private theorem age_paid {E:Credit}(R:Realm G (e+1) E){m j:ℕ}(hm:R.anchor ≤ m)(hj:m ≤ j):
    1  ≤  WilsonIndependentMatchedCoverDate.age R m j:=by
  have a:=R.depth m hm
  have b:=scales R.draws.S hj
  unfold WilsonIndependentMatchedCoverDate.age
  linarith only [a,b,Nat.cast_nonneg (α:=ℝ) (j-m)]

theorem original (G:Gauge)(out e u b:ℕ)(l:Fin (n+1)→ℕ)(E W₀ U₀:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E)(m h N:ℕ)(_hm:R.anchor ≤ m)(_endDate:m+h ≤ N)
    (d w:Fin (n+1)→ℕ)(φ:(s:Fin (n+1))→Rarity (dim s))(P:Fin (n+1)→ℕ→Era G ℝ)
    (δ y t z:ℝ)(o:CellR)(A B:Fin (n+1)→ℝ),
    ∑s,l s  ≤  out → 1  ≤  (b:ℝ)-((∑s,d s:ℕ):ℝ)-((∑s,w s:ℕ):ℝ)/4 →
    SpringD R out u b W₀ → Dormitory R (∑s,l s) u U₀ →0<δ→0<t →
    (∀a c,a≠c→ClearDay (φ a) (φ c) t)→(∀s,radiusH (φ s) 1 y  ≤  z)→
    (∀s,0  ≤  A s)→(∀s,Amplitude (φ s) (B s))→
    (∀s,Lane R (l s) (d s) m h N u b (φ s) y o δ ((w s:ℝ)/4) (A s) (B s) (P s))→
    let product:=cruises R.draws R.paid N (∑s,l s) (m+h) m (mass P h)
    let gross:=volume C (priceWG G e out u b E W₀) R m h ((∑s,d s)+(∑s,w s))
    Auth (∑s,l s) product ∧ Flush e u 1 product (price n out e u b l gross δ t z A B (∑s,w s)):=by
  obtain ⟨C,date⟩:=WilsonIndependentMatchedRosterDate.original (D:=dim) G out e u b l E W₀ U₀
  refine ⟨C,?_⟩
  intro R m h N hm endDate d w φ P δ y t z o A B room clear spring dorm hd ht sep profile cash test lane product gross
  let Z:=perSite u b z A B
  let M:=gross*profiles n out e u b t z Z
  have hv:0 ≤ gross:=by dsimp only [gross,volume];positivity
  have hz:0  ≤  z:=(zero_le_one.trans (fieldCap (φ 0) 1 y)).trans (profile 0)
  have Zpos:0 ≤ Z:=by
    apply Finset.prod_nonneg
    intro s _
    have v₁:=cash s
    have v₂:=(test s).1
    unfold WilsonIndependentMatchedRosterTariff.factor
    positivity
  have posM:0  ≤  M:=by have base:=coinMat_nn out e;unfold M profiles;positivity
  have own (i:ℕ)(hi:i<h):
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
    have wage:=date R spring dorm m N h endDate hm room d w φ P δ t y z o A B hd ht sep profile cash test lane i hi
    let J:=WilsonIndependentMatchedCoverDate.age R m j
    let S:=priceWG G e out u b E W₀
    have paid:C.buy J*R.cash S j *L^((∑s,d s)+(∑s,w s))  ≤  gross:=by
      let f:=fun i=>let j:=m+i; |C.buy (WilsonIndependentMatchedCoverDate.age R m j)*R.cash S j*
        (((ll R.draws j).L.val:ℝ)^((∑s,d s)+(∑s,w s)))|
      have one: f i  ≤  ∑i∈Finset.range h,f i:=Finset.single_le_sum (f:=f) (fun i _=>abs_nonneg _) (Finset.mem_range.mpr hi)
      exact (le_abs_self _).trans (one.trans (le_add_of_nonneg_left zero_le_one))
    have hC:0  ≤  C.buy J:=zero_le_one.trans (C.purchase (by dsimp only [J,WilsonIndependentMatchedCoverDate.age]; exact WilsonIndependentMatchedPhysicalComponent.age_paid R hm (Nat.le_add_right m i)))
    have hS:0  ≤  R.cash S j:=zero_le_one.trans (S.purchase (R.depth j live))
    have charge:=WilsonIndependentMatchedRosterMoney.original (k:=out) (e:=e) (u:=u) (b:=b)
      (C.buy J) (R.cash S j) gross d w A B δ x L t z hC hS cash (fun s=>(test s).1)
      (pace_pos ..) hl hd ht hz paid
    dsimp only at wage charge ⊢
    rw [step] at charge
    exact ⟨wage.2.1.trans charge,fun j hj r hr=>(wage.2.2 j hj r hr).more charge⟩
  have home:=WilsonIndependentMatchedRosterHome.original R m h N d w l φ P δ y z o A B hd profile cash test lane
  have summed:=WilsonIndependentMatchedRosterSum.original R l m N h u b (∑s,d s) (∑s,w s)
    endDate P (fun s=>(lane s).accounts.head) (fun s=>(lane s).pushed) δ M _ hd posM clear home.2 own
  convert summed using 3
  unfold price M Z perSite
  ring

end YM.Integration.WilsonIndependentMatchedPhysicalComponent
