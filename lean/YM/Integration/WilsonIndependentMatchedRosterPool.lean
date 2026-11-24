import YM.Integration.WilsonIndependentMatchedRosterCuts

/-! All choices of signed residuals and fitted peers for a finite roster
use a single eventual opening of the original torus range. The total
number of positions and the retained output moment are fixed beforehand. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterPool
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
variable {G:Gauge}{h D k e u₀ n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}{dim:Fin (n+1)→ℕ}

open WilsonIndependentEvenPassport (old count)
open WilsonIndependentMatchedRosterReception (bill)

open WilsonIndependentMatchedRosterStop (Hearing)
open WilsonIndependentMatchedRosterSlots (degree entry wallet)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedCutBudget (restored)
open WilsonIndependentEvenPassport (young)

open WilsonIndependentMatchedRosterCuts (counts ranks)

private lemma rooms {τ n k h b:ℕ}(flag:Fin (n+1)→Bool)(small:n+1 ≤ τ)(ang:h ≤ k)(stage:τ*k ≤ b)
    (γ:1 ≤ (b:ℝ)-((τ*h:ℕ):ℝ)-(τ:ℝ)/4):
    ranks flag k h ≤ b ∧ 1 ≤ (b:ℝ)-((∑_s:Fin (n+1),h:ℕ):ℝ)-(counts flag:ℝ)/4:=by
  have get (s:Fin (n+1)):degree (flag s) k h ≤ k:=by cases flag s <;> simp [degree,ang]
  have first:(∑s,degree (flag s) k h)  ≤  (n+1)*k:=by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun s _=>get s)
  have one (s:Fin (n+1)):WilsonIndependentMatchedRosterSlots.count (flag s) ≤ 1:=by cases flag s <;> decide
  have hcnt:counts flag ≤ n+1:=by simpa [counts] using Finset.sum_le_sum (s:=Finset.univ) (fun s _=>one s)
  have hs:((∑_s:Fin (n+1),h:ℕ):ℝ) ≤ ((τ*h:ℕ):ℝ):=by exact_mod_cast (by simpa using Nat.mul_le_mul_right h small : (∑_s:Fin (n+1),h) ≤ τ*h)
  have hc:(counts flag:ℝ) ≤ (τ:ℝ):=by exact_mod_cast hcnt.trans small
  exact ⟨first.trans ((Nat.mul_le_mul_right k small).trans stage),by linarith⟩
def Billed (run:XSpace.Run)(base idx:ℕ)(flag:Fin (n+1)→Bool)(u b:ℕ)(η:ℝ)
    (X:Fin (n+1)→CutsP H T p v E W K U)(f:ℕ)(φ:Fin (n+1)→Rarity D)
    (a amp fee B:Fin (n+1)→ℝ)(c:Fin (n+1)→Verse F)(y t z:ℝ)(o:CellR):Prop:=
    let δ:=(run.step idx).spacing
    let l:=fun s=>degree (flag s) k h
    let A:=fun s=>wallet (flag s) (X s) (c s) (|a s| * (δ^(-η)*fee s)) u b
    let P:=fun s=>entry (flag s) (X s) (a s/amp s) (c s) (φ s) y o
∀stop  ≤  old run base idx,
    Hearing (X 0) (ranks flag k h) u ((X 0).m+(X 0).i) (f+stop) (mass P (X 0).i)
      (δ^(-η)*(bill b e u b l δ η t z A B*δ^((counts flag:ℝ)/4)))

def Offer (run:XSpace.Run)(base idx:ℕ)(flag:Fin (n+1)→Bool)(u b:ℕ)(W₀ U₀:Credit)(cap η:ℝ):Prop:=
  ∀(L:Torch H T p v E W K)(X:Fin (n+1)→CutsP H T p v E W K U)
    (f:ℕ)(φ:Fin (n+1)→Rarity D)(a amp fee B:Fin (n+1)→ℝ)(c:Fin (n+1)→Verse F)
    (stem:Fin (n+1)→TowerS G D)(y t z:ℝ)(o:CellR),
    let δ:=(run.step idx).spacing
    (∀s,Filed (X s) L run base idx f (amp s) δ η (fee s) (stem s))→
    (∀i  ≤  old run base idx,L.L.V.y (f+i)  ≤  cap)→L.L.V.anchor=f→
    SpringD L.L.V b u b W₀→Dormitory L.L.V (ranks flag k h) u U₀→
    0<t→(∀s a,s≠a→ClearDay (φ s) (φ a) t)→(∀s,radiusH (φ s) 1 y  ≤  z)→(∀s,0  ≤  fee s)→
    (∀s,Amplitude (φ s) (B s))→Billed run base idx flag u b η X f φ a amp fee B c y t z o

theorem original (run:XSpace.Run)(base τ u b:ℕ)(W₀ U₀:Credit)(cap η:ℝ)
    (nonneg:0 ≤ cap)(small:0<η)(width:u+b ≤ u₀)(stage:τ*k ≤ b)(ang:h ≤ k)
    (γ:1 ≤ (b:ℝ)-((τ*h:ℕ):ℝ)-(τ:ℝ)/4):
    ∀ᶠidx:ℕ in atTop,∀g:Fin τ,∀flag:Fin (g.val+1)→Bool,
      Offer (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (W:=W) (K:=K) (U:=U) run base idx flag u b W₀ U₀ cap η:=by
  apply Filter.eventually_all.mpr;intro g;apply Filter.eventually_all.mpr;intro flag
  have hs:=rooms flag g.isLt ang stage γ
  exact WilsonIndependentMatchedRosterCuts.original (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (W:=W) (K:=K) (U:=U)
    run base flag b u b W₀ U₀ cap η nonneg small hs.1 width hs.2

end YM.Integration.WilsonIndependentMatchedRosterPool
