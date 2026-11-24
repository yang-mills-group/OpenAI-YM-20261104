import YM.Integration.WilsonIndependentMovingRosterStableLanding
import YM.Integration.WilsonIndependentMovingRosterStableRetention
import YM.Integration.WilsonIndependentMatchedRosterSum

/-! A complete signed stable/fitted product on two actual reporting
dates. Every prior first connection is kept on its genuine successor. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterStableCensus

open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterTariff (factor)
open WilsonIndependentMovingRosterStableSale (homes centers)
open WilsonIndependentMatchedRosterChronology (mass born)
open WilsonIndependentMatchedRosterPowers (profiles)
open scoped BigOperators Topology Classical

variable {n:ℕ}{D:Fin ((n+1)+1)→ℕ}

theorem original (G:Gauge)(k e u b:ℕ)(l:Fin ((n+1)+1)→ℕ)(E W V:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E)(_spring:SpringD R k u b W)(_later:Dormitory R (∑s,l s) u V)
      (t m N:ℕ)(_away:t ≤ m)(_upper:m ≤ N)(_live:R.anchor ≤ m)
      (d w:Fin ((n+1)+1)→ℕ)(φ:(s:Fin ((n+1)+1))→Rarity (D s))
      (P:Fin ((n+1)+1)→ℕ→Era G ℝ)(A B:Fin ((n+1)+1)→ℝ)(y z gap budget:ℝ)(o:CellR),
      let T:=paceT R.draws.S m t
      let δ:=paceT R.draws.S m N
      let Y:=fun s=>P s (N-homes t m s)
      let Z:=∏s,factor u b z*(B s*A s)
      let amount:=T^(d 0+u)*((coinMat (∑s,l s) e)^(n+1)*Z)+
        2*(T^(d 0+u+u)*(budget*profiles (n+1) k e u b gap z Z))
      1≤T → 0<gap → 0≤budget → (∑s,l s)≤k → 1≤(b:ℝ)-((∑s,d s:ℕ):ℝ)-((∑s,w s:ℕ):ℝ)/4 →
      (∀s,0≤A s) → (∀s,Amplitude (φ s) (B s)) →
      (∀s,radiusH (φ s) 1 (centers y T s)≤z) →
      (∀a c:Fin (n+1),a≠c→ClearDay (φ a.succ) (φ c.succ) gap) →
      (∀a:Fin (n+1),∀p∈tsupport (φ a.succ).ψ.val,∀q∈tsupport (φ 0).ψ.val,gap≤dist p (T • q)) →
      (∀j,m≤j→j<N→C.buy (WilsonIndependentMatchedCoverDate.age R m j)*
        R.cash (priceWG G e k u b E W) j*((ll R.draws j).L.val:ℝ)^((∑s,d s)+(∑s,w s))≤budget) →
      (∀s,Lane R (l s) (d s) (homes t m s) (N-homes t m s) N u b (φ s) (centers y T s) o
        (paceT R.draws.S (homes t m s) N) ((w s:ℝ)/4) (A s) (B s) (P s)) →
      let out:=cruises R.draws R.paid N (∑s,l s) N m (MassP G ℝ (n+1) Y)
      Auth (∑s,l s) out ∧ Flush e u 1 out (amount*δ^(((∑s,w s:ℕ):ℝ)/4)):=by
  obtain ⟨C,retain⟩:=WilsonIndependentMovingRosterStableRetention.original (n:=n) G (∑s,l s) k e u b E W V
  refine ⟨C,?_⟩
  intro R spring later t m N away upper live d w φ P A B y z gap budget o T δ Y Z amount
    zoom apt money room clear positive tests caps near far bank lanes out
  let calendar:=fun s i=>P s (m+i-homes t m s)
  have admissible (s:Fin ((n+1)+1)):homes t m s ≤ m:=by
    induction s using Fin.cases with
    | zero=>exact away
    | succ _=>exact le_rfl
  have auth (s) (i:ℕ) (hi:i≤N-m):Auth (l s) (calendar s i):=by
    apply (lanes s).accounts.head
    exact Nat.sub_le_sub_right (by omega) _
  have legal (s) (i:ℕ) (hi:i<N-m):
      verseI R.draws R.paid (m+i) N (l s) (calendar s (i+1))=calendar s i:=by
    have hm:=admissible s
    have h₁:homes t m s+(m+i-homes t m s)=m+i:=by omega
    have h₂:m+(i+1)-homes t m s=(m+i-homes t m s)+1:=by omega
    change verseI R.draws R.paid (m+i) N (l s) (P s (m+(i+1)-homes t m s))=_
    rw [h₂]
    have passed:=(lanes s).pushed (m+i-homes t m s) (by omega)
    simpa only [h₁] using passed
  let M:=T^(d 0+u+u)*(budget*profiles (n+1) k e u b gap z Z)
  have zp:0≤z:=(zero_le_one.trans (fieldCap ..)).trans (caps 0)
  have Zpos:0≤Z:=Finset.prod_nonneg fun s _=>by
    have h₁:=positive s
    have h₂:=(tests s).1
    unfold WilsonIndependentMatchedRosterTariff.factor
    positivity
  have Mpos:0≤M:=by
    have h₁:=coinMat_nn k e
    have h₂:=zero_le_one.trans zoom
    unfold M profiles
    positivity
  have earn (i:ℕ)(hi:i<N-m):
      let r:=paceT R.draws.S m (m+i)
      Flush e u 1 (cruises R.draws R.paid N (∑s,l s) (m+i) m (born R m N l calendar i))
        (M*r^((b:ℝ)-((∑s,d s:ℕ):ℝ))*(δ/r)^(((∑s,w s:ℕ):ℝ)/4)):=by
    let j:=m+i
    have cur:m≤j:=Nat.le_add_right m i
    have fine:j<N:=by dsimp [j];omega
    have post:=WilsonIndependentMovingRosterStableSale.original R spring t m away cur fine (live.trans cur)
      l d w room φ A B y z gap o P zoom apt positive tests caps near far lanes
    have ours:=retain R later m j N live cur fine.le d w A B (born R m N l calendar i) T gap z budget
      zoom apt zp positive (fun s=>(tests s).1) (bank j cur fine)
    dsimp only [WilsonIndependentMatchedRosterChronology.born] at ours ⊢
    have same:(fun s=>P s (j+1-homes t m s))=fun s=>calendar s (i+1):=by
      dsimp only [j,calendar]
      simp only [Nat.add_assoc]
    dsimp only at post
    rw [same] at post
    exact (ours post.1 post.2).2
  have landing:=WilsonIndependentMovingRosterStableLanding.original R t m N away upper l d w φ P A B y z o
    zoom positive tests caps lanes
  have finish:m+(N-m)=N:=Nat.add_sub_of_le upper
  have full:=WilsonIndependentMatchedRosterSum.original R l m N (N-m) u b (∑s,d s) (∑s,w s)
    finish.le calendar auth legal δ M _ (pace_pos ..) Mpos clear landing.2 earn
  dsimp only [WilsonIndependentMatchedRosterChronology.mass,calendar] at full
  rw [finish] at full
  refine ⟨full.1,?_⟩
  convert full.2 using 1
  unfold amount M
  ring

end YM.Integration.WilsonIndependentMovingRosterStableCensus
