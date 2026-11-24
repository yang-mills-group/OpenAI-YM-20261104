import YM.Integration.WilsonIndependentMatchedPhysicalSector
import YM.Integration.WilsonIndependentFittedRosterFilms
/-! Fixed released fit axes on every live peer of a true stable subset, independent of its reported coefficient. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedPhysicalAxes
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedRosterLane WilsonIndependentMatchedCoverPairBudget
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedRosterSlots (entry wallet degree count)
open WilsonIndependentMatchedPhysicalComponent (volume price)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedPhysicalMasks (ranksV)
variable {G:Gauge}{h D n k e u₀:ℕ}{H:Hol G}{Q:Fin (n+1)→SealR G}{v:∀i,Rails (Q i).h k u₀ e}
local notation "C" => Credit.leanC
abbrev Courts:=(i:Fin (n+1))→CutsP H (Q i).ans (Q i).path (v i) C C C C

open WilsonIndependentMatchedPhysicalSector (stamp)
open WilsonIndependentFittedRosterFilms (Vote piece)
open WilsonIndependentMatchedPivotSeat (axis ticket)
open WilsonIndependentMatchedReportedProxy (reported)

def pin {F:Labels.Frame G h}:(flag:Bool)→Vote F flag→Verse F
  | true,_=>0
  | false,b=>axis b 0

def field (flag:Fin (n+1)→Bool)(X:Courts (H:=H) (v:=v))(F:Wilt Q)(y:ℝ)(o:CellR)
    (sel:∀s,Vote (Q s).F (flag s)):Era G ℝ:=
  MassP G ℝ n fun s=>piece false (X s) 1 0 (F s) y o (flag s) (sel s)

def rent {F:Labels.Frame G h}{T:SectionData F}{p:h<D}{w:Rails h k u₀ e}
    (flag:Bool)(X:CutsP H T p w C C C C)(A:ℝ)(u b:ℕ):ℝ:=
  if flag then A else (WilsonIndependentMatchedProxyIncome.tariff H T p e u b C C C).buy X.Age

private lemma unwind {F:Labels.Frame G h}{T:SectionData F}{p:h<D}{w:Rails h k u₀ e}
    (X:CutsP H T p w C C C C)(φ:Rarity D)(y:ℝ)(o:CellR)(flag:Bool)(s:Vote F flag):
    piece false X 1 0 φ y o flag s=entry flag X 1 (pin flag s) φ y o X.i:=by
  cases flag <;> rfl

private lemma axisWallet {F:Labels.Frame G h}{T:SectionData F}{p:h<D}{w:Rails h k u₀ e}
    (flag:Bool)(s:Vote F flag)(X:CutsP H T p w C C C C)(A:ℝ)(u b:ℕ):
    wallet flag X (pin flag s) A u b=rent flag X A u b:=by
  cases flag
  · simp [wallet,rent,pin,WilsonIndependentMatchedPivotSeat.ticket]
  · rfl

def charge (V:Realm G (e+1) C)(X:Courts (H:=H) (v:=v))(flag:Fin (n+1)→Bool)
    (u b out host m K:ℕ)(primary:Fin (n+1)→Credit)(middle last:Credit)(t z:ℝ)(B:Fin (n+1)→ℝ):ℝ:=
  let δ:=paceT V.draws.S m K
  let h:=fun s=>(Q s).h
  let l:=fun s=>degree (flag s) k (h s)
  let w:=fun s=>count (flag s)
  let A:=fun s=>rent (flag s) (X s) ((primary s).buy (X s).Age*(X s).fuel) u b
  let gross:=volume middle (priceWG G e out u b C C) V m (K-m) ((∑s,h s)+(∑s,w s))
  last.buy (Compar V.draws.S V.y host m)*price n out e u b l gross δ t z A B (∑s,w s)

theorem original (H:Hol G)(Q:Fin (n+1)→SealR G)(v:∀i,Rails (Q i).h k u₀ e)(u b out:ℕ)
    (width:u+b ≤ u₀)(stage:(n+1)*k ≤ out)(spread:1 ≤ (b:ℝ)-((∑s,(Q s).h:ℕ):ℝ)-((n+1:ℕ):ℝ)/4):
    ∃(primary:Fin (n+1)→Credit)(middle last:(Fin (n+1)→Bool)→Credit),
    ∀(V:Realm G (e+1) C)(X:Courts (H:=H) (v:=v))(host m K N:ℕ)(F:Wilt Q)(B:Fin (n+1)→ℝ)
    (t z y:ℝ)(o:CellR),stamp V X m K N → V.anchor ≤ host → host ≤ m → m ≤ K → K ≤ N →
    SpringD V out u b C → (∀l ≤ out,Dormitory V l u C) → 0<t →
    (∀s q,s≠q →ClearDay (F s) (F q) t) → (∀s,radiusH (F s) 1 y ≤ z) →
    (∀s,Amplitude (F s) (B s)) → ∀(flag:Fin (n+1)→Bool)(sel:∀s,Vote (Q s).F (flag s)),
    response e u (cruises V.draws V.paid N (ranksV flag k (fun s=>(Q s).h)) K host (field flag X F y o sel))
      (charge V X flag u b out host m K primary (middle flag) (last flag) t z B):=by
  let h:=fun i=>(Q i).h
  let ranks:=fun (flag:Fin (n+1)→Bool) i=>degree (flag i) k (h i)
  choose primary issued using (fun i=>WilsonIndependentMatchedPhysicalArm.original H (Q i).ans (Q i).path (v i) C C C C)
  choose middle joined using (fun flag=>WilsonIndependentMatchedPhysicalComponent.original (dim:=fun s=>(Q s).D)
    G out e u b (ranks flag) C C C)
  choose last heard using (fun (flag:Fin (n+1)→Bool)=>WilsonIndependentMatchedPhysicalCourt.older G (∑s,ranks flag s) e u C C)
  refine ⟨primary,middle,last,?_⟩
  intro V X host m K N F B t z y o filed awake older start live spring dorm ht sep span test flag sel
  let δ:=paceT V.draws.S m K
  let w:=fun s=>count (flag s)
  let A:=fun s=>rent (flag s) (X s) ((primary s).buy (X s).Age*(X s).fuel) u b
  let d:=fun s=>pin (flag s) (sel s)
  let f:=fun s=>entry (flag s) (X s) 1 (d s) (F s) y o
  have lev s: (X s).ax=V.draws:=(filed s).1
  have clock s: (X s).tx=V.paid:=(filed s).2.1
  have home s: (X s).m=m:=(filed s).2.2.1
  have top s: (X s).ceilC=K:=(filed s).2.2.2.1
  have prior s: (X s).N=N:=(filed s).2.2.2.2
  have gap s: (X s).i=K-m:=by
    have eq: (X s).m+(X s).i=K:=top s
    rw [home s] at eq
    omega
  have turf s:paceT (X s).ax.S (X s).m (X s).ceilC=δ:=by rw [lev s,home s,top s]
  have eq s:wallet (flag s) (X s) (d s) ((primary s).buy (X s).Age*(X s).fuel) u b=A s:=axisWallet ..
  have cash s:0 ≤ A s:=by
    rw [←eq s]
    exact WilsonIndependentMatchedRosterSlots.money _ _ _
      (mul_nonneg (zero_le_one.trans ((primary s).purchase (X s).windowC.warm)) (X s).hf) _ _
  have admitted s:Lane V (ranks flag s) (h s) m (K-m) N u b (F s) y o δ ((w s:ℝ)/4) (A s) (B s) (f s):=by
    have ear:=issued s (X s) 1
    rw [abs_one,one_mul,turf s] at ear
    have row:=WilsonIndependentMatchedRosterSlots.source (flag s) (X s) 1 (d s) (F s) y o
      δ _ (B s) ear (test s) u b width
    have posted:=WilsonIndependentMatchedPhysicalArm.lane (R':=V) (lev s) (clock s) row
    rw [home s,gap s,prior s,eq s] at posted
    exact posted
  have rle s:ranks flag s ≤ k:=by cases ok:flag s <;> simp [ranks,degree,ok,h,(v s).hk]
  have fit:∑s,ranks flag s ≤ out:=by
    apply le_trans _ stage
    simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>rle i)
  have count₁ s:w s ≤ 1:=by cases ok:flag s <;> simp [w,WilsonIndependentMatchedRosterSlots.count,ok]
  have countAll:(∑s,w s:ℕ) ≤ n+1:=by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _=>count₁ i)
  have cnt:((∑s,w s:ℕ):ℝ) ≤ ((n+1:ℕ):ℝ):=by exact_mod_cast countAll
  have clear:1 ≤ (b:ℝ)-((∑s,h s:ℕ):ℝ)-((∑s,w s:ℕ):ℝ)/4:=by dsimp only [h];linarith only [spread,cnt]
  have mk:m+(K-m)=K:=Nat.add_sub_of_le start
  have one:=joined flag V m (K-m) N (awake.trans older) (by rwa [mk]) h w F f δ y t z o A B fit clear spring
    (dorm _ fit) (pace_pos ..) ht sep span cash test admitted
  dsimp only at one
  have covered:WilsonIndependentMatchedRosterChronology.mass f (K-m)=field flag X F y o sel:=by
    apply congrArg (MassP G ℝ n)
    funext i
    rw [unwind,←gap i]
  rw [mk,covered] at one
  have whole:=heard flag V (dorm _ fit) host m N awake older (start.trans live) _ _ one.1 one.2
  rw [←cruisesMore _ _ _ older start] at whole
  exact whole
end YM.Integration.WilsonIndependentMatchedPhysicalAxes
