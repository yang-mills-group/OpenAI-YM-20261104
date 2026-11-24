import YM.Integration.WilsonIndependentMatchedInheritedStop
import YM.Integration.WilsonIndependentMatchedRosterCuts
import YM.Integration.WilsonIndependentMatchedRosterSlots
import YM.Integration.WilsonIndependentMatchedCensusReceipt

/-! An appointed list of released cuts on one true notebook supplies both
the actual compensated upper and the positive coarse peers at all its stops. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedInheritedCuts
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
open WilsonIndependentMatchedCutBudget (restored)
open WilsonIndependentMatchedRosterReception (bill)

open WilsonIndependentMatchedRosterStop (Hearing)
open WilsonIndependentMatchedRosterSlots (degree entry wallet)
open WilsonIndependentMatchedRosterCuts (counts ranks)
open WilsonIndependentMatchedCutBudget (restored)
open WilsonIndependentEvenPassport (young)

structure Recorded (X:CutsP H T p v E W K U)(L:Torch H T p v E W K)(run:XSpace.Run)
    (base idx f N:ℕ)(amp δ η fee:ℝ)(stem:TowerS G D):Prop where
  school : X.L=L
  report : X.m=f+old run base idx
  top : X.N=N
  gap : X.i=young base idx
  scale : WilsonOriginalPublicPlantedStableCredit.span X X.i= -Real.log δ
  residual : X.springP X.i=amp • stem-Shrine X.Ntop X.tileP
  actual (a:ℝ) : (a/amp) • X.pt=a • stem
  charge (a:ℝ) : restored X (a/amp) δ η=|a| * (δ^(-η)*fee)

theorem placed (X:CutsP H T p v E W K U)(L:Torch H T p v E W K)(run:XSpace.Run)
    (base idx f N:ℕ)(amp δ η fee:ℝ)(stem:TowerS G D)(pos:0<amp)
    (school:X.L=L)(report:X.m=f+old run base idx)(top:X.N=N)(gap:X.i=young base idx)
    (actual:X.pt=amp • stem)(price:X.fuel=amp*fee)(residual:X.springP X.i=amp • stem-Shrine X.Ntop X.tileP)
    (scale:WilsonOriginalPublicPlantedStableCredit.span X X.i= -Real.log δ):
    Recorded X L run base idx f N amp δ η fee stem:=by
  refine ⟨school,report,top,gap,scale,residual,?_,?_⟩
  · intro a;rw [actual,smul_smul,div_mul_cancel₀ a pos.ne']
  · intro a
    rw [restored,price,abs_div,abs_of_pos pos]
    field_simp [pos.ne']

theorem original (run:XSpace.Run)(base:ℕ)(flag:Fin (n+1)→Bool)(out u b:ℕ)(W₀ U₀:Credit)(cap η:ℝ)
    (nonneg:0 ≤ cap)(small:0<η)(room:ranks flag k h ≤ out)(width:u+b ≤ u₀)
    (clear:1 ≤ (b:ℝ)-((∑_s:Fin (n+1),h:ℕ):ℝ)-(counts flag:ℝ)/4):
    ∀ᶠ idx:ℕ in atTop,∀(L:Torch H T p v E W K)(X:Fin (n+1)→CutsP H T p v E W K U)
    (f N:ℕ)(φ:Fin (n+1)→Rarity D)(a amp fee B:Fin (n+1)→ℝ)(c:Fin (n+1)→Verse F)
    (stem:Fin (n+1)→TowerS G D)(y t z:ℝ)(o:CellR),
    let δ:=(run.step idx).spacing
    let l:=fun s=>degree (flag s) k h
    let A:=fun s=>wallet (flag s) (X s) (c s) (|a s| * (δ^(-η)*fee s)) u b
    let P:=fun s=>entry (flag s) (X s) (a s/amp s) (c s) (φ s) y o
    (∀s,Recorded (X s) L run base idx f N (amp s) δ η (fee s) (stem s))→
    (∀i ≤ old run base idx,L.L.V.y (f+i) ≤ cap)→L.L.V.anchor=f→
    SpringD L.L.V out u b W₀→Dormitory L.L.V (ranks flag k h) u U₀→
    0<t→(∀s a,s≠a→ClearDay (φ s) (φ a) t)→(∀s,radiusH (φ s) 1 y ≤ z)→(∀s,0 ≤ fee s)→
    (∀s,Amplitude (φ s) (B s))→∀stop ≤ old run base idx,
    Hearing (X 0) (ranks flag k h) u ((X 0).m+(X 0).i) (f+stop) (mass P (X 0).i)
      (δ^(-η)*(bill out e u b l δ η t z A B*δ^((counts flag:ℝ)/4))) :=by
  let l:=fun s=>degree (flag s) k h
  let w:=fun s=>WilsonIndependentMatchedRosterSlots.count (flag s)
  let h₀:=fun _:Fin (n+1)=>h
  filter_upwards [WilsonIndependentMatchedInheritedStop.original (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (W:=W) (K:=K) (U:=U)
      (dim:=fun _:Fin (n+1)=>D) run base l h₀ w out u b W₀ U₀ cap η nonneg small room clear,
    WilsonIndependentMatchedCutBudget.original (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (W:=W) (K:=K) (U:=U) run cap η small]
    with idx read earn L X f N φ a amp fee B c stem y t z o δ ranks A P filed ages anchor spring dorm ht sep profile price test stop hstop
  have equal (s):(X s).vesselsC=L.L.V:=congrArg (fun l=>l.L.V) (filed s).school
  have course (s):(X s).vesselsC=(X 0).vesselsC:=(equal s).trans (equal 0).symm
  have landing (s):(X s).m=(X 0).m:=(filed s).report.trans (filed 0).report.symm
  have endDate (s):(X s).N=(X 0).N:=(filed s).top.trans (filed 0).top.symm
  have gap (s):(X s).i=(X 0).i:=(filed s).gap.trans (filed 0).gap.symm
  have lane (s):Lane (X 0).vesselsC (l s) h (X 0).m (X 0).i (X 0).N u b (φ s) y o δ ((w s:ℝ)/4)
      (A s) (B s) (P s):=by
    have capX:(X s).vesselsC.y (X s).m ≤ cap:=by rw [equal,(filed s).report];exact ages _ le_rfl
    have stable:=earn (X s) (a s/amp s) capX (filed s).scale
    rw [(filed s).charge] at stable
    have sold:=WilsonIndependentMatchedRosterSlots.source (flag s) (X s) (a s/amp s) (c s) (φ s) y o δ _ (B s) stable (test s) u b width
    simpa only [course s,landing s,gap s,endDate s] using sold
  have positive:0<δ:=(run.step idx).positive
  have here:(X 0).vesselsC.anchor=f:=(equal 0) ▸ anchor
  exact read (X 0) f φ P y t z o A B here (filed 0).report ((equal 0) ▸ ages)
    (filed 0).scale ((equal 0) ▸ spring) ((equal 0) ▸ dorm) ht sep profile
    (fun s=>WilsonIndependentMatchedRosterSlots.money (flag s) (X s) (c s) (by have p:=price s;positivity) u b)
    test lane stop hstop

end YM.Integration.WilsonIndependentMatchedInheritedCuts
