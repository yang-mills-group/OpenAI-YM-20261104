import YM.Integration.WilsonIndependentMatchedRosterReception
import YM.Integration.WilsonIndependentMatchedPivotStop

/-! The negative source and every proper ordinary peer share the actual
older Wilson receiver. The entire reported marked unit continues through it. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterStop
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

def Hearing (X:CutsP H T p v E W K U)(out u top stop:ℕ)(prod:Era G ℝ)(fare:ℝ):Prop:=
  let read:=cruises X.ax X.tx X.N out top stop prod
  Flush e u 1 read fare ∧ ∀j  ≤  e,∀z:Fin 0→YForest G,‖read.2 j 0 z‖ ≤ fare

theorem original (run:XSpace.Run)(base:ℕ)(l d w:Fin (n+1)→ℕ)(out u b:ℕ)(W₀ U₀:Credit)(cap η:ℝ)
    (nonneg:0 ≤ cap)(hp:0<η)(room:∑s,l s ≤ out)(clear:1 ≤ (b:ℝ)-((∑s,d s:ℕ):ℝ)-((∑s,w s:ℕ):ℝ)/4):
    ∀ᶠ idx:ℕ in atTop,∀(X:CutsP H T p v E W K U)(f:ℕ)
    (φ:(s:Fin (n+1))→Rarity (dim s))(P:Fin (n+1)→ℕ→Era G ℝ)
    (y t z:ℝ)(o:CellR)(A B:Fin (n+1)→ℝ),
    let δ:=(run.step idx).spacing
    X.vesselsC.anchor=f→X.m=f+old run base idx→X.N=f+count run base idx→
    (∀i ≤ old run base idx,X.vesselsC.y (f+i) ≤ cap)→
    WilsonOriginalPublicPlantedStableCredit.span X X.i= -Real.log δ→
    SpringD X.vesselsC out u b W₀→Dormitory X.vesselsC (∑s,l s) u U₀→
    0<t→(∀a c,a≠c→ClearDay (φ a) (φ c) t)→(∀s,radiusH (φ s) 1 y ≤ z)→
    (∀s,0 ≤ A s)→(∀s,Amplitude (φ s) (B s))→
    (∀s,Lane X.vesselsC (l s) (d s) X.m X.i X.N u b (φ s) y o δ ((w s:ℝ)/4) (A s) (B s) (P s))→
    ∀stop ≤ old run base idx,Hearing X (∑s,l s) u (X.m+X.i) (f+stop) (mass P X.i)
      (δ^(-η)*(bill out e u b l δ η t z A B*δ^(((∑s,w s:ℕ):ℝ)/4))) :=by
  filter_upwards [WilsonIndependentMatchedRosterReception.original (H:=H) (T:=T) (p:=p) (v:=v)
    (K:=K) (E:=E) (W:=W) (U:=U) (dim:=dim) run l d w out u b W₀ U₀ cap η hp room clear,
    WilsonOriginalPublicPlantedOlderJoin.original G (∑s,l s) e u E U₀ run base cap η nonneg hp]
    with idx localRead oldRead X f φ P y t z o A B δ first report top house clock spring dorm ht sep profile cash test lane stop small
  have paid:=localRead X φ P y t z o A B (report ▸ house _ le_rfl) clock spring dorm ht sep profile cash test lane
  have heard:=oldRead X.vesselsC dorm f first house stop (old run base idx) small le_rfl _ paid.1 _ paid.2
  have here:f+stop ≤ X.m:=report ▸ Nat.add_le_add_left small f
  have next:X.m ≤ X.m+X.i:=Nat.le_add_right _ _
  dsimp only at heard
  rw [←report,←top] at heard
  simp only [←cruisesMore X.ax X.tx (mass P X.i) here next] at heard
  exact heard

end YM.Integration.WilsonIndependentMatchedRosterStop
