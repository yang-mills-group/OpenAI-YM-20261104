import YM.Integration.WilsonSeparatedPrefixMovingBeforeRead
import YM.Integration.WilsonSeparatedPrefixMovingTwoRulers
import YM.Integration.WilsonIndependentMovingRosterAllFineFunded

/-! All genuine first contacts with the nominated external field up to
the actual inner capture, at arbitrary finite near arity on a single
paid master. The center and the measured prior remain fixed. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingBeforeCapture
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Elected Named needed)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open WilsonIndependentMovingRosterBirthCalendar (room)
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingWages (coupon)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonSeparatedPrefixMovingBeforeRead (scalar)
open Finset
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{H:Hol G}{n height seats:ℕ}

theorem original (M:Master H)(Q:Fin (n+1)→SealR G)(F:SealR G)(e u h:ℕ)(positive:0<h)
    (near:∀s,Named M height seats (Q s))(far:Named M height seats F)
    (budget:needed (F.h+capP Q) u h ≤ seats):
    let k:=F.h+capP Q
    let τ:=h+k
    let a:=F.h+(u+τ)
    let anew:=capP Q+F.h+(u+τ+2)
    let amid:=F.h+(u+τ+2)
    ∃first shape chron middle:Credit,∀(R:Realm G (e+1) C)(_sold:Elected M R height seats)
      (older t b m N:ℕ)(_gate:R.anchor ≤ older)(_start:older ≤ t)(_home:t ≤ b)(_formed:b ≤ m)(_top:m ≤ N)
      (φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)(o:CellR)(y r gap farGap DF:ℝ)(B:Fin (n+1)→ℝ),
      let T:=paceT R.draws.S m t
      let scale:=paceT R.draws.S m b
      let Z:=epoch R older m
      let fresh:=WilsonSeparatedPrefixMovingUnformedSector.invoice Q F X Y e k u anew r farGap DF B
      let old:=shape.buy (room r gap y)*WilsonIndependentMovingRosterInvoice.charge Q F X Y e u a r farGap DF B
      let stable:=(16*r)^u*(farGap⁻¹)^amid*coupon F Y e (u+amid) r DF*9^(u+amid)*(∏s,B s*fee (Q s) e (X s))
      let total:=2*fresh*first.buy Z+4*old*chron.buy Z+scale^h*(Z*(stable*middle.buy Z))
      0<gap → 0<farGap → (∀s,Amplitude (φ s) (B s)) → Amplitude ψ DF →
      (∀s d,s≠d→ClearDay (φ s) (φ d) gap) →
      (∀s,(φ s).radius+|y|+1 ≤ r) → ψ.radius+|y/T|+1 ≤ r → 2+2*|y| ≤ r →
      room r gap y ≤ Z →
      (∀z∈tsupport ψ.ψ.val,T*farGap+max r (scale+|y|) ≤ ‖T • z‖) →
      ∀ω:Fin 0→YForest G,Heard e h T total (fun q=>scalar R Q F φ ψ X Y o y t b m older N q ω):=by
  intro k τ a anew amid
  obtain ⟨first,shape,chron,upper⟩:=WilsonIndependentMovingRosterAllFineFunded.original M Q F e u h positive near far budget
  obtain ⟨middle,sale⟩:=WilsonSeparatedPrefixMovingMiddleSector.original H Q F k e u τ C C C C C C
  refine ⟨first,shape,chron,middle,?_⟩
  intro R sold older t b m N gate start home formed top φ ψ X Y o y r gap farGap DF B T scale Z fresh old stable total
    innerPrice farPrice purchase feeFar shapes fits outerBox nearBox shield separated ω
  let T_b:=paceT R.draws.S b t
  obtain ⟨owners,⟨outside⟩⟩:=WilsonIndependentMovingRosterAllFineSeats.roster sold Q F near far
  obtain ⟨_,_,_,_,term,cross,spring,dorm⟩:=WilsonIndependentMovingRosterAllFineSeats.finance sold Q F u h budget
  obtain ⟨whole,shift,final,remote⟩:=WilsonSeparatedPrefixMovingTwoRulers.original R.draws.S t b m formed ψ y farGap r
    nearBox outerBox separated
  obtain ⟨pairs,sight⟩:=WilsonIndependentMovingRosterAllFine.separated φ ψ T farGap r y fits whole nearBox
  have fine:=upper R sold older t m N gate start (home.trans formed) top φ ψ X Y o y r gap farGap DF B
    innerPrice farPrice purchase feeFar shapes pairs sight fits outerBox nearBox ω
  have seen:=WilsonIndependentMovingRosterBirthCalendar.geometry Q φ B r gap y innerPrice purchase
    (fun s=>by linarith only [fits s,abs_nonneg y]) shapes
  have inv:Z⁻¹ ≤ (room r gap y)⁻¹:=inv_anti₀ (zero_lt_one.trans_le seen.pos) shield
  have nearCart:Bough Q φ y Z B:=⟨seen.pos.trans shield,seen.lanes,fun s=>(seen.rents s).trans shield,
    seen.room.trans shield,fun i j neq p hp q hq=>inv.trans (seen.seats i j neq p hp q hq)⟩
  have met:=sale R cross term owners outside spring dorm older t b m N gate start home formed top le_rfl
    φ ψ X Y o y farGap r DF B farPrice nearCart feeFar shift final remote
  apply WilsonSeparatedPrefixMovingBeforeRead.original R Q F owners outside φ ψ X Y o y t b m older N h
    (gate.trans start) home (start.trans home) formed top ω _ _ fine
  have bp:0<T_b:=pace_pos ..
  have rebased (q:ℕ)(hq:q ≤ e):‖∑d∈range (m-b),WilsonSeparatedPrefixMovingMiddleSector.joined R Q F φ ψ X Y o y t m older N q ω
      (b+d)‖ ≤ (T_b^τ)⁻¹*(Z*(stable*middle.buy Z)):=by
    exact (met q hq ω).trans_eq (by change Z*((T_b^τ)⁻¹*stable*middle.buy Z)=(T_b^τ)⁻¹*(Z*(stable*middle.buy Z));ring)
  have all:=WilsonSeparatedPrefixMovingBeforeRead.heard e τ T_b (Z*(stable*middle.buy Z)) _ bp rebased
  exact (WilsonIndependentMovingRosterAllFineFunded.cheaper (pace_ge R.draws.S home) (Nat.le_add_right h k) all).1

end YM.Integration.WilsonSeparatedPrefixMovingBeforeCapture
