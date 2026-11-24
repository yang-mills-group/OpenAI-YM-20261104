import YM.Integration.WilsonSeparatedPrefixMovingBeforeCapture
import YM.Integration.WilsonSeparatedPrefixMovingPinSigned
import YM.Integration.WilsonSeparatedPrefixMovingPinSector

/-! Jointly paid high-to-capture scalar at every actual lattice pin. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPinBefore
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
open WilsonSeparatedPrefixMovingBeforeRead (heard)
open WilsonSeparatedPrefixMovingPinSigned (slice)
open WilsonSeparatedPrefixMovingPinController (appointed)
open Finset
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{H:Hol G}{n height seats:ℕ}

theorem original (M:Master H)(Q:Fin (n+1)→SealR G)(F:SealR G)(e h:ℕ)(positive:0<h)
    (near:∀s,Named M height seats (Q s))(far:Named M height seats F)
    (budget:needed (F.h+capP Q) 0 h ≤ seats):
    let u:=0
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
      ∀site:Cover,∀ω:Fin 0→YForest G,Heard e h T total (fun q=>(WilsonSeparatedPrefixMovingPinSigned.slice R Q F φ ψ X Y o y site t m b older N b N).2 q 0 ω):=by
  intro u k τ a anew amid
  have active:0<τ:=by dsimp only [τ];omega
  obtain ⟨first,plain⟩:=WilsonSeparatedPrefixMovingUnformedSector.mounted H Q F k e u τ C C C C
  obtain ⟨shape,chron,previous⟩:=WilsonSeparatedPrefixMovingPinSector.original H Q F k e u τ active C C C C C C
  obtain ⟨middle,sale⟩:=WilsonSeparatedPrefixMovingMiddleSector.mounted H Q F k e u τ C C C C C C
  refine ⟨first,shape,chron,middle,?_⟩
  intro R sold older t b m N gate start home formed top φ ψ X Y o y r gap farGap DF B T scale Z fresh old stable total
    innerPrice farPrice purchase feeFar shapes fits outerBox nearBox shield separated site ω
  let T_b:=paceT R.draws.S b t
  let pin:=appointed G e R.draws.S b site
  obtain ⟨owners,⟨outside⟩⟩:=WilsonIndependentMovingRosterAllFineSeats.roster sold Q F near far
  obtain ⟨sf,so,sn,dn,term,cross,spring,dorm⟩:=WilsonIndependentMovingRosterAllFineSeats.finance sold Q F u h budget
  obtain ⟨whole,shift,final,remote⟩:=WilsonSeparatedPrefixMovingTwoRulers.original R.draws.S t b m formed ψ y farGap r
    nearBox outerBox separated
  obtain ⟨pairs,sight⟩:=WilsonIndependentMovingRosterAllFine.separated φ ψ T farGap r y fits whole nearBox
  have plainCash:=plain R pin sf term owners outside older t m N gate start (home.trans formed) top le_rfl
    φ ψ X Y o y farGap r DF B farPrice purchase feeFar pairs fits outerBox
  have parcelCash:=previous R pin so sn dn term owners outside older t m N gate start (home.trans formed) top le_rfl
    φ ψ X Y o y r gap farGap r DF B innerPrice farPrice purchase feeFar
    (fun s=>by linarith only [fits s,abs_nonneg y]) shapes sight nearBox outerBox
  let paid₁:=2*fresh*first.buy Z+4*old*chron.buy Z
  have early:Heard e τ T paid₁ (fun q=>(slice R Q F φ ψ X Y o y site t m b older N m N).2 q 0 ω):=by
    apply heard _ _ _ _ _ (pace_pos ..)
    intro q hq
    rw [WilsonSeparatedPrefixMovingPinSigned.fine R Q F owners outside φ ψ X Y o y site t m b older N q ω
      (gate.trans start) (home.trans formed) (start.trans home) formed top]
    refine (norm_add_le ..).trans ((add_le_add (plainCash q hq ω) (parcelCash q hq ω)).trans_eq ?_)
    change 2*((T^τ)⁻¹*fresh)*first.buy Z+4*((T^τ)⁻¹*old)*chron.buy Z=(T^τ)⁻¹*paid₁
    dsimp only [paid₁];ring
  have seen:=WilsonIndependentMovingRosterBirthCalendar.geometry Q φ B r gap y innerPrice purchase
    (fun s=>by linarith only [fits s,abs_nonneg y]) shapes
  have inv:Z⁻¹ ≤ (room r gap y)⁻¹:=inv_anti₀ (zero_lt_one.trans_le seen.pos) shield
  have nearCart:Bough Q φ y Z B:=⟨seen.pos.trans shield,seen.lanes,fun s=>(seen.rents s).trans shield,
    seen.room.trans shield,fun i j neq p hp q hq=>inv.trans (seen.seats i j neq p hp q hq)⟩
  have met:=sale R pin cross term owners outside spring dorm older t b m N gate start home formed top le_rfl
    φ ψ X Y o y farGap r DF B farPrice nearCart feeFar shift final remote
  let paid₂:=Z*(stable*middle.buy Z)
  have during:Heard e τ T_b paid₂ (fun q=>(slice R Q F φ ψ X Y o y site t m b older N b m).2 q 0 ω):=by
    apply heard _ _ _ _ _ (pace_pos ..)
    intro q hq
    rw [WilsonSeparatedPrefixMovingPinSigned.middle R Q F owners outside φ ψ X Y o y site t m b older N q ω
      (gate.trans start) home (start.trans home) formed top]
    exact (met q hq ω).trans_eq (by change Z*((T_b^τ)⁻¹*stable*middle.buy Z)=(T_b^τ)⁻¹*paid₂
                                    dsimp only [paid₂];ring)
  have firstCut:=WilsonIndependentMovingRosterAllFineFunded.cheaper (pace_ge R.draws.S (home.trans formed))
    (Nat.le_add_right h k) early
  have nextCut:=WilsonIndependentMovingRosterAllFineFunded.cheaper (pace_ge R.draws.S home)
    (Nat.le_add_right h k) during
  have div:T/T_b=scale:=by
    dsimp only [T,T_b,scale,paceT];field_simp [(R.draws.S.a_pos b).ne',(R.draws.S.a_pos m).ne',(R.draws.S.a_pos t).ne']
  have rates:(T_b^h)⁻¹=(T^h)⁻¹*scale^h:=by
    have tp:0<T:=pace_pos ..
    have bp:0<T_b:=pace_pos ..
    rw [←div,div_pow];field_simp [tp.ne',bp.ne']
  apply heard _ _ _ _ _ (pace_pos ..)
  intro q hq
  rw [WilsonSeparatedPrefixMovingPinSigned.regroup R Q F φ ψ X Y o y site t m b older N]
  refine (norm_add_le ..).trans ((add_le_add (firstCut.1 q hq) (nextCut.1 q hq)).trans_eq ?_)
  rw [rates];change (T^h)⁻¹*paid₁+((T^h)⁻¹*scale^h)*paid₂=(T^h)⁻¹*(paid₁+scale^h*paid₂)
  ring
end YM.Integration.WilsonSeparatedPrefixMovingPinBefore
