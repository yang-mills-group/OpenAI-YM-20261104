import YM.Integration.WilsonIndependentMovingFittedEpoch
import YM.Integration.WilsonIndependentMovingFittedCash
import YM.Integration.WilsonIndependentFittedRosterLedger
import YM.Integration.WilsonIndependentFittedRosterHearing

/-! In one stopped native product each fitted home contributes its
own full finite numerical coefficient. The coefficientwise gross is
spent only on the terms thrown out by the common truncation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedCoffer
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentFittedRosterFilms (Vote factor piece)
open WilsonIndependentMovingFittedRoster (row unitRow)
open WilsonIndependentFittedRosterCash (numerical reserve)
open WilsonIndependentFittedMixedCash (embed)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
open WilsonIndependentMatchedRosterSlots (entry)
open WilsonIndependentMatchedRosterStop (Hearing)
open WilsonIndependentMatchedRosterCuts (ranks)
open WilsonIndependentMatchedPivotSeat (axis)
open WilsonIndependentMatchedRosterChronology (mass)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentEvenPassport (old)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

open WilsonIndependentFittedHomeReserve (receipt)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMovingFittedCash (factors)
open WilsonIndependentMovingFittedEpoch (debit)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonIndependentFittedRelativeClock (reported)

def slot (X:CutsP H T p v E W K U)(s q:ℕ)(a:ℝ)(keep:Bool):ℝ:=
  ∑j:Vote F keep,belt q (embed (clock X.ax X.tx X.N X.m s (factor (dose X a⁻¹) keep j)))

theorem one (X:CutsP H T p v E W K U)(s q:ℕ)(a δ fee A:ℝ)(warm:1 ≤ A)(keep:Bool)(older:s ≤ X.m)
    (paid:receipt X s q (dose X a⁻¹) ≤ debit F q δ fee*A):
    slot X s q a keep ≤ (if keep then 1 else debit F q δ fee)*A:=by
  cases keep with
  | false=>exact paid
  | true=>
    have folded:clock X.ax X.tx X.N X.m s 1=1:=by
      conv_lhs => enter [4];rw [show X.m=s+(X.m-s) by omega]
      rw [WilsonIndependentFittedRelativeClock.reported]
      exact map_one _
    change (∑_:Unit,belt q (embed (clock X.ax X.tx X.N X.m s 1))) ≤ 1*A
    rw [folded,Fintype.sum_unique,(WilsonIndependentFittedRosterLedger.unit q 0).1,one_mul]
    exact warm

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit)(n:ℕ):
    ∃faculty:Credit,∀(X:Fin (n+1) → CutsP H T p v E W K U)(L:Torch H T p v E W K)
      (N s q:ℕ)(flag:Fin (n+1) → Bool)(a fee:Fin (n+1) → ℝ),
      (∀i,(X i).L=L) → (∀i,(X i).N=N) → (∀i,(X i).N=(X i).ceilC) →
      L.L.V.anchor ≤ s → (∀i,s ≤ (X i).m) → q ≤ e → (∀i,0<a i) → (∀i,(X i).fuel=a i*fee i) →
      reserve q (factors X L N s flag (fun i=>dose (X i) (a i)⁻¹)) ≤
        (∏i,if flag i then 1 else debit F q (paceT L.L.V.draws.S (X i).m N) (fee i))*
          faculty.buy (epoch L.L.V s N):=by
  obtain ⟨A,source⟩:=WilsonIndependentMovingFittedEpoch.original H T p v E W K U
  refine ⟨A.powC (n+1),?_⟩
  intro X L N s q flag a fee school ending last live older cap amp salary
  let z:=epoch L.L.V s N
  have top:s ≤ N:=by
    have fine:(X 0).m+(X 0).i=N:=(last 0).symm.trans (ending 0)
    exact (older 0).trans ((Nat.le_add_right ..).trans fine.le)
  have warm:1 ≤ A.buy z:=A.purchase (WilsonSeparatedPrefixMovingCalendar.window L.L.V s s N live le_rfl top).1
  have account (i:Fin (n+1)):
      (∑j:Vote F (flag i),belt q (embed (factors X L N s flag (fun i=>dose (X i) (a i)⁻¹) i j))) ≤
        (if flag i then 1 else debit F q (paceT L.L.V.draws.S (X i).m N) (fee i))*A.buy z:=by
    have cash:=source L.L.V (X i) s N q (a i) (fee i) (congrArg (fun T=>T.L.V) (school i)) live
      (older i) (ending i) (last i) cap (amp i) (salary i)
    have charge:=one (X i) s q (a i) _ (fee i) (A.buy z) warm (flag i) (older i) cash
    have draw:(X i).ax=L.L.V.draws:=congrArg (fun T=>T.L.V.draws) (school i)
    have coin:(X i).tx=L.L.V.paid:=congrArg (fun T=>T.L.V.paid) (school i)
    simpa only [slot,draw,coin,ending,factors] using charge
  unfold reserve
  calc
    _ ≤ ∏i:Fin (n+1),((if flag i then 1 else debit F q (paceT L.L.V.draws.S (X i).m N) (fee i))*A.buy z):=
      prod_le_prod (fun _ _=>sum_nonneg (fun _ _=>sum_nonneg (fun _ _=>norm_nonneg _))) (fun i _=>account i)
    _=_:=by simp only [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,Credit.power,z]

end YM.Integration.WilsonIndependentMovingFittedCoffer
