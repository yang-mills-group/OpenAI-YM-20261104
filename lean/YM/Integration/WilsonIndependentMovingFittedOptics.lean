import YM.Integration.WilsonIndependentMovingFittedCoffer
import YM.Integration.WilsonIndependentMovingRosterAllFineAge
import YM.Integration.WilsonIndependentFittedRosterHearing

/-! In one stopped native product each fitted home contributes its
own full finite numerical coefficient. The coefficientwise gross is
spent only on the terms thrown out by the common truncation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingFittedOptics
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

open RegulatorIR RegulatorIR.Ledger Filter
open WilsonIndependentEvenPassport (count)
open WilsonIndependentExactPlate (Requests)
open scoped Topology

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit)(n:ℕ)
    (V:XSpace.Run)(base phase:ℕ)(ha:0<base)(good:4 ≤ phase)(cash η:ℝ)(positive:0<η):
    ∀ᶠ idx:ℕ in atTop,∀i:Requests base,i.val=idx → ∀(board:Levels G)(anchor:ℕ),
      (∀f:Flap (WilsonIndependentExactPlate.M V base),f.volW=i →
        (board.clock.op (anchor+(WilsonIndependentExactPlate.M V base i-(f.offset+1))) 0).patch=
          (WilsonIndependentExactPlate.S V base ha phase good).pactP f) →
      ∀(L:Torch H T p v E W K)(X:Fin (n+1) → CutsP H T p v E W K U)(N s q:ℕ)(flag:Fin (n+1) → Bool)
        (a fee:Fin (n+1) → ℝ),L.L.V.draws=board → L.L.V.anchor=anchor → anchor ≤ s → L.L.V.y s ≤ cash →
        N ≤ anchor+count V base i.val → (∀j,(X j).L=L) → (∀j,(X j).N=N) → (∀j,(X j).N=(X j).ceilC) →
        (∀j,s ≤ (X j).m) → q ≤ e → (∀j,0<a j) → (∀j,(X j).fuel=a j*fee j) →
        reserve q (factors X L N s flag (fun j=>dose (X j) (a j)⁻¹)) ≤
          (∏j,if flag j then 1 else debit F q (paceT L.L.V.draws.S (X j).m N) (fee j))*
            (V.step idx).spacing^(-η):=by
  obtain ⟨C,portfolio⟩:=WilsonIndependentMovingFittedCoffer.original H T p v E W K U n
  filter_upwards [WilsonIndependentMovingRosterAllFineAge.original (G:=G) (e:=e+1) (E:=E)
    V base phase ha good C cash η positive] with idx paid
  intro i ix board anchor levels L X N s q flag a fee draw start land atS upper school ending ceil older cap amp salary
  have active:L.L.V.anchor ≤ s:=start ▸ land
  have live:s ≤ N:=by
    have hi:(X 0).m+(X 0).i=N:=(ceil 0).symm.trans (ending 0)
    exact (older 0).trans ((Nat.le_add_right ..).trans hi.le)
  apply (portfolio X L N s q flag a fee school ending ceil active older cap amp salary).trans
  apply mul_le_mul_of_nonneg_left (paid i ix board anchor levels L.L.V draw start s N land live upper atS)
  apply prod_nonneg
  intro j _
  split
  · exact zero_le_one
  · have pay:= (X j).hf
    rw [salary j] at pay
    have nn:=nonneg_of_mul_nonneg_right pay (amp j)
    have step:0<paceT L.L.V.draws.S (X j).m N:=div_pos (L.L.V.draws.S.a_pos _) (L.L.V.draws.S.a_pos _)
    unfold WilsonIndependentMovingFittedEpoch.debit
    positivity

end YM.Integration.WilsonIndependentMovingFittedOptics
