import YM.Integration.WilsonMovingForkSharpAxisCash
import YM.Integration.WilsonIndependentMovingRosterDoseCost

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpCoordinate
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingLateLaw (whole)
open WilsonSeparatedPrefixMovingWages (coupon)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Elected Named)
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{h D k n height seats:ℕ}{H:Hol G}{F:Labels.Frame G h}{T:SectionData F}{p:h<D}


open WilsonSeparatedPrefixMovingJointWaves (sheet)
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointExpansion (angle)
open WilsonMovingForkSharpMaster (Paid)
open scoped ContDiff
variable {a u e:ℕ}{v:Rails h k (u+a) e}
open WilsonSeparatedPrefixMovingJointRows (bill page)
open WilsonMovingForkSharpIncome (gain)
open MeasureTheory
open scoped SchwartzMap
open WilsonSeparatedPrefixMovingJointExpansion (coefficient)
open WilsonSeparatedPrefixMovingJointIntegral (signedRow multiplier growth)
open WilsonMovingForkSharpProjected (amp incoming paired axisRow)
open WilsonMovingForkSharpReportClock (atFar)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonIndependentMatchedFittedSeat (dose)

open WilsonIndependentMatchedReportedProxy (sectionSeal passport)
open WilsonIndependentMatchedPivotSeat (axis)
open WilsonMovingForkSharpGramBirth (pair)
open WilsonSeparatedPrefixMovingUnformedSector (invoice)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonMovingForkSharpAxisWindow (top wage)
open WilsonMovingForkSharpAxisCash (mass)
theorem original (p:h<D)(T:SectionData F)(v:Rails h k (u+a) e):
    ∃pay thermal:Credit,∀(Y:CutsP H T p v C C C C)(m older:ℕ),
      Y.vesselsC.anchor  ≤  older → older  ≤  Y.m → Y.ceilC  ≤  m → m  ≤  Y.N →
      ∀(x:Verse F),x=(paceT Y.ax.S m Y.ceilC)^h • steep Y.ax Y.tx T p Y.N Y.ceilC (m-Y.ceilC) Y.tileP →
      ∀q  ≤  e,let lanes:=fun j=>clock Y.ax Y.tx Y.N Y.m older (atFar Y m x j)
      let Z:=epoch Y.vesselsC older Y.ceilC
      mass lanes q  ≤  (Fintype.card (Alma F):ℝ)*(q+1:ℕ)*(thermal.buy Z*(pay.buy Z*Y.fuel)):=by
  classical
  obtain ⟨pay,basis⟩:=WilsonIndependentFittedReportedWage.original H T p v C C C C
  obtain ⟨thermal,kin⟩:=WilsonIndependentFittedKineticMass.original G h e C F
  refine ⟨pay,thermal,?_⟩
  intro Y m older live age span cut x report q grade lanes Z
  let d:=atFar Y m x
  have placed:d=dose Y (amp Y):=(WilsonMovingForkSharpReportClock.original Y m span cut x report).symm
  have engineering:0 < amp Y:=pow_pos (pace_pos ..) _
  have duration:=WilsonSeparatedPrefixMovingCapturedFees.age Y older live age
  have opening:=Y.windowC.warm
  have sample (j:ℕ)(bound:j ≤ e)(l:Alma F):‖PowerSeries.coeff j (d l)‖ ≤ pay.buy Z*Y.fuel:=by
    rw [placed]
    have price:=basis Y (amp Y) j bound l
    rw [WilsonIndependentMovingRosterDoseCost.rate,abs_of_pos engineering] at price
    change _ ≤ (amp Y)⁻¹*pay.buy Y.Age*(amp Y*Y.fuel) at price
    calc _  ≤  _:=price
         _=pay.buy Y.Age*Y.fuel:=by field_simp
         _ ≤ _:=mul_le_mul_of_nonneg_right (Credit.elder pay opening duration) Y.hf
  have oldTop:Y.m ≤ Y.N:=(Nat.le_add_right Y.m Y.i).trans (Y.hc.trans Y.hn)
  let R:=Y.vesselsC
  let W:WindowS G (e+1) C:=⟨R,older,Y.m-older,Y.N,Y.N,Y.m,live,by omega,oldTop,oldTop⟩
  have label:older+(Y.m-older)=Y.m:=by omega
  have habit:W.Age ≤ Z:=by
    change R.y older+(R.draws.S.scale (older+(Y.m-older))-R.draws.S.scale older)+(Y.m-older:ℕ) ≤ Z
    rw [label]
    have dated:Compar R.draws.S R.y older Y.m ≤ epoch R older Y.m:=(window R older older Y.m live le_rfl age).2.2.1
    apply dated.trans
    change epoch R older Y.m ≤ epoch R older Y.ceilC
    unfold WilsonSeparatedPrefixMovingCalendar.epoch
    have last:=scales R.draws.S (Nat.le_add_right Y.m Y.i)
    change R.draws.S.scale Y.m ≤ R.draws.S.scale Y.ceilC at last
    linarith
  let cash:=pay.buy Z*Y.fuel
  have start:1 ≤ Z:=opening.trans duration
  have nonneg:0 ≤ cash:=mul_nonneg (zero_le_one.trans (pay.purchase start)) Y.hf
  have row (j:ℕ)(bound:j ≤ q)(l:Alma F):‖PowerSeries.coeff j (lanes l)‖ ≤ thermal.buy Z*cash:=by
    have issued:=kin W d cash nonneg sample j (bound.trans grade) l
    have clocked:lanes l=music (relativeF W.robe.draws W.robe.paid W.n W.base W.span) d l:=by
      change clock Y.ax Y.tx Y.N Y.m older (d l)=reel (relativeF Y.ax Y.tx Y.N older (Y.m-older)) (d l)
      have equal:=WilsonIndependentFittedRelativeClock.reported Y.ax Y.tx Y.N older (Y.m-older) (d l)
      simpa only [label] using equal
    rw [clocked]
    exact issued.trans (mul_le_mul_of_nonneg_right (Credit.elder thermal W.warm habit) nonneg)
  unfold mass
  calc _  ≤  ∑_l:Alma F,∑_j∈Finset.range (q+1),thermal.buy Z*cash:=
             Finset.sum_le_sum (fun l _=>Finset.sum_le_sum fun j hj=>row j (by simpa using hj) l)
       _=_:=by simp only [Finset.sum_const,Finset.card_range,Finset.card_univ,nsmul_eq_mul,Nat.cast_add,Nat.cast_one];ring
end YM.Integration.WilsonMovingForkSharpCoordinate
