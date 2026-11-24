import YM.Integration.WilsonMovingForkSharpAxisCash
import YM.Integration.WilsonSeparatedPrefixMovingJointReceipt

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpAxisWave
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
open WilsonMovingForkSharpAxisCash (panel)
private theorem axisAt (Y:CutsP H T p v C C C C)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q C C)
    (φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (X:Q.Rider)(y:ℝ)(o:CellR)(older i:ℕ)(ear:older ≤ Y.m)(home:Y.m ≤ i)(ceiling:i ≤ Y.N)
    (j:Alma F)(q:ℕ)(w:Fin 0→YForest G)(c d:Bool):
    Measurable fun ξ:Euclid=>(pair Y.vesselsC (sectionSeal T p) Q (sheet φ (angle ξ) c)
      (sheet χ (angle ξ) d) (axis j 0) X o y Y.m i older Y.N).2 q 0 w:=by
  let R:=Y.vesselsC
  let A:=sectionSeal T p
  let x:=paceT Y.ax.S Y.m i
  let P:=polarP R.draws R.paid A.ans A.path Y.N Y.m i (axis j 0)
  let far:=polarP R.draws R.paid Q.ans Q.path Y.N Y.m i X
  have paid:R.anchor ≤ i:=Y.ha.trans home
  have ok:Auth h P:=by
    dsimp only [P]
    let κ:=passport Y
    change Auth A.h (polarP R.draws R.paid A.ans A.path Y.N Y.m i (axis j 0))
    rw [←κ.lands,←κ.modes]
    exact On_auth (tournure κ.f.arch (axis j 0) (κ.tap.symm ▸ paid) ceiling)
  have good:Auth Q.h far:=by
    dsimp only [far]
    rw [←ticket.lands,←ticket.modes]
    exact On_auth (tournure ticket.f.arch X (ticket.tap.symm ▸ paid) ceiling)
  exact (WilsonSeparatedPrefixMovingJointContinuity.original R P far ok good (ear.trans home) ceiling
    (WilsonSeparatedPrefixMovingJointFarBook.abroad q 0 w)
    (WilsonSeparatedPrefixMovingJetPrice.cover D q 0 w) (WilsonSeparatedPrefixMovingJetService.cover D q 0 w)
    (WilsonSeparatedPrefixMovingJetPrice.cover Q.D q 0 w) (WilsonSeparatedPrefixMovingJetService.cover Q.D q 0 w)
    φ χ hφ hχ x y x y (pace_pos ..) (pace_le _ home) (pace_pos ..) (pace_le _ home)
    o o h Q.h c d).2

theorem measured (Y:CutsP H T p v C C C C)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q C C)
    (φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (X:Q.Rider)(y:ℝ)(o:CellR)(m older q:ℕ)(ear:older ≤ Y.m)(x:Verse F)(w:Fin 0→YForest G)(arm c d:Bool):
    Measurable fun ξ:Euclid=>panel Y Q (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) X y o m older q x w arm:=by
  classical
  simp only [WilsonMovingForkSharpAxisCash.panel,map_sum,PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.measurable_sum _ fun j _=>Finset.measurable_sum _ fun i _=>measurable_const.mul ?_
  cases arm
  · simp only [if_false,Bool.false_eq_true,WilsonOlderFreshSoftSocketKinetic.reading,PowerSeries.coeff_mk]
    change Measurable fun ξ:Euclid=>(pair Y.vesselsC (sectionSeal T p) Q (sheet φ (angle ξ) c)
      (sheet χ (angle ξ) d) (axis j 0) X o y Y.m Y.ceilC older Y.N).2 (q-i) 0 w
    exact axisAt Y Q ticket φ χ hφ hχ X y o older Y.ceilC ear (Nat.le_add_right ..)
      (Y.hc.trans Y.hn) j (q-i) w c d
  · simp only [if_true,WilsonOlderFreshSoftSocketKinetic.reading,PowerSeries.coeff_mk]
    change Measurable fun ξ:Euclid=>(pair Y.vesselsC (sectionSeal T p) Q (sheet φ (angle ξ) c)
      (sheet χ (angle ξ) d) (axis j 0) X o y Y.m Y.N older Y.N).2 (q-i) 0 w
    exact axisAt Y Q ticket φ χ hφ hχ X y o older Y.N ear ((Nat.le_add_right Y.m Y.i).trans (Y.hc.trans Y.hn))
      le_rfl j (q-i) w c d

def tested (Y:CutsP H T p v C C C C)(Q:SealR G)(φ:Rarity D)(χ:Rarity Q.D)(X:Q.Rider)
    (y:ℝ)(o:CellR)(m older q:ℕ)(x:Verse F)(w:Fin 0→YForest G)(S:𝓢(Euclid,ℂ))(arm:Bool)(ξ:Euclid):ℝ:=
  ∑c:Bool,∑d:Bool,coefficient (S ξ) c d*
    panel Y Q (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) X y o m older q x w arm

theorem original (Y:CutsP H T p v C C C C)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q C C)
    (φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (X:Q.Rider)(y:ℝ)(o:CellR)(m older q:ℕ)(ear:older ≤ Y.m)(x:Verse F)(w:Fin 0→YForest G)(S:𝓢(Euclid,ℂ))(arm:Bool):
    Measurable (tested Y Q φ χ X y o m older q x w S arm):=by
  apply Finset.measurable_sum _ fun c _=>Finset.measurable_sum _ fun d _=>?_
  have co:Continuous (fun ξ:Euclid=>coefficient (S ξ) c d):=by
    cases c <;> cases d <;> dsimp only [coefficient] <;> fun_prop
  exact co.measurable.mul (measured Y Q ticket φ χ hφ hχ X y o m older q ear x w arm c d)
end YM.Integration.WilsonMovingForkSharpAxisWave
