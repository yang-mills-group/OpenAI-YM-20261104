import YM.Integration.WilsonMovingForkSharpCaptured
import YM.Integration.WilsonIndependentFittedPivotRoster
import YM.Integration.WilsonIndependentMatchedCoverGrade

/-! The full near word and its subtracted finite field are read with the same retained
exterior, on the same original independent course and at the same older date. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpProjected
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingLateLaw (whole far)
open WilsonIndependentMatchedFittedSeat (receiving dose)
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedPivotSeat (film)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U V:Credit}

def amp (Y:CutsP H T p v E W K U):ℝ:=(paceT Y.ax.S Y.m Y.ceilC)^h

def paired (Y:CutsP H T p v E W K U)(Q:SealR G)(ψ:Rarity Q.D)(X:Q.Rider)(y:ℝ)
    (o:CellR)(older rank:ℕ)(near:Era G ℝ):Era G ℝ:=
  cruises Y.ax Y.tx Y.N (rank+Q.h) Y.ceilC older (agateV near (far Y Q ψ X y o Y.i))

def incoming (Y:CutsP H T p v E W K U)(φ:Rarity D)(y:ℝ)(o:CellR):Era G ℝ:=
  WilsonIndependentMatchedCoverProfile.word (amp Y •Y.pt) φ (paceT Y.ax.S Y.m Y.ceilC) y o h

def axisRow (Y:CutsP H T p v E W K U)(Q:SealR G)(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y:ℝ)
    (o:CellR)(older:ℕ)(j:Alma F):Era G ℝ:=
  paired Y Q ψ X y o older h (film Y j 0 φ y o Y.i)

theorem outside (Y:CutsP H T p v E W K U)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q W V)
    (ψ:Rarity Q.D)(X:Q.Rider)(y:ℝ)(o:CellR):Auth Q.h (far Y Q ψ X y o Y.i):=
  WilsonSeparatedPrefixMovingNativeCut.grades Y.vesselsC Q ticket ψ X o y Y.m Y.ceilC Y.N
    (Y.ha.trans (Nat.le_add_right ..)) (Y.hc.trans Y.hn)

theorem split (Y:CutsP H T p v E W K U)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q W V)
    (φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y:ℝ)(o:CellR)(older:ℕ)(before:older≤Y.m):
    paired Y Q ψ X y o older k (incoming Y φ y o)=whole Y Q φ ψ X y o older Y.i+
      paired Y Q ψ X y o older k (receiving Y (amp Y) φ y o Y.i):=by
  let a:=amp Y
  let diff:=seat Y a φ y o Y.i
  let fitted:=receiving Y a φ y o Y.i
  let viewer:=far Y Q ψ X y o Y.i
  have split':incoming Y φ y o=diff+fitted:=WilsonIndependentMatchedTotalTop.placed Y a φ y o
  have hv:Auth Q.h viewer:=outside Y Q ticket ψ X y o
  have hd:Auth k diff:=(WilsonIndependentMatchedCoveredSeats.traced Y a φ y o).1 Y.i le_rfl
  have hr:Auth k fitted:=(WilsonIndependentFittedMixedReturn.paid Y (dose Y a) φ y o).tall v.hk
  have high:=hd.manor hv
  have low:=hr.manor hv
  have δ:=cruisePlus Y.ax (before.trans (Nat.le_add_right Y.m Y.i)) Y.vesselsC.hG Y.vesselsC.green
    (Y.hc.trans Y.hn) (high.add low) low
  rw [add_sub_cancel_right] at δ
  unfold paired
  rw [split',(WilsonIndependentMatchedTotalTop.binary diff fitted viewer).1]
  exact sub_eq_iff_eq_add.mp δ.symm

theorem basis (Y:CutsP H T p v E W K U)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q W V)
    (room:Q.h≤k)(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y:ℝ)(o:CellR)(older:ℕ)(before:older≤Y.m)
    {r:ℕ}(legs:Fin r→YForest G):
    reading (paired Y Q ψ X y o older k (receiving Y (amp Y) φ y o Y.i)).2 legs=
      ∑j,clock Y.ax Y.tx Y.N Y.m older (dose Y (amp Y) j)*reading (axisRow Y Q φ ψ X y o older j).2 legs:=by
  let viewer:=far Y Q ψ X y o Y.i
  let fitted:=dose Y (amp Y)
  have hv:Auth Q.h viewer:=outside Y Q ticket ψ X y o
  have halt:=before.trans (Nat.le_add_right Y.m Y.i)
  have top:=Y.hc.trans Y.hn
  have grade {l:ℕ}{A:Era G ℝ}(auth:Auth l A)(paid:l+Q.h≤k+k):
      paired Y Q ψ X y o older l A=cruises Y.ax Y.tx Y.N (k+k) Y.ceilC older (agateV A viewer):=
    WilsonIndependentMatchedCoverGrade.carried Y.ax Y.tx Y.vesselsC.hG Y.vesselsC.green halt top _ (auth.manor hv) paid
  have inRank:=grade ((WilsonIndependentFittedMixedReturn.paid Y fitted φ y o).tall v.hk) (Nat.add_le_add_left room k)
  have purchased:=(WilsonIndependentFittedPivotRoster.joined Y viewer (hv.tall room) older before fitted φ y o r legs).2
  calc
    _=WilsonIndependentFittedMixedReturn.word Y older (receiving Y (amp Y) φ y o Y.i) viewer r legs:=
      congrArg (fun A:Era G ℝ=>reading A.2 legs) inRank
    _=_:=purchased.trans (Finset.sum_congr rfl fun j _=>by
      have unit:=WilsonIndependentFittedMixedReturn.paid Y (WilsonIndependentMatchedPivotSeat.axis j 0) φ y o
      have filed:=grade unit (Nat.add_le_add v.hk room)
      exact congrArg (fun A:Era G ℝ=>clock Y.ax Y.tx Y.N Y.m older (fitted j)*reading A.2 legs) filed.symm)

theorem original (Y:CutsP H T p v E W K U)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q W V)
    (room:Q.h≤k)(φ:Rarity D)(ψ:Rarity Q.D)(X:Q.Rider)(y:ℝ)(o:CellR)(older:ℕ)(before:older≤Y.m)
    {r:ℕ}(legs:Fin r→YForest G):
    reading (paired Y Q ψ X y o older k (incoming Y φ y o)).2 legs-
      ∑j,clock Y.ax Y.tx Y.N Y.m older (dose Y (amp Y) j)*reading (axisRow Y Q φ ψ X y o older j).2 legs=
        reading (whole Y Q φ ψ X y o older Y.i).2 legs:=by
  rw [←basis Y Q ticket room φ ψ X y o older before legs,split Y Q ticket φ ψ X y o older before]
  apply PowerSeries.ext
  intro a
  simp [WilsonOlderFreshSoftSocketKinetic.reading]

end YM.Integration.WilsonMovingForkSharpProjected
