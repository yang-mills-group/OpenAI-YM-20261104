import YM.Integration.WilsonIndependentMatchedCoverMixed
import YM.Integration.WilsonIndependentMatchedSeatedIncome

/-! Put the already fitted summand on its genuine normalized reporting
vector and its own canonical cover path, retaining all scalar and lower
entries of the same actual layout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedReportedProxy
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

def sectionSeal (T:SectionData F)(p:h<D):SealR G:=⟨h,F,D,T,p⟩
def passport (X:CutsP H T p v E W K U):PassportC H X.vesselsC (sectionSeal T p) W U where
  f:=X.L'
  lands:=congrArg (fun z=>z.V.draws) X.he
  modes:=congrArg (fun z=>z.V.paid) X.he
  depths:=congrArg (fun z=>z.V.y) X.he
  tap:=congrArg (fun z=>z.V.anchor) X.he

def reported (X:CutsP H T p v E W K U)(c:Verse F):Verse F:=
  street X.ax X.tx T p X.N X.m X.i c

lemma returned (X:CutsP H T p v E W K U)(c:Verse F):
    steep X.ax X.tx T p X.N X.m X.i (reported X c)=c:=by
  have hb:X.m+X.i ≤ X.N:=X.hc.trans X.hn
  exact street_up X.L.L X.ha hb (Street_up X.L.L (reported X c) X.ha hb)

theorem fine (X:CutsP H T p v E W K U)(c:Verse F):
    polarP X.ax X.tx T p X.N X.m (X.m+X.i) (reported X c)=Shrine X.Ntop c:=by
  rw [polarP,Nat.add_sub_cancel_left,returned]

theorem coarse (X:CutsP H T p v E W K U)(c:Verse F):
    polarP X.ax X.tx T p X.N X.m X.m (reported X c)=Shrine (X.L.L.lore X.N X.m) (reported X c):=
  steep_nil X.L.L X.ha ((Nat.le_add_right _ _).trans (X.hc.trans X.hn)) _

/-- The signed residual and the complete projected peer add back the true
offered top field on this cut, before the marked product is taken. -/
theorem appointed (X:CutsP H T p v E W K U):
    X.springP X.i+polarP X.ax X.tx T p X.N X.m (X.m+X.i) (reported X X.tileP)=X.pt:=by
  rw [fine,X.carve1,sub_add_cancel]

end YM.Integration.WilsonIndependentMatchedReportedProxy
