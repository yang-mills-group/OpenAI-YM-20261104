import YM.Integration.WilsonIndependentMatchedProxyIncome
import YM.WilsonCoeffUV.Stable.Analytic.Step

/-! The positive seat opposite a designated residual is the very same
fitted top Shrine, including the physical prefactor on every coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedFittedSeat
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

open WilsonIndependentMatchedReportedProxy WilsonIndependentMatchedCoveredSeats
open WilsonIndependentMatchedSeatedIncome

def dose (X:CutsP H T p v E W K U)(a:ℝ):Verse F:=reported X (a • X.tileP)
def receiving (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR):ℕ → Era G ℝ:=
  printed X.vesselsC (sectionSeal T p) φ (dose X a) X.m X.N y o

theorem scaled (X:CutsP H T p v E W K U)(a:ℝ):
    polarP X.ax X.tx T p X.N X.m (X.m+X.i) (dose X a)=a • Shrine X.Ntop X.tileP:=by
  rw [dose,fine,Shrine,Shrine,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact WilsonCoeffUV.StableStrip.stem_μ _ _ a

theorem inlet (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR):
    receiving X a φ y o X.i=word (a • Shrine X.Ntop X.tileP) φ
      (paceT X.ax.S X.m (X.m+X.i)) y o h:=by
  change word (polarP X.ax X.tx T p X.N X.m (X.m+X.i) (dose X a)) φ _ y o h=_
  rw [scaled]

theorem taken (X:CutsP H T p v E W K U)(a:ℝ):
    a • X.springP X.i+polarP X.ax X.tx T p X.N X.m (X.m+X.i) (dose X a)=a • X.pt:=by
  rw [scaled,←smul_add,X.carve1,sub_add_cancel]

def fee (X:CutsP H T p v E W K U)(c:ℝ)(u b:ℕ):ℝ:=
  (WilsonIndependentMatchedProxyIncome.tariff H T p e u b E W U).buy X.Age*
    WilsonIndependentMatchedProxyIncome.cost e (dose X c)

theorem funds (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR)
    (δ B:ℝ)(test:Amplitude φ B)(u b:ℕ):
    Funds X.vesselsC h h X.m X.i u b φ y o δ 0 (fee X a u b) B (receiving X a φ y o):=
  WilsonIndependentMatchedProxyIncome.original X φ (dose X a) y o δ B test u b

theorem nn (X:CutsP H T p v E W K U)(a:ℝ)(u b:ℕ):0 ≤ fee X a u b:=
  mul_nonneg (zero_le_one.trans ((WilsonIndependentMatchedProxyIncome.tariff H T p e u b E W U).purchase X.windowC.warm))
    (WilsonIndependentMatchedProxyIncome.nn _)

/-- The fitted peer and the designated residual use their own genuine fields
and the same normalized transfer in each ordered product. -/
theorem along (X Y:CutsP H T p v E W K U)(school:Y.L=X.L)
    (home:Y.m=X.m)(ceiling:Y.N=X.N)(a c:ℝ)(φ ψ:Rarity D)(y:ℝ)(o:CellR):
    Posted X.vesselsC k h X.m X.N X.i (seat X a φ y o) (receiving Y c ψ y o) ∧
    Posted X.vesselsC h k X.m X.N X.i (receiving Y c ψ y o) (seat X a φ y o):=by
  have realm:Y.vesselsC=X.vesselsC:=congrArg (fun z=>z.L.V) school
  have same:receiving Y c ψ y o=printed X.vesselsC (sectionSeal T p) ψ (dose Y c) X.m X.N y o:=by
    unfold receiving
    rw [realm,home,ceiling]
  rw [same]
  exact mixed X (sectionSeal T p) (passport X) a φ ψ (dose Y c) y o

end YM.Integration.WilsonIndependentMatchedFittedSeat
