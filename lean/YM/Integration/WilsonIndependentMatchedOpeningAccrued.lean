import YM.Integration.WilsonIndependentMatchedOpeningProfile
import YM.Integration.WilsonIndependentMatchedOrdinaryFitted
/-! The actual filed K source and its true accrued projection share their complete group stencil before the next evolution. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningAccrued
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Wheel.Flooring PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedSectionIncome (leaf)
open WilsonIndependentMatchedOrdinarySeat (here received)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open scoped Classical BigOperators
open WilsonIndependentMatchedTopReceipt (realDose)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedOpeningFiled (terms planted)
open WilsonCoeffUV.StableStrip
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedFittedSeat (receiving)
variable {G:Gauge}{H:Hol G}{h D k u e d:ℕ}{p:h<D}{native:Labels.Frame G h}
  {T:SectionData native}{v:Rails h k u e}{E A K U:Credit}
variable (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
def group (s:Bool)(w:d<D)(c:Verse (R.family.labels.level d))(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ):Era G ℝ:=
  ∑z∈VisitsT φ x y o,drumB l x • ∑j,terms R W s w (wheelC x y z φ.ψ o) c z j

theorem issued (s:Bool)(w:d<D)(c:Verse (R.family.labels.level d))(X:CutsP H T p v E A K U)
    (amp a:ℝ)(file:(a/amp) • X.pt=a • Shrine (plate (sectionAt R W s d) w) c)
    (φ:Rarity D)(y:ℝ)(o:CellR):
    let x:=paceT X.ax.S X.m (X.m+X.i)
    word ((a/amp) • X.pt) φ x y o h=group R W s w (a • c) φ x y o h ∧
    WilsonIndependentMatchedCoveredSeats.seat X (a/amp) φ y o X.i=
      group R W s w (a • c) φ x y o h-receiving X (a/amp) φ y o X.i:=by
  intro x
  have upper: word ((a/amp) • X.pt) φ x y o h=group R W s w (a • c) φ x y o h:=by
    rw [file];exact WilsonIndependentMatchedOpeningProfile.scaled R W s w c φ x y o h a (pace_pos ..)
  refine ⟨upper,?_⟩
  rw [←upper,WilsonIndependentMatchedTotalTop.placed]
  abel

theorem filed (s:Bool)(w:d<D)(c:Verse (R.family.labels.level d))(X:CutsP H T p v E A K U)
    {L:Torch H T p v E A K}{run:XSpace.Run}{base idx f:ℕ}{amp δ η fee:ℝ}
    (file:Filed X L run base idx f amp δ η fee (Shrine (plate (sectionAt R W s d) w) c))
    (a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR):
    let x:=paceT X.ax.S X.m (X.m+X.i)
    word ((a/amp) • X.pt) φ x y o h=group R W s w (a • c) φ x y o h ∧
    WilsonIndependentMatchedCoveredSeats.seat X (a/amp) φ y o X.i=
      group R W s w (a • c) φ x y o h-receiving X (a/amp) φ y o X.i:=
  issued R W s w c X amp a (file.actual a) φ y o

theorem fresh (kind:Bool)(X:CutsP H (sectionAt R W kind h) p v E A K U)
    (birth:X.N=X.ceilC)(t:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR):
    receiving X t φ y o X.i=group R W kind p (t • X.tileP) φ (paceT X.ax.S X.m (X.m+X.i)) y o h:=by
  have top:=WilsonIndependentMatchedTopStencils.initial X birth
  rw [WilsonIndependentMatchedFittedSeat.inlet,top]
  exact WilsonIndependentMatchedOpeningProfile.scaled R W kind p X.tileP φ _ y o h t (pace_pos ..)
end YM.Integration.WilsonIndependentMatchedOpeningAccrued
