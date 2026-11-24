import YM.Integration.WilsonIndependentMatchedOpeningFiled
import YM.Integration.WilsonIndependentMatchedOrdinaryProfile
/-! The exact fully tested finite-restart source before the older Wilson courses act. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningProfile
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
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G){d D:ℕ}
local notation "F" => R.family.labels.level d

theorem original (s:Bool)(w:d<D)(c:Verse F)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(hx:0<x):
    word (Shrine (plate (sectionAt R W s d) w) c) φ x y o l=
      ∑z∈VisitsT φ x y o,drumB l x •
        ∑a,terms R W s w (wheelC x y z φ.ψ o) c z a:=by
  rw [word,pupil_eye l _ φ x y o hx]
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg ((drumB l x) • ·)
  exact WilsonIndependentMatchedOpeningFiled.original R W s w (wheelC x y z φ.ψ o) c z

theorem scaled (s:Bool)(w:d<D)(c:Verse F)(φ:Rarity D)(x y:ℝ)(o:CellR)(l:ℕ)(a:ℝ)(hx:0<x):
    word (a • Shrine (plate (sectionAt R W s d) w) c) φ x y o l=
      ∑z∈VisitsT φ x y o,drumB l x •
        ∑t,terms R W s w (wheelC x y z φ.ψ o) (a • c) z t:=by
  rw [←WilsonCoeffUV.StableStrip.shrine_μ]
  exact original R W s w _ φ x y o l hx
end YM.Integration.WilsonIndependentMatchedOpeningProfile
