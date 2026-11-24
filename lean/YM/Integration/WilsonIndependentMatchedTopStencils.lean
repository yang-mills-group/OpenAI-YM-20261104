import YM.Integration.WilsonIndependentMatchedLowerAtSix
import YM.Integration.WilsonPositionProgramMasterBirth
import YM.Integration.WilsonMaxwellThermometerSurveyBirth
import YM.Integration.WilsonIndependentMatchedNamedPair

/-! At a genuine top the fitted field expands on the same section as its
original peak. The coefficient vector retains all components returned from the
lower reporting date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedTopStencils
open WilsonCoeffUV WilsonCoeffUV.Shard
open WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open XSpace PhysicalNext.Repeat.Legato
open scoped BigOperators Topology Classical

variable {G:Gauge}{D d k u e:ℕ}{F:Labels.Frame G d}
  {H:Hol G}{T:SectionData F}{w:d<D}{v:Rails d k u e}{E W K U:Credit}

theorem initial (L:CutsP H T w v E W K U)(top:L.N=L.ceilC) :
    L.Ntop=(fun n i => herald T w i n, anthem T w) := by
  change Peaks L.ax L.tx T w L.N L.ceilC = _
  rw [←top, Peak_initial]

variable (R:Run G)
local notation "F₀" => R.family.labels.level d

/-- The fitted physical section, with its actual test and complete fitted tile. -/
theorem original (L:CutsP H (R.family.localSection d) w v E W K U)
    (top:L.N=L.ceilC)(n:Side)(b:Volume D) :
    let M:=Shrine L.Ntop L.tileP
    X^WilsonPositionProgramMasterBirth.rank R (d:=d) * flash (jot b (M.1 n)) =
      ∑ s, X^(WilsonPositionProgramMasterBirth.rank R (d:=d)-valence F₀ s) *
        Blue.soil (L.tileP s) * (jewelBloom w s b • jet (Plies (R.family.localSection d) (sheet F₀ s) n)) := by
  have eq:L.Ntop=Peaks R.family.path.levels R.metals.O (R.family.localSection d) w L.N L.N := by
    rw [initial L top,Peak_initial]
  dsimp only
  rw [eq]
  exact WilsonPositionProgramMasterBirth.assembly R w L.N n L.tileP b

variable (I:Initialize G)
local notation "T₁" => WilsonMaxwellThermometerSurveyIncome.chapter I d

/-- The elected independent survey is expanded in its own genuine stencils on
the same true top and with each test derivative retained. -/
theorem survey (L:CutsP H T₁ w v E W K U)(top:L.N=L.ceilC)(n:Side)(b:Volume D) :
    let M:=Shrine L.Ntop L.tileP
    X^WilsonPositionProgramMasterBirth.rank R (d:=d) * flash (jot b (M.1 n)) =
      ∑ s, X^(WilsonPositionProgramMasterBirth.rank R (d:=d)-valence ((primes G).F d) s) *
        Blue.soil (L.tileP s) * (jewelBloom w s b • jet (Plies T₁ (sheet ((primes G).F d) s) n)) := by
  have eq:L.Ntop=Peaks R.family.path.levels R.metals.O T₁ w L.N L.N := by
    rw [initial L top,Peak_initial]
  dsimp only
  rw [eq]
  exact WilsonMaxwellThermometerSurveyBirth.assembly R I w L.N n L.tileP b

end YM.Integration.WilsonIndependentMatchedTopStencils
