import YM.Integration.WilsonIndependentConditionedFolioInventory
import YM.Integration.WilsonIndependentConditionedFolioReporter
import YM.Integration.WilsonIndependentConditionedFolioVolume
import YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
import YM.Integration.WilsonOriginalPublicNodalTestedChronology

/-! An individual native visit of the tested pupil on every occupied mark. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioTerm
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

open WilsonIndependentNotebookConstantSeat (issue part)
open private seated_sum from YM.Integration.WilsonIndependentNotebookConstantSeat
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentMatchedOpeningColumn (column)


open WilsonIndependentMatchedCoverProfile (word)

open WilsonIndependentRawRosterWord (fold degree)
open RegulatorIR.Cluster (Composite)
open WilsonIndependentMatchedOpeningRoster (field)
open WilsonIndependentRawPhysicalFaces (ordered entered)
open WilsonOriginalPublicNodalTestedChronology (registered rank)
open WilsonIndependentConditionedFolioPupil (atSite)

open WilsonIndependentMatchedOpeningRoster (enrolled)
open WilsonIndependentRawPhysicalFaces (Lists)
open WilsonIndependentConditionedFolioReader (ear)
open WilsonOlderFreshHybridClock (flat)
open WilsonCoeffUV.Power PertExtension Metric Precision Exterior
open private scales from YM.Integration.WilsonIndependentConditionedFolioVisit
local notation "J" => Fin 2
variable {G:Gauge}(R:Run G)(W:Initialize G)(d:J→ℕ){D:J→ℕ}(cut:∀i,d i<D i)(home:J → Cover)
local notation "F" => R.family.labels.level
local notation "L" => R.family.path.levels
local instance full_ne:Nonempty (↥(Finset.univ:Finset J)):=⟨⟨0,mem_univ _⟩⟩

def partField (i:J)(b:(F (d i)).Index):Era G ℝ:=column R W false (cut i) (seat (F (d i)) b) (home i)

theorem price (i:J)(b:(F (d i)).Index)(k:ℕ)(cap:d i≤k)(s:ℝ):
    Auth k (s • partField R W d cut home i b):=by
  have a:=WilsonIndependentMatchedOpeningColumn.enrolled R W false (cut i) (seat (F (d i)) b) (home i)
  have maxrank:valence (F (d i)) (seat (F (d i)) b)≤k:=
    ((WilsonMaxwellThermometerMaximalHead.rank (F (d i)) b).trans (Nat.div_le_self ..)).trans cap
  exact (a.tall maxrank).tuft (s • ContinuousLinearMap.id ℝ ℝ)

def picks (a:(F (d 0)).Index)(b:(F (d 1)).Index):(i:J)→(F (d i)).Index:=
  Fin.cons a (Fin.cons b (fun j=>j.elim0))

def archive (N K v:ℕ)(b:∀i,(F (d i)).Index):Era G ℝ:=
  cruises L R.metals.O N (rank R d b univ) K v (registered R W d b cut home univ)

theorem original (u:G.ColorIndex)
    (tags:∀ i n,(FormalBulk08.Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (simple:G.Simple)(priceRows:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices priceRows R.kit)
    {A:Levels G}{O:ChartRatio G}(layout:A=L)(reset:LocalRatio O)(k:ℕ)(cap:∀i,d i≤k)(N K v:ℕ)(vk:v ≤ K)(kn:K ≤ N)
    (a:(F (d 0)).Index)(b:(F (d 1)).Index)(C E g:ℝ)(q:ℕ)(z:Fin 0→YForest G):
    ear q g z (cruises A O N (k+k) K v (agateV (C • partField R W d cut home 0 a) (E • partField R W d cut home 1 b)))=
    ((C*E*flat (archive R W d cut home N K v (picks R d a b)) q g:ℝ):ℂ):=by
  let key:=picks R d a b
  have p0:Auth k (partField R W d cut home 0 a):=by simpa using price R W d cut home 0 a k (cap 0) 1
  have p1:Auth k (partField R W d cut home 1 b):=by simpa using price R W d cut home 1 b k (cap 1) 1
  have same:agateV (partField R W d cut home 0 a) (partField R W d cut home 1 b)=registered R W d key cut home univ:=
    WilsonIndependentConditionedFolioInventory.pair R W d key cut home
  let Z:=registered R W d key cut home univ
  have native:Auth (rank R d key univ) Z:=
    enrolled R W (fun _:↥(Finset.univ:Finset J)=>false) (fun i=>d i) (fun i=>key i) (fun i=>cut i) (fun i=>home i) ordered
  have paid:Auth (k+k) Z:=by
    change Auth (k+k) (registered R W d key cut home univ)
    rw [←same]
    exact p0.manor p1
  rw [scales p0 p1,same,WilsonIndependentConditionedFolioReporter.reported R u tags simple priceRows funded
    layout reset N K v (k+k) (rank R d key univ) vk kn Z paid native,WilsonIndependentConditionedFolioReporter.scalar]
  rfl

end YM.Integration.WilsonIndependentConditionedFolioTerm
end
