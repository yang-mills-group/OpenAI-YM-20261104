import YM.Integration.WilsonIndependentConditionedFolioTerm
import YM.Integration.WilsonIndependentConditionedPlacementPorts
import YM.Integration.WilsonIndependentConditionedFolioReporter
import YM.Integration.WilsonIndependentConditionedFolioVolume
import YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
import YM.Integration.WilsonOriginalPublicNodalTestedChronology

/-! An individual native visit of the tested pupil on every occupied mark. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedFolioCellResponse
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
open WilsonIndependentConditionedFolioReader (site)
open WilsonIndependentConditionedPlacementArm (stencil head)
open WilsonIndependentConditionedFolioTerm (picks partField archive)
local notation "J" => Fin 2
variable {G:Gauge}(R:Run G)(W:Initialize G){d D:J→ℕ}(fit:∀i,d i<D i)
local notation "F" => R.family.labels.level
local notation "L" => R.family.path.levels
variable (j:J→ℕ)(m f K N per:ℕ)(axes:∀i,R.family.label (d i)≃ₗ[ℂ]R.family.label (d i))
  (bare:∀i,R.family.label (d i))(turn:J→Signed)(hand im:J→Bool)(phase:J→ℂ)
local notation "x" => R.family.S.a K/R.family.S.a m
local notation "ink" i => head R (d i) (j i) K N per (axes i) (bare i) (turn i) (hand i) (phase i)

def entry (i:J)(φ:Rarity (D i))(y:ℝ)(o:CellR)(n:Cover)(b:(F (d i)).Index):ℝ:=
  x^4*(part (im i) ((ink i) b)*φ.ψ.val (Mer.position x y o n))

theorem local_sum (i:J)(φ:Rarity (D i))(y:ℝ)(o:CellR)(home:J → Cover):
    site (stencil R (axes i) (bare i) (turn i) (hand i) (phase i) (j i) m f K N per W false false (im i) (fit i))
      φ x y o (d i) (home i)=∑b:(F (d i)).Index,
      entry R j m K N per axes bare turn hand im phase i φ y o (home i) b •
        partField R W d fit home i b:=by
  rw [WilsonIndependentConditionedFolioVolume.site_at,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [smul_smul]
  rfl

theorem original {k e:ℕ}{B:Credit}(V:Realm G (e+1) B)(layout:V.draws=L)(cap:∀i,d i ≤ k)
    (u:G.ColorIndex)(tags:∀ i n,(FormalBulk08.Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (simple:G.Simple)(priceRows:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices priceRows R.kit)
    (v:ℕ)(vk:v ≤ K)(kn:K ≤ N)(φ:(i:J)→Rarity (D i))(y:ℝ)(o:CellR)(home:J → Cover)
    (z:Fin 0→YForest G)(q:ℕ)(g:ℝ):
    let call:=fun i:J=>site
      (stencil R (axes i) (bare i) (turn i) (hand i) (phase i) (j i) m f K N per W false false (im i) (fit i))
      (φ i) x y o (d i) (home i)
    let pay:=fun i:J=>entry R j m K N per axes bare turn hand im phase i (φ i) y o (home i)
    ear q g z (cruises V.draws V.paid N (k+k) K v (agateV (call 0) (call 1)))=
      ∑a:(F (d 0)).Index,∑b:(F (d 1)).Index, ((pay 0 a*pay 1 b*flat
        (archive R W d fit home N K v (picks R d a b)) q g:ℝ):ℂ):=by
  classical
  intro call pay
  have entered(i:J):call i=∑b:(F (d i)).Index,pay i b • partField R W d fit home i b:=
    local_sum R W fit j m f K N per axes bare turn hand im phase i (φ i) y o home
  rw [entered,entered]
  rw [WilsonIndependentConditionedFolioReader.pair V vk kn _ _ _ _
    (fun b _=>WilsonIndependentConditionedFolioTerm.price R W d fit home 0 b k (cap 0) (pay 0 b))
    (fun b _=>WilsonIndependentConditionedFolioTerm.price R W d fit home 1 b k (cap 1) (pay 1 b))]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact WilsonIndependentConditionedFolioTerm.original R W d fit home u tags simple priceRows funded layout V.green k cap
    N K v vk kn a b (pay 0 a) (pay 1 b) g q z

end YM.Integration.WilsonIndependentConditionedFolioCellResponse
end
