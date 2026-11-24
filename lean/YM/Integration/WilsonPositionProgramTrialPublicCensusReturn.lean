import YM.Integration.WilsonPositionProgramTrialPublicCensus
import YM.Integration.WilsonIndependentMatchedPhysicalCohort
import YM.Integration.WilsonPositionProgramTrialHomeFaces

/-! The price of the original fixed-address K filings summed over their true visits, against the same measured normal coordinates on a separately capped history. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCensusReturn
open Precision Function Finset Lattice Laurent Wilson RG Source Labels Marker Tree Exterior PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.StableStrip WilsonCoeffUV.Power
open RG.Supply Next.Foundations PhysicalNext.Repeat
open WilsonFiniteMarkedHistoryStep
open WilsonOriginalPublicNodalChildSites (digits here)
open WilsonPositionProgramTrialPublicPulse (choices frame sites survey)
open WilsonReceivedCanonicalSocketSeed (contact)
open WilsonPositionProgramTrialPublicGather (gather)
open WilsonPositionProgramTrialPublicOldReturn (portfolio)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentRawPhysicalFaces (ordered entered)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonPositionProgramTrialHomeFaces (Filed)
open WilsonMarkedIndependentNormalizedElection (deck)
open PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
open WilsonIndependentMatchedPhysicalReturn (ordinary)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonPositionProgramTrialAccrued (home)

variable {G:Gauge}{n k u e:ℕ}
local notation "Lib" => Fin (n+1)
local notation "C" => Credit.leanC

def logged (R:Run G)(D d:Lib→ℕ)(j K N host c:ℕ)(S:Finset Lib)
    (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (φ:Lib→ℂ→L[ℝ]ℝ)(T:(i:Lib)→Rarity (D i))(y:ℝ)(o:CellR):Era G ℝ:=
  let L:=R.family.path.levels
  let O:=R.metals.O
  let x:Lib→ℝ:=fun _=>paceT L.S j K
  let off:Lib→CellR:=fun _=>o
  ∑z:choices D T x y off S,portfolio R D d (fun i=>contact (D i)) (fun _=>zeroC) S fill v φ
    (frame D d T x y off S z) L O N (digits L K (sites D T x y off S z)) host c K
    (here L K (sites D T x y off S z) c)

theorem quoted (R:Run G)(W:Initialize G)(D d:Lib→ℕ)(cut:∀i,d i<D i)
    (own:∀i,Rails (d i) k u e)(α:∀i,Alma (R.family.labels.level (d i))→ℝ)(Z B:Lib→Credit)
    (N j c K host:ℕ)(hc:host≤c)(cK:c≤K)(KN:K≤N)(simple:G.Simple)(ratio:LocalRatio R.metals.O)
    (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (φ:Lib→ℂ→L[ℝ]ℝ)(S:Finset Lib)[Nonempty S]{a:ℕ}(idx:Fin (a+1)≃S)
    (X:∀i,CutsP (hol G) ((deck (G:=G) d D cut) i).ans ((deck (G:=G) d D cut) i).path (own i) C C C C)
    (file:Filed R W d D cut (fun _=>false) own (fun i=>written _ (v i) (φ i)) α Z B j K N X)
    (T:(i:Lib)→Rarity (D i))(y:ℝ)(o:CellR):
    let L:=R.family.path.levels
    let Q:=deck (G:=G) d D cut
    let leg:Fin (a+1)→Lib:=fun i=>idx i
    logged R D d j K N host c S fill v φ T y o =
      cruises L R.metals.O N (capP (Q∘leg)) K host (ordinary (Q:=Q∘leg) (v:=fun i=>own (leg i)) L
        (fun i=>X (leg i)) (fun i=>T (leg i)) j K y o):=by
  let L:=R.family.path.levels
  let Q:=deck (G:=G) d D cut
  let leg:Fin (a+1)→Lib:=fun i=>idx i
  have rank:mass d S=capP (Q∘leg):=by
    unfold mass capP
    change ∑i∈S,d i=∑i,d (idx i)
    rw [←Finset.sum_coe_sort]
    exact (Equiv.sum_comp idx (fun i:S=>d i.val)).symm
  have sale:=WilsonPositionProgramTrialPublicCensus.original R W D d cut own α Z B N j c K host hc cK KN
    simple ratio fill v φ S idx X file T (fun _=>paceT L.S j K) (fun _=>pace_pos ..) y (fun _=>o)
  dsimp only at sale
  rw [rank] at sale
  exact sale

end YM.Integration.WilsonPositionProgramTrialPublicCensusReturn
end
