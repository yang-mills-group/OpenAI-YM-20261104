import YM.Integration.WilsonIndependentSpoutPhysicalHomes
import YM.Integration.WilsonIndependentMatchedBufferedVacuum
import YM.Integration.WilsonPositionProgramTrialReverseLens

/-! The normalized public master at the common fresh top, with its actual lower and unit coordinates. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutNormalizedMaster
open Lattice Wilson Tree RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision Exterior Gauge
open PhysicalNext PhysicalNext.Repeat Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Bank
open WilsonCoeffUV.StableStrip WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Ticket
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedOpeningComposite (branch)
open WilsonIndependentMatchedOpeningHomes (Visits rent name site rowAt spent assigned)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentMatchedOpeningRoster (field)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonIndependentMatchedBufferedVacuum (stopped)
open scoped BigOperators Classical
variable {G:Gauge}{n:ℕ}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
local notation "L" => R.family.path.levels
local notation "Q" => (deck (G:=G) d D cut)

def vector (b:Herit Q)(m K:ℕ)(i:Fin (n+1)):Verse (R.family.labels.level (d i)):=
  received L R.metals.O (Q i) m K K (b i)

theorem one (b:Herit Q)(φ:Wilt Q)(m K:ℕ)(y:ℝ)(o:CellR)(i:Fin (n+1)):
    awaken Q L R.metals.O φ (normalized L R.metals.O Q b m K) m K K y o i=
      word (Shrine (plate (sectionAt R W false (d i)) (cut i)) (vector R d D cut b m K i))
        (φ i) (paceT (L).S m K) y o (d i):=by
  change word (Shrine (Peaks L R.metals.O (Q i).ans (Q i).path K K) (vector R d D cut b m K i))
    (φ i) (paceT (L).S m K) y o (d i)=_
  rw [Peak_initial]
  rfl

theorem opened (b:Herit Q)(φ:Wilt Q)(m K:ℕ)(y:ℝ)(o:CellR):
    let x:Fin (n+1)→ℝ:=fun _=>paceT (L).S m K
    let locations:Fin (n+1)→CellR:=fun _=>o
    Ashore Q L R.metals.O φ (normalized L R.metals.O Q b m K) m K K y o=
      ∑z:((i:Fin (n+1))→Visits R d D φ x y locations i),
        affiled (∏i,rent R d D cut (vector R d D cut b m K) φ x y locations (fun _=>1) d i (z i))
          (field R W (fun _=>false) d (name R d D φ x y locations z) cut (site R d D φ x y locations z) (branch n id)):=by
  intro x loc
  let c:=vector R d D cut b m K
  let rows:=rowAt R W (fun _=>false) d D cut c φ x y loc (fun _=>1) d
  have paid (i:Fin (n+1))(z:Visits R d D φ x y loc i):Auth (d i) (rows i z):=
    (spent R W (fun _=>false) d D cut c φ x y loc (fun _=>1) d i z).tall (valence_cap _ _)
  have tile (i:Fin (n+1)):awaken Q L R.metals.O φ (normalized L R.metals.O Q b m K) m K K y o i=∑z,rows i z:=by
    rw [one R W d D cut b φ m K y o i]
    change word (Shrine (plate (sectionAt R W false (d i)) (cut i)) (c i)) (φ i) (x i) y (loc i) (d i)=∑z,rows i z
    rw [←one_smul ℝ (Shrine (plate (sectionAt R W false (d i)) (cut i)) (c i))]
    exact (WilsonIndependentMatchedOpeningProfile.scaled R W false (cut i) (c i) (φ i) (x i) y (loc i) (d i) 1
      (pace_pos ..)).trans (WilsonIndependentMatchedOpeningPorts.grouped ..)
  change MassP G ℝ n (awaken Q L R.metals.O φ (normalized L R.metals.O Q b m K) m K K y o)=_
  rw [funext tile,WilsonIndependentMatchedOpeningMass.original (Visits R d D φ x y loc) d rows paid]
  exact Finset.sum_congr rfl fun z _=>assigned R W (fun _=>false) d D cut c φ x y loc (fun _=>1) d z

theorem passage (b:Herit Q)(φ:Wilt Q)(m K h:ℕ)(early:h ≤ m)(pre:m ≤ K)(y:ℝ)(o:CellR):
    stopped L R.metals.O Q φ b m K K h y o=cruises L R.metals.O K (capP Q) K h
      (Ashore Q L R.metals.O φ (normalized L R.metals.O Q b m K) m K K y o):=by
  change cruises _ _ _ _ _ _ (cruises _ _ _ _ _ _ _)=_
  rw [←cruisesMore _ _ _ early pre]
end YM.Integration.WilsonIndependentSpoutNormalizedMaster
end
