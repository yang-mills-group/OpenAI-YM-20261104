import YM.Integration.WilsonIndependentMatchedFreshCompact
import YM.Integration.WilsonIndependentMatchedFreshInverseIncome

/-! Actual projection after running the fresh compact word through its finite K
vacuum.  The read here is the opal of the propagated whole source, before
any projection, normalization or independent comparison on another cutoff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedFreshWhole
open Function Filter Finset Matrix Lattice RG Wilson Precision Source Labels
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring PowerSeries
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (matrix ticket)
open WilsonIndependentMatchedFiledIncome (plate)
open scoped BigOperators Classical
variable {G:Gauge}{e k:ℕ}
local notation "CC" => Credit.leanC

def projected (L:Levels G)(O:ChartRatio G)(Q:SealR G)(m K k:ℕ)(X:TowerS G Q.D):Q.Rider :=
  matrix (Wray L O Q.ans Q.path K m) (opal Q.F (spools L O K k Q.h m (K-m) X))

theorem returned (H:Hol G)(Q:SealR G){U V:Credit}(T:Theatre H Q.ans Q.path e U V)(m K:ℕ)
    (entered:T.V.anchor ≤ m)(before:m ≤ K)(capacity:Q.h ≤ k)(b:Q.Rider):
    let L:=T.V.draws
    let O:=T.V.paid
    projected L O Q m K k (Shrine (plate Q.ans Q.path) (received L O Q m K K b))=b:=by
  intro L O
  let x:=received L O Q m K K b
  have ledger:=spooled (N:=K) (i:=K-m) T x entered capacity (by omega)
  rw [Nat.add_sub_of_le before] at ledger
  change spools L O K k Q.h m (K-m) (Shrine (Peaks L O Q.ans Q.path K K) x)=
    Shrine (T.lore K m) (street L O Q.ans Q.path K m (K-m) x) at ledger
  rw [Peak_initial] at ledger
  calc
    _ = ticket L O Q K m K x := by
      change matrix _ (opal _ (spools L O K k Q.h m (K-m) (Shrine _ x)))=_
      rw [plate,ledger,Shrine_read _ _ (production T before entered).1]
      rfl
    _ = _ := WilsonPositionProgramTrialReverseLens.field H Q T entered before le_rfl b

end YM.Integration.WilsonIndependentMatchedFreshWhole
