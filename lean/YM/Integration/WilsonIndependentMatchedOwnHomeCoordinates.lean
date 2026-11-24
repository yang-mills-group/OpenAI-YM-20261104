import YM.Integration.WilsonPositionProgramTrialReverseLens

/-! A change of reporting date on one given vacuum keeps the entire entering
tile.  The chart at each date is that vacuum's actual compensated chart. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeCoordinates
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonPositionProgramTrialReverseLens (received)
open scoped BigOperators Classical
variable {G:Gauge}{H:Hol G}{e:ℕ}{U W:Credit}

theorem concat (A:Levels G)(O:ChartRatio G)(Q:SealR G)(N t m:ℕ)(entry:t ≤ m)(k:ℕ)(x:Q.Rider):
    street A O Q.ans Q.path N t ((m-t)+k) x=
      street A O Q.ans Q.path N t (m-t) (street A O Q.ans Q.path N m k x):=by
  induction k generalizing x with
  | zero=>rw [Nat.add_zero,street_nil]
  | succ k ih=>
    rw [←Nat.add_assoc,←Street_steal,←Street_steal (m:=m) (i:=k),
        show t+(m-t+k)=m+k from by omega]
    exact ih _

def brought (A:Levels G)(O:ChartRatio G)(Q:SealR G)(N t m:ℕ)(b:Q.Rider):Q.Rider:=
  ticket A O Q N t m (PermuteLens A O Q N m b)

theorem original (Q:SealR G)(T:Theatre H Q.ans Q.path e U W)(N K t m:ℕ)
    (awake:T.V.anchor ≤ t)(first:t ≤ m)(second:m ≤ K)(cap:K ≤ N)(b:Q.Rider):
    let A:=T.V.draws
    let O:=T.V.paid
    let z:=brought A O Q N t m b
    received A O Q t K N z=received A O Q m K N b ∧
    centralL A O N t K Q (PermuteLens A O Q N t z)=centralL A O N m K Q (PermuteLens A O Q N m b):=by
  intro A O z
  let tile:=received A O Q m K N b
  have own:ticket A O Q N t K tile=z:=by
    change WilsonPositionProgramTrialFittedLens.matrix _
      (street _ _ _ _ _ _ _ _)=WilsonPositionProgramTrialFittedLens.matrix _ _
    congr 1
    rw [show K-t=m-t+(K-m) from by omega,concat A O Q N t m first]
    exact congrArg _ (Street_up T _ (awake.trans first) (by omega: m+(K-m) ≤ N))
  have same:=WilsonPositionProgramTrialFittedLens.original H Q T awake (first.trans second) cap tile
  have exactTile:received A O Q t K N (ticket A O Q N t K tile)=tile:=same.2.1
  have exactWord:centralL A O N t K Q (PermuteLens A O Q N t (ticket A O Q N t K tile))=
      Shrine (Peaks A O Q.ans Q.path N K) tile:=same.2.2
  rw [own] at exactTile exactWord
  exact ⟨exactTile,exactWord⟩
end YM.Integration.WilsonIndependentMatchedOwnHomeCoordinates
end
