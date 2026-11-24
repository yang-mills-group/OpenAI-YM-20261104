import YM.Integration.WilsonPositionProgramTrialFittedLens

/-! The finite coefficient matrix on the true received group rows. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialFittedTable
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonPositionProgramTrialFittedLens (ticket matrix)
open scoped BigOperators Classical
variable {G:Gauge}{l e:ℕ}{F:Frame G l}

def head (x:Alma F→ℝ):Verse F:=fun i=>C (x i)
def change (A:Levels G)(O:ChartRatio G)(Q:SealR G)(N m K t:ℕ):Wall Q.F:=
  Wray A O Q.ans Q.path N m * lineS (CurNames A O Q.ans Q.path N m (K-m) false) t

theorem native (A:Levels G)(O:ChartRatio G)(Q:SealR G)(N m K t:ℕ)(x:Alma Q.F→ℝ):
    (fun j=>coeff t (ticket A O Q N m K (head x) j))=change A O Q N m K t *ᵥ x:=by
  have inner:(fun i=>coeff t (street A O Q.ans Q.path N m (K-m) (head x) i))=
      lineS (CurNames A O Q.ans Q.path N m (K-m) false) t *ᵥ x:=by
    funext i
    simp [street,music,head,reel_C,Matrix.mulVec,dotProduct,lineS,PowerSeries.coeff_mul_C]
  calc
    _ = Wray A O Q.ans Q.path N m *ᵥ (fun i=>coeff t (street A O Q.ans Q.path N m (K-m) (head x) i)):=by
      funext i;simp [ticket,matrix,Matrix.mulVec,dotProduct]
    _ = _ := by rw [inner,Matrix.mulVec_mulVec];rfl

theorem ground (H:Hol G)(Q:SealR G){U W:Credit}(book:Theatre H Q.ans Q.path e U W)
    {m K N:ℕ}(entered:book.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N):
    change book.V.draws book.V.paid Q N m K 0=
      identum (forwardW book.V.draws book.V.paid Q.ans Q.path N m (K-m))*
      Wray book.V.draws book.V.paid Q.ans Q.path N K:=by
  have bank:=(wallways book (k:=K-m) entered (show m+(K-m) ≤ N by omega)).1
  simpa only [change,show m+(K-m)=K by omega] using bank

end YM.Integration.WilsonPositionProgramTrialFittedTable
