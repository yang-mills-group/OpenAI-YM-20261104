import YM.Integration.WilsonPositionProgramTrialFittedTable

/-! The true weight-h signed heads of the finite chart and its remaining lower readings. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialFittedHead
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonPositionProgramTrialFittedTable (head)
open scoped BigOperators Classical
variable {G:Gauge}{e:ℕ}(H:Hol G)(Q:SealR G){U W:Credit}(book:Theatre H Q.ans Q.path e U W)
variable {m K N:ℕ}(entered:book.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)
local notation "A" => book.V.draws
local notation "O" => book.V.paid
include entered before live

theorem filed (x:Alma Q.F→ℝ)(i:Alma Q.F):
    let z:=Wray A O Q.ans Q.path N K *ᵥ x
    let P:=identum (forwardW A O Q.ans Q.path N m (K-m))
    coeff 0 (ticket A O Q N m K (head x) i)-z i=
      ∑j,if Q.h=weight Q.F j then 0 else (P i j-(1:Wall Q.F) i j)*z j:=by
  intro z P
  have known:=congrFun (WilsonPositionProgramTrialFittedTable.native A O Q N m K 0 x) i
  rw [WilsonPositionProgramTrialFittedTable.ground H Q book entered before live,←Matrix.mulVec_mulVec] at known
  have slope:∀j,Q.h=weight Q.F j → P i j=(1:Wall Q.F) i j:=
    (wallways book (k:=K-m) entered (by omega)).2.2.2 i
  calc
    _ = (P *ᵥ z) i-((1:Wall Q.F) *ᵥ z) i:=by rw [Matrix.one_mulVec];exact sub_left_inj.mpr known
    _ = ∑j,(P i j-(1:Wall Q.F) i j)*z j:=by simp only [Matrix.mulVec,dotProduct,sub_mul,Finset.sum_sub_distrib]
    _ = _:=by apply sum_congr rfl;intro j _;by_cases eq:Q.h=weight Q.F j <;> simp [eq,slope]

theorem original (z:Alma Q.F→ℝ)(placed:∀i,Q.h≠weight Q.F i → z i=0):
    let P:=Wray A O Q.ans Q.path N K
    let x:=P⁻¹ *ᵥ z
    (fun j=>coeff 0 (ticket A O Q N m K (head x) j))=z:=by
  intro P x
  have hu:IsUnit P.det:=wick_unit _ (production book live (entered.trans before)).1 _ _
  have restore:P *ᵥ x=z:=by change P *ᵥ (P⁻¹ *ᵥ z)=_;rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hu,Matrix.one_mulVec]
  funext i
  have lower:=filed H Q book entered before live x i
  change _-((P *ᵥ x) i)=∑j,if Q.h=weight Q.F j then 0 else _*(P *ᵥ x) j at lower
  rw [restore] at lower
  apply sub_eq_zero.mp
  rw [lower]
  apply sum_eq_zero;intro j _
  by_cases eq:Q.h=weight Q.F j <;> simp [eq,placed]

end YM.Integration.WilsonPositionProgramTrialFittedHead
