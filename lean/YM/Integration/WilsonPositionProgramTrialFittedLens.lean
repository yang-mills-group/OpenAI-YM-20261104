import YM.Integration.WilsonPositionProgramNormalizedMaster
import YM.Integration.WilsonPositionProgramBlockedTrialBirth

/-! A finite received raw vector is converted into the independent
normalized reporting coordinates by the actual chart at its own dates. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialFittedLens
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Carp
open scoped BigOperators Classical
variable {G:Gauge}{l D e:ℕ}{F:Frame G l}

def matrix (M:Wall F)(v:Verse F):Verse F:=fun i=>∑j,M i j • v j

theorem compose (A B:Wall F)(v:Verse F):matrix A (matrix B v)=matrix (A*B) v:=by
  funext i
  simp only [matrix,Finset.smul_sum,smul_smul,Matrix.mul_apply,Finset.sum_smul]
  exact Finset.sum_comm

theorem cancel (A:Wall F)(v:Verse F)(unit:IsUnit A.det):matrix A⁻¹ (matrix A v)=v:=by
  rw [compose,Matrix.nonsing_inv_mul _ unit]
  funext i;simp [matrix,Matrix.one_apply]

def ticket (A:Levels G)(Ñ:ChartRatio G)(Q:SealR G)(N m K:ℕ)(v:Q.Rider):Q.Rider:=
  matrix (Wray A Ñ Q.ans Q.path N m) (street A Ñ Q.ans Q.path N m (K-m) v)

theorem original (H:Hol G)(Q:SealR G){U W:Credit}(T:Theatre H Q.ans Q.path e U W)
    {m K N:ℕ}(entered:T.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)(v:Q.Rider):
    let A:=T.V.draws
    let O:=T.V.paid
    let x:=ticket A O Q N m K v
    (PermuteLens A O Q N m x=street A O Q.ans Q.path N m (K-m) v) ∧
    (steep A O Q.ans Q.path N m (K-m) (PermuteLens A O Q N m x)=v) ∧
    centralL A O N m K Q (PermuteLens A O Q N m x)=Shrine (Peaks A O Q.ans Q.path N K) v:=by
  intro A O x
  have unit:IsUnit (Wray A O Q.ans Q.path N m).det:=wick_unit _ (production T (before.trans live) entered).1 _ _
  have real:PermuteLens A O Q N m x=street A O Q.ans Q.path N m (K-m) v:=cancel _ _ unit
  have bound:m+(K-m) ≤ N:=by omega
  have earned:steep A O Q.ans Q.path N m (K-m) (PermuteLens A O Q N m x)=v:=by
    rw [real]
    apply street_up T entered bound
    exact Street_up T _ entered bound
  exact ⟨real,earned,by change Shrine _ (steep _ _ _ _ _ _ _ _)=_;rw [earned]⟩

end YM.Integration.WilsonPositionProgramTrialFittedLens
