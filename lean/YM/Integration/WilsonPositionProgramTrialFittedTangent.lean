import YM.Integration.WilsonPositionProgramTrialFittedTable

/-! The original forward kinetic ratio preserves the incoming first derivative on every filmed component. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialFittedTangent
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonPositionProgramTrialFittedLens (ticket matrix)
open scoped BigOperators Classical
open WilsonPositionProgramTrialFittedTable (head change)
variable {G:Gauge}{h:ℕ}{F:Frame G h}

def ink (x y:Alma F→ℝ):Verse F:=fun i=>C (x i)+X*C (y i)

private theorem product (P b:PowerSeries ℝ)(v:ℝ)(clock:constantCoeff b=1):
    coeff 1 (P*((b*X)*C v))=coeff 0 P*v:=by
  rw [←mul_assoc P (b*X) (C v),←mul_assoc P b X,PowerSeries.coeff_mul_C,PowerSeries.coeff_succ_mul_X,
    PowerSeries.coeff_zero_eq_constantCoeff,map_mul,clock,mul_one]

theorem original (L:Levels G)(O:ChartRatio G)(Q:SealR G)(N m K:ℕ)(simple:G.Simple)(law:LocalRatio O)
    (before:m ≤ K)(live:K ≤ N)(x y:Alma Q.F→ℝ):
    (fun i=>coeff 1 (ticket L O Q N m K (ink x y) i))=
      change L O Q N m K 1 *ᵥ x+change L O Q N m K 0 *ᵥ y:=by
  let b:=relativeF L O N m (K-m)
  have clock:constantCoeff b=1:=angularF simple law (show m+(K-m)≤N by omega)
  let M:=CurNames L O Q.ans Q.path N m (K-m) false
  let tmp:=street L O Q.ans Q.path N m (K-m) (ink x y)
  have filed:(fun i=>coeff 1 (tmp i))=lineS M 1 *ᵥ x+lineS M 0 *ᵥ y:=by
    funext i
    simp only [tmp,street,Matrix.mulVec,dotProduct,music,ink,map_add,map_mul,reel_C,reel_X,mul_add,
      Finset.sum_add_distrib,map_sum,Pi.add_apply,lineS,Matrix.of_apply]
    change (∑j,coeff 1 (M i j*C (x j)))+(∑j,coeff 1 (M i j*((b*X)*C (y j))))=_
    simp only [PowerSeries.coeff_mul_C,product _ _ _ clock]
  calc
    _=Wray L O Q.ans Q.path N m *ᵥ fun i=>coeff 1 (tmp i):=by
      funext i;simp [ticket,matrix,tmp,Matrix.mulVec,dotProduct]
    _=_:=by rw [filed,Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec];rfl

end YM.Integration.WilsonPositionProgramTrialFittedTangent
