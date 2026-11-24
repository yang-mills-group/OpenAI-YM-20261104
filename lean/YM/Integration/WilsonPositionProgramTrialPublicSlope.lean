import YM.Integration.WilsonPositionProgramTrialFittedTangent
import YM.Integration.WilsonPositionProgramTrialReverseLens
import YM.XSpace.FPS

/-! First variation of the actual independently fitted coordinates on each
nonbare original field. Both the dressing and the submitted dose may vary. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicSlope
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonPositionProgramTrialFittedLens (ticket matrix)
open scoped BigOperators Classical
open WilsonPositionProgramTrialFittedTable (head change)
variable {G:Gauge}{h e:ℕ}{F:Frame G h}


open WilsonPositionProgramTrialReverseLens (received)

def grade (v:Verse F)(t:ℕ):Alma F→ℝ:=fun i=>coeff t (v i)

theorem kinetic (b v:Cost)(unit:constantCoeff b=1):
    constantCoeff (reel b v)=constantCoeff v ∧ coeff 1 (reel b v)=coeff 1 v:=by
  have zero:constantCoeff (b*X)=0:=by simp
  constructor
  · rw [←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply (R:=ℝ) v,reel_apply,XSpace.FPS.coeff_substituted v zero]
    simp [coeff_zero_eq_constantCoeff]
  · rw [reel_apply,XSpace.FPS.coeff_substituted v zero]
    simp [Finset.sum_range_succ,unit]

private theorem through (A:Wall F)(v:Verse F)(t:ℕ):
    grade (matrix A v) t=A *ᵥ grade v t:=by
  funext i
  simp [matrix,grade,Matrix.mulVec,dotProduct]

variable (L:Levels G)(O:ChartRatio G)(Q:SealR G)(N m K:ℕ)
theorem forward (simple:G.Simple)(law:LocalRatio O)(before:m ≤ K)(live:K ≤ N)(v:Q.Rider):
    grade (ticket L O Q N m K v) 0=change L O Q N m K 0 *ᵥ grade v 0 ∧
    grade (ticket L O Q N m K v) 1=change L O Q N m K 1 *ᵥ grade v 0+change L O Q N m K 0 *ᵥ grade v 1:=by
  let b:=relativeF L O N m (K-m)
  let M:=CurNames L O Q.ans Q.path N m (K-m) false
  let bank:=street L O Q.ans Q.path N m (K-m) v
  have clock:constantCoeff b=1:=angularF simple law (show m+(K-m) ≤ N by omega)
  have ground (j):constantCoeff (reel b (v j))=constantCoeff (v j):=(kinetic b (v j) clock).1
  have first (j):coeff 1 (reel b (v j))=coeff 1 (v j):=(kinetic b (v j) clock).2
  have base:grade bank 0=lineS M 0 *ᵥ grade v 0:=by
    funext i
    change coeff 0 (∑j,M i j*reel b (v j))=∑j,coeff 0 (M i j)*coeff 0 (v j)
    simp only [coeff_zero_eq_constantCoeff,map_sum,map_mul,ground]
  have slope:grade bank 1=lineS M 1 *ᵥ grade v 0+lineS M 0 *ᵥ grade v 1:=by
    funext i
    change coeff 1 (∑j,M i j*reel b (v j))=
      (∑j,coeff 1 (M i j)*coeff 0 (v j))+(∑j,coeff 0 (M i j)*coeff 1 (v j))
    rw [map_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [coeff_one_mul,coeff_zero_eq_constantCoeff,ground,first]
    ring
  change grade (matrix _ bank) 0=_ ∧ grade (matrix _ bank) 1=_
  rw [through,through,base,slope,Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]
  exact ⟨rfl,rfl⟩

theorem reported (H:Hol G){U V:Credit}(T:Theatre H Q.ans Q.path e U V)(entered:T.V.anchor ≤ m)
    (before:m ≤ K)(live:K ≤ N)(simple:G.Simple)(law:LocalRatio T.V.paid)(X:Q.Rider):
    let L:=T.V.draws
    let O:=T.V.paid
    let w:=received L O Q m K N X
    change L O Q N m K 0 *ᵥ grade w 0=grade X 0 ∧
    change L O Q N m K 1 *ᵥ grade w 0+change L O Q N m K 0 *ᵥ grade w 1=grade X 1:=by
  intro L O w
  have read:=forward L O Q N m K simple law before live w
  have issued:ticket L O Q N m K w=X:=WilsonPositionProgramTrialReverseLens.field H Q T entered before live X
  rw [issued] at read
  exact ⟨read.1.symm,read.2.symm⟩

end YM.Integration.WilsonPositionProgramTrialPublicSlope
end
