import YM.Integration.WilsonMeasuredPublicEntranceJointBilled
import YM.Integration.WilsonMeasuredPublicEntranceCutoffHearing

/-! Four public corners, with the left and right source fixed before the crossing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePublicFour
open Function Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction WilsonAddressedPhysicalCells WilsonMeasuredPublicEntranceProfileRegistry
open scoped Classical BigOperators

def corner (l r:Bool):Fin 2→Bool:=![l,r]
def sign (b:Fin 2→Bool):ℂ:=if b 0=b 1 then 1 else -1

theorem sum (Z:(Fin 2→Bool)→ℂ):
    (∑b,sign b*Z b)=Z (corner false false)-Z (corner false true)-Z (corner true false)+Z (corner true true):=by
  have grid(b:Fin 2→Bool):corner (b 0) (b 1)=b:=by funext i;fin_cases i <;> rfl
  calc
    _=∑ab:Bool×Bool,(if ab.1=ab.2 then (1:ℂ) else -1)*Z (corner ab.1 ab.2):=by
      apply Fintype.sum_equiv (piFinTwoEquiv (fun _:Fin 2=>Bool))
      intro b
      change sign b*Z b=sign b*Z (corner (b 0) (b 1))
      rw [grid]
    _=_:=by simp [Fintype.sum_prod_type];ring

theorem weight:(∑b:Fin 2→Bool,‖sign b‖)=4:=by
  have one (b:Fin 2→Bool):‖sign b‖=1:=by unfold sign;split <;> simp
  simp [one]

theorem heard {k:ℕ}(φ:Test k)(a scale:ℝ)(side:Side)(D:(Fin 2→Bool)→Sites side k→ℂ)(cost:ℝ)
    (paid:Billed φ a scale side (fun t=>∑b,sign b*D b t) ((∑b,‖sign b‖)*cost)):
    Billed φ a scale side (fun t=>D (corner false false) t-D (corner false true) t-
      D (corner true false) t+D (corner true true) t) (4*cost):=by
  simpa only [sum (fun b=>D b _),weight] using paid

theorem tensor (X Y:Bool→ℂ):(∑b,sign b*(X (b 0)*Y (b 1)))=(X false-X true)*(Y false-Y true):=by
  rw [sum]
  change X false*Y false-X false*Y true-X true*Y false+X true*Y true=_
  ring

end YM.Integration.WilsonMeasuredPublicEntrancePublicFour
end
