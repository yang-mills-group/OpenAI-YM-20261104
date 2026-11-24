import YM.Integration.WilsonOriginalPolarizedAngularPage
import YM.Next.STATIONARY.Lift.Pathways

/-! Positive angular coefficients on the actual finite link board, evaluated with one
position, exterior component and color per slot. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalLinkedAngularPage
open Lattice Finset Further.PhysicalPeriodLimitF933 Macrame
open WilsonOriginalOccupiedAngularPage WilsonOriginalPolarizedAngularPage
open scoped BigOperators Classical
variable {G:Gauge} {n N:Side} {r:ℕ}

/-- Translation on the real finite-link chart used for both the pupil and its prescribed forest. -/
def move (G:Gauge) (a:Site N):Stationary.Link G N→L[ℝ]Stationary.Link G N:=
  LinearMap.toContinuousLinearMap {
    toFun:=fun f y=>f (y.1-a,y.2)
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl }

def ray (G:Gauge) (p:Site N×Stationary.Loc G 1):Stationary.Link G N:=
  fun b=>if b=p then 1 else 0

private theorem placed (a:Site N) (x:Site N×Stationary.Loc G 1):
    move G a (ray G x)=ray G (a+x.1,x.2):=by
  funext y
  change (if (y.1-a,y.2)=x then (1:ℝ) else 0)=(if y=(a+x.1,x.2) then 1 else 0)
  rcases y with ⟨t,c⟩
  rcases x with ⟨s,b⟩
  simp only [Prod.mk.injEq,sub_eq_iff_eq_add,add_comm s a]

abbrev coefficient (r:ℕ) (F:Stationary.Link G N→ℂ):Positions N (Stationary.Loc G 1) r→ℂ:=
  entries r (ray G) F

/-- Both connected rosters are first differentiated on the same real held field.
Every nonzero rank is returned with an exponential toll at the original physical period. -/
theorem original (h:n.val∣N.val) (root left right:Site N) (j:Fin r)
    (F Z:Stationary.Link G N→ℂ) (smooth:ContDiff ℝ r F) (model:ContDiff ℝ r Z)
    (matched:∀ A,board h left (move G) F A=board h right (move G) Z A)
    (span:Positions N (Stationary.Loc G 1) r→ℝ) {D ρ spent fare:ℝ}
    (reach:∀x,(separation root (x j).1:ℝ) ≤ span x+D)
    (cable:D ≤ (n.val:ℝ)/8) (strip:0 ≤ ρ)
    (paid:(∑x,Real.exp (ρ*span x)*‖coefficient r F x‖) ≤ spent)
    (earned:(∑x,Real.exp (ρ*span x)*‖coefficient r Z x‖) ≤ fare):
    (∑x,Real.exp (ρ*span x/2)*‖coefficient r F x-coefficient r Z x‖) ≤ 
      2*Real.exp (-(ρ*n.val)/8)*(spent+fare):=by
  apply WilsonOriginalOccupiedAngularPage.compared h left right root j _ _ span reach cable strip _ paid earned
  exact binding h left right (move G) (ray G) placed r F Z smooth model matched

end YM.Integration.WilsonOriginalLinkedAngularPage
