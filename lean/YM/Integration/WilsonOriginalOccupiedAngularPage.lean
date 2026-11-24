import YM.Integration.WilsonOriginalConnectedPeriodPage

/-! The angular coefficient of a connected deposited face, with its original
centre, stencil indices and ordered positive-rank argument. The two rosters
can use different enumerations and different chosen representatives. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalOccupiedAngularPage
open Lattice Function Finset Further.PhysicalPeriodLimitF933 Macrame
open FVA1Physical TwoReset WilsonOriginalConnectedPeriodPage
open scoped BigOperators
variable {n N:Side} {α:Type*} {r:ℕ}
abbrev Positions (N:Side) (α:Type*) (r:ℕ) := Fin r→Site N×α

def shift (a:Site N) : Positions N α r≃Positions N α r where
  toFun x i:=(a+(x i).1,(x i).2)
  invFun x i:=((x i).1-a,(x i).2)
  left_inv x:=by funext i;apply Prod.ext <;> simp
  right_inv x:=by funext i;apply Prod.ext <;> simp

def roster (h:n.val∣N.val) (root:Site N) (k:Positions N α r→ℂ) (x:Positions N α r):ℂ:=
  ∑i:Fin (Pages n N),k (shift ((page h (splitter h root) i).val-root) x)

theorem current (h:n.val∣N.val) (root:Site N) (k:Positions N α r→ℂ) (x:Positions N α r) :
    roster h root k x=∑c:Deck h,k (shift c.val x):=by
  unfold roster
  have count:=WilsonOriginalConnectedPeriodPage.pages h root (fun v=>k (shift (v-root) x))
  simpa only [add_sub_cancel_right] using count

private theorem income {X:Type*} [Fintype X] (issued scheduled:X→ℂ) (span:X→ℝ)
    {ρ spent fare:ℝ} (paid:(∑x,Real.exp (ρ*span x)*‖issued x‖) ≤ spent)
    (earned:(∑x,Real.exp (ρ*span x)*‖scheduled x‖) ≤ fare) :
    (∑x,Real.exp (ρ*span x)*‖issued x-scheduled x‖) ≤ spent+fare:=calc
  _ ≤ ∑x,(Real.exp (ρ*span x)*‖issued x‖+Real.exp (ρ*span x)*‖scheduled x‖):=by
    apply sum_le_sum;intro x _;rw [←mul_add]
    exact mul_le_mul_of_nonneg_left (norm_sub_le ..) (Real.exp_pos _).le
  _ ≤ _ :=by rw [sum_add_distrib];exact add_le_add paid earned

private theorem cancel (h:n.val∣N.val) (left right:Site N) (issued scheduled:Positions N α r→ℂ)
    (binding:∀x,roster h left issued x=roster h right scheduled x) (x:Positions N α r) :
    (∑c:Deck h,(issued (shift c.val x)-scheduled (shift c.val x)))=0:=by
  rw [sum_sub_distrib,sub_eq_zero]
  exact (current h left issued x).symm.trans ((binding x).trans (current h right scheduled x))

theorem compared [Fintype α] (h:n.val∣N.val) (left right root:Site N) (j:Fin r)
    (issued scheduled:Positions N α r→ℂ) (span:Positions N α r→ℝ)
    {D ρ spent fare:ℝ} (reach:∀x,(separation root (x j).1:ℝ) ≤ span x+D)
    (cable:D ≤ (n.val:ℝ)/8) (strip:0 ≤ ρ)
    (binding:∀x,roster h left issued x=roster h right scheduled x)
    (paid:(∑x,Real.exp (ρ*span x)*‖issued x‖) ≤ spent)
    (earned:(∑x,Real.exp (ρ*span x)*‖scheduled x‖) ≤ fare) :
    (∑x,Real.exp (ρ*span x/2)*‖issued x-scheduled x‖) ≤ 2*Real.exp (-(ρ*n.val)/8)*(spent+fare):=by
  let roll (c:Deck h):Positions N α r≃Positions N α r:=shift c.val
  have home (x:Positions N α r):roll 0 x=x:=by
    funext i
    change ((0:Site N)+(x i).1,(x i).2)=x i
    rw [zero_add]
  exact WilsonOriginalConnectedPeriodPage.original (X:=Positions N α r) h root (fun x=>(x j).1) roll home (fun _ _=>rfl)
    (fun x=>issued x-scheduled x) span reach cable strip (cancel h left right issued scheduled binding)
    (income issued scheduled span paid earned)

end YM.Integration.WilsonOriginalOccupiedAngularPage
