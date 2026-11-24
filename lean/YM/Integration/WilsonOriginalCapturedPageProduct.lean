import YM.Integration.WilsonOriginalLinkedAngularPage
import YM.Integration.WilsonOriginalRelativePageTail

/-! The ordinary deposited AB times C is evaluated on the same chosen copy.
Both the zero and positive angular coefficients enter its finite Wick/reversion sum. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalCapturedPageProduct
open Lattice Finset WilsonOriginalOccupiedAngularPage WilsonOriginalLinkedAngularPage
open scoped BigOperators Classical

private theorem term (a b c d:ℂ):‖a*b-c*d‖ ≤ ‖a-c‖*‖b‖+‖c‖*‖b-d‖:=calc
  _ = ‖(a-c)*b+c*(b-d)‖ :=by congr 1;ring
  _ ≤ _ :=by simpa only [norm_mul] using norm_add_le ((a-c)*b) (c*(b-d))

private theorem sums {X Y:Type*} [Fintype X] [Fintype Y] (f:X→ℝ) (g:Y→ℝ) :
    (∑x,∑y,f x*g y)=(∑x,f x)*(∑y,g y):=by simp_rw [←mul_sum];rw [←sum_mul]

private theorem nn {T:Type*} [Fintype T] (m:T→ℝ)(u:T→ℂ)(pos:∀t,0 ≤ m t):0 ≤ ∑t,m t*‖u t‖:=
  sum_nonneg fun t _=>mul_nonneg (pos t) (norm_nonneg _)

private theorem bill {X Y:Type*} [Fintype X] [Fintype Y]
    (a c:X→ℂ) (b d:Y→ℂ) (l:X→ℝ) (r:Y→ℝ) (combined:X→Y→ℝ)
    {ρ D A B E F:ℝ} (ρpos:0 ≤ ρ) (splice:∀x y,combined x y ≤ l x+r y+D)
    (ab:(∑x,Real.exp (ρ*l x)*‖a x-c x‖) ≤ E) (cp:(∑y,Real.exp (ρ*r y)*‖b y-d y‖) ≤ F)
    (first:(∑x,Real.exp (ρ*l x)*‖c x‖) ≤ A) (second:(∑y,Real.exp (ρ*r y)*‖b y‖) ≤ B):
    (∑x,∑y,Real.exp (ρ*combined x y)*‖a x*b y-c x*d y‖) ≤ Real.exp (ρ*D)*(E*B+A*F):=by
  let h:=Real.exp (ρ*D)
  let w (x:X):=Real.exp (ρ*l x)
  let z (y:Y):=Real.exp (ρ*r y)
  have bound (x:X) (y:Y):Real.exp (ρ*combined x y) ≤ h*(w x*z y):=by
    dsimp only [h,w,z]
    rw [←Real.exp_add,←Real.exp_add,Real.exp_le_exp]
    linarith only [mul_le_mul_of_nonneg_left (splice x y) ρpos]
  have at_one (x:X) (y:Y):
      Real.exp (ρ*combined x y)*‖a x*b y-c x*d y‖ ≤
      h*((w x*‖a x-c x‖)*(z y*‖b y‖)+(w x*‖c x‖)*(z y*‖b y-d y‖)):=calc
    _ ≤ (h*(w x*z y))*(‖a x-c x‖*‖b y‖+‖c x‖*‖b y-d y‖):=
      mul_le_mul (bound x y) (term ..) (norm_nonneg _) (by dsimp [h,w,z];positivity)
    _ = _ :=by ring
  calc
    _ ≤ ∑x,∑y,h*((w x*‖a x-c x‖)*(z y*‖b y‖)+(w x*‖c x‖)*(z y*‖b y-d y‖)):=
      sum_le_sum fun x _=>sum_le_sum fun y _=>at_one x y
    _ = h*((∑x,w x*‖a x-c x‖)*(∑y,z y*‖b y‖)+(∑x,w x*‖c x‖)*(∑y,z y*‖b y-d y‖)):=by
      simp_rw [←mul_sum,sum_add_distrib]
      rw [sums,sums]
    _ ≤ _ :=by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply add_le_add
      · exact mul_le_mul ab second (nn (T:=Y) z b fun _=>(Real.exp_pos _).le)
          ((nn (T:=X) w (fun x=>a x-c x) fun _=>(Real.exp_pos _).le).trans ab)
      · exact mul_le_mul first cp (nn (T:=Y) z (fun y=>b y-d y) fun _=>(Real.exp_pos _).le)
          ((nn (T:=X) w c fun _=>(Real.exp_pos _).le).trans first)

/-- For any two retained angular ranks of the actual finite link board, including
either rank zero. Coherent here means both fields have already been placed
on the chosen physical lift before taking their product. -/
theorem original {G:Gauge}{N:Side}{i j:ℕ}
    (A C A' C':Stationary.Link G N→ℂ)
    (l:Positions N (Stationary.Loc G 1) i→ℝ) (r:Positions N (Stationary.Loc G 1) j→ℝ)
    (joined:Positions N (Stationary.Loc G 1) i→Positions N (Stationary.Loc G 1) j→ℝ)
    {ρ D e f p q:ℝ} (strip:0 ≤ ρ) (cable:∀x y,joined x y ≤ l x+r y+D)
    (pair:(∑x,Real.exp (ρ*l x)*‖coefficient i A x-coefficient i A' x‖) ≤ e)
    (arm:(∑y,Real.exp (ρ*r y)*‖coefficient j C y-coefficient j C' y‖) ≤ f)
    (paidPair:(∑x,Real.exp (ρ*l x)*‖coefficient i A' x‖) ≤ p)
    (paidArm:(∑y,Real.exp (ρ*r y)*‖coefficient j C y‖) ≤ q):
    (∑x,∑y,Real.exp (ρ*joined x y)*
      ‖coefficient i A x*coefficient j C y-coefficient i A' x*coefficient j C' y‖) ≤
        Real.exp (ρ*D)*(e*q+p*f):=
  bill _ _ _ _ l r joined strip cable pair arm paidPair paidArm

end YM.Integration.WilsonOriginalCapturedPageProduct
