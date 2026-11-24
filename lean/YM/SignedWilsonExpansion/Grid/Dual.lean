import YM.SignedWilsonExpansion.Heter
namespace YM.SignedWilsonExpansion.Overlap.JetD
/-! a tiny real 2-parameter bid, with the actual mixed derivative not 2!. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter Heter
open scoped Classical Topology ContDiff
local notation "S" => (ℝ × ℝ)
abbrev F := S → ℝ
abbrev Clean (f:F) := ContDiff ℝ ∞ f
structure Slip where
   root : ℝ
   dx : ℝ
   dy : ℝ
   cost : ℝ
   deriving Inhabited
lemma down {f:F} (hp:Clean f) (x:ℝ): ContDiff ℝ ∞ (fun y:ℝ=> f (x,y)):= hp.comp (contDiff_const.prodMk contDiff_id)
lemma across {f:F} (hp:Clean f) : ContDiff ℝ ∞ (fun x:ℝ=> f (x, (0:ℝ))):= hp.comp (contDiff_id.prodMk contDiff_const)
structure Worth (f:F)(s:Slip) : Prop where
   clean : Clean f
   exist : f 0=s.root
   arrive : deriv (fun x:ℝ=> f (x,0)) 0=s.dx
   depart : dY f 0=s.dy
   taxes : tooth f=s.cost
namespace Slip
variable (f g:Slip)(h:ℝ→ℝ)(q:ℝ)
def tied : Slip:= ⟨f.root+g.root, f.dx+g.dx, f.dy+g.dy, f.cost+g.cost⟩
def both : Slip:= ⟨ f.root*g.root, f.dx*g.root+f.root*g.dx,f.dy*g.root+f.root*g.dy, f.cost*g.root + f.dx*g.dy+f.dy*g.dx+ f.root*g.cost ⟩
def negS : Slip:= ⟨ -f.root,-f.dx,-f.dy,-f.cost ⟩
def roof : Slip:= ⟨ h f.root, deriv h f.root*f.dx, deriv h f.root*f.dy,
    deriv (deriv h) f.root*f.dx*f.dy + deriv h f.root*f.cost ⟩
def constant : Slip:= ⟨q,0,0,0⟩
def fst : Slip:= ⟨0,1,0,0⟩
def snd : Slip:= ⟨0,0,1,0⟩
end Slip
namespace Worth
variable {f g:F} {s z:Slip}{q:ℝ}
lemma add (u:Worth f s)(v:Worth g z): Worth (fun x=>f x+g x) (Slip.tied s z) := by
    refine ⟨u.clean.add v.clean,?_ ,?_ ,?_ ,?_ ⟩
    · rw [u.exist,v.exist]; rfl
    · have A:= ( across u.clean ).differentiable (by simp) 0; have B:= ( across v.clean ).differentiable (by simp) 0; change deriv (fun x:ℝ=>f (x,0)+g (x,0) ) 0 = s.dx+z.dx; rw [ deriv_fun_add A B,u.arrive,v.arrive ]
    · have A:= ( down u.clean 0 ).differentiable (by simp) 0; have B:= ( down v.clean 0 ).differentiable (by simp) 0; unfold dY; change deriv (fun y:ℝ=>f (0,y)+g (0,y) ) 0 = s.dy+z.dy; rw [ deriv_fun_add A B ]; change dY f 0+dY g 0=_; rw [u.depart,v.depart]
    rw [tooth_add u.clean v.clean,u.taxes,v.taxes]; rfl
lemma neg (u:Worth f s): Worth (fun x=>-f x) s.negS := by
    have ht(x:ℝ): dY (fun x=>-f x) x= -dY f x:= deriv.fun_neg
    refine ⟨u.clean.neg,?_ ,?_ ,?_ ,?_ ⟩
    · rw [u.exist]; rfl
    · rw [deriv.fun_neg, u.arrive]; rfl
    · rw [ht, u.depart]; rfl
    · rw [ tooth, funext ht, deriv.fun_neg ]; change -tooth f= -_; rw [u.taxes]
lemma sub (u:Worth f s)(v:Worth g z): Worth (fun x=>f x-g x) ( Slip.tied s z.negS ) := by simpa only [sub_eq_add_neg] using u.add v.neg
lemma mul (u:Worth f s)(v:Worth g z): Worth (fun x=>f x*g x) ( Slip.both s z ) := by
    have A:= ( across u.clean ).differentiable (by simp) 0; have B:= ( across v.clean ).differentiable (by simp) 0
    have U : f (0,0)=s.root:= u.exist; have V : g (0,0)=z.root:= v.exist
    have Q(x:ℝ): dY (fun x=>f x*g x) x=dY f x*g (x,0)+f (x,0)*dY g x:= deriv_fun_mul (c:=fun y=>f (x,y)) (( down u.clean x ).differentiable (by simp) 0) (( down v.clean x ).differentiable (by simp) 0)
    refine ⟨ u.clean.mul v.clean,?_ ,?_ ,?_ ,?_ ⟩
    · rw [u.exist,v.exist]; rfl
    · rw [deriv_fun_mul A B]; rw [U,V,u.arrive,v.arrive]; rfl
    · rw [Q,U,V,u.depart,v.depart]; rfl
    have C:= (Heter.dY_s u.clean).differentiable (by simp) 0; have D:= (Heter.dY_s v.clean).differentiable (by simp) 0
    rw [tooth, funext Q, deriv_fun_add (f:=fun x=>dY f x*g (x,0)) (g:=fun x=>f (x,0)*dY g x) (C.fun_mul B) (A.fun_mul D) ]; rw [deriv_fun_mul C B, deriv_fun_mul A D]; change tooth f * g (0,0) + dY f 0* deriv _ _+ (deriv _ _* dY g 0 + f (0,0)*tooth g)= _; rw [U,V,u.depart,v.depart,u.arrive,v.arrive,u.taxes,v.taxes]; unfold Slip.both; abel
lemma layer (u:Worth f s) {h:ℝ→ℝ} (v:ContDiff ℝ ∞ h) : Worth (fun x=> h (f x)) ( s.roof h ) := by
    have A:= ( across u.clean ).differentiable (by simp) 0
    have V : f (0,0)=s.root:=u.exist; have B:=v.differentiable (by simp)
    have W: ContDiff ℝ ∞ (deriv h):= by apply ContDiff.deriv'; simpa using v
    have Q(x:ℝ): dY (fun x=>h (f x)) x = deriv h ( f (x,0) ) * dY f x:= HasDerivAt.deriv ( ( B (f (x,0)) ).hasDerivAt.comp (h:= fun y:ℝ=> f (x,y)) (0:ℝ) (((down u.clean x).differentiable (by simp) 0).hasDerivAt) )
    refine ⟨ v.comp u.clean,?_ ,?_ ,?_ ,?_ ⟩
    · rw [u.exist]; rfl
    · refine (HasDerivAt.deriv ?_); have hp:= ( B (f (0,0)) ).hasDerivAt.comp (h:=fun x:ℝ=> f (x,0)) (0:ℝ) A.hasDerivAt; beta_reduce at hp; rw [u.arrive,V] at hp; exact hp
    · rw [Q,V,u.depart]; rfl
    have C:= W.differentiable (by simp) (f (0,0)); have H : HasDerivAt (fun x:ℝ=> deriv h ( f (x,0) )) (deriv (deriv h) (f (0,0))*deriv (fun x:ℝ=>f (x,0)) 0) 0:= C.hasDerivAt.comp (h:=fun x:ℝ=> f (x,0)) (0:ℝ) A.hasDerivAt
    rw [tooth, funext Q]; have D: HasDerivAt ( dY f ) ( tooth f ) 0:= (( Heter.dY_s u.clean ).differentiable (by simp) 0).hasDerivAt
    obtain hD:= ( H.fun_mul D ).deriv; rw [V,u.arrive,u.depart,u.taxes] at hD; exact hD
lemma c (q:ℝ): Worth (fun _=>q) (Slip.constant q):= by constructor; exact contDiff_const; rfl; simp [Slip.constant]; simp [Slip.constant,dY]; unfold tooth dY; simp [Slip.constant]
lemma x : Worth Prod.fst Slip.fst:= by constructor; exact contDiff_fst; rfl; simp [Slip.fst]; simp [Slip.fst,dY]; unfold tooth dY; simp [Slip.fst]
lemma y : Worth Prod.snd Slip.snd:= by constructor; exact contDiff_snd; rfl; simp [Slip.snd]; simp [Slip.snd,dY]; unfold tooth dY; simp [Slip.snd]
lemma square (u:Worth f s) : Worth (fun x=> f x^2) (Slip.both s s):= by simp only [pow_two]; exact u.mul u
lemma cube (u:Worth f s) : Worth (fun x=> f x^3) (Slip.both (Slip.both s s) s):= by rw [show (fun x=>f x^3)=(fun x=> f x^2*f x) from funext (fun x=>by ring) ]; exact u.square.mul u
lemma quartic (u:Worth f s): Worth (fun x=>f x^4) ( Slip.both (Slip.both s s) (Slip.both s s) ):= by rw [show (fun x=>f x^4)=(fun x=> f x^2 * f x^2) from funext (fun x=>by ring) ]; exact u.square.mul u.square
end Worth
end
end YM.SignedWilsonExpansion.Overlap.JetD
