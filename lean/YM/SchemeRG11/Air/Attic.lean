import YM.SchemeRG11.Air.Helix
/-! Power budget on the difference of ordinary exterior waves and their
 nearest Team. Interior test rotation mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Air
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook
open Labels Long MvPolynomial
open scoped Classical Pointwise
variable {G:Gauge}{m n:ℕ}{T:Align.Itinerary}{R r:ℝ}{F U:Falls G}{f g:Ban G}
structure Defect(T:Itinerary)(r R:ℝ)(N:ℕ)(F U:Falls G)(x:ℤ)(f:Ban G):Prop where
 before : Local T r 0 (-x) (fun i z=> aeval (F i) (f i z))
 afterV : Local T r 0 (-x) (fun i z=> aeval (U i) (f i z))
 charge : Local T r N ((N:ℤ)-x) (fun i z=> aeval (F i) (f i z)-aeval (U i) (f i z))
 handy : Streams T (fun p=>‖p‖<2*R) (-x) (fun i z=> aeval (F i) (f i z))
namespace Defect
variable {x y:ℤ}
lemma born (h: Local T r 0 (-x) (fun i z=>aeval (F i) (f i z))) (he:Local T r m ((m:ℤ)-x) (fun i z=>aeval (F i) (f i z)-aeval (U i) (f i z)))(hp:Streams T (fun p=>‖p‖<2*R) (-x) (fun i z=>aeval (F i) (f i z))) : Defect T r R m F U x f:=by
 refine ⟨h,?_,he,hp⟩; let v: Slate:=fun i z=>aeval (F i) (f i z); let b:Slate:=fun i z=>aeval (U i) (f i z)
 have hh := Long.fold he m (by positivity); rw [sub_self, sub_right_comm,sub_self,zero_sub] at hh; change Local _ _ _ _ (v-b) at hh
 change Local _ _ _ _ b; rw [←sub_sub_self v b]; exact Wall.sub h hh
lemma init1 (T:Align.Itinerary)(F U:Falls G)(N r R):Defect T r R N F U 0 1:=by
 apply born
 · simp only [Pi.one_apply,map_one]; exact Wall.const _
 · simp only [Pi.one_apply,map_one,sub_self]; exact Wall.zero
 simp only [Pi.one_apply,map_one,neg_zero]; exact Streams.const _
lemma pure_null : Defect T r R n F U x 0:=by apply born <;> simp only [Pi.zero_apply,map_zero,sub_self]; exact Wall.zero; exact Wall.zero; exact Streams.zero -- newline parser
lemma add(h:Defect T r R n F U x f)(b:Defect T r R n F U x g):Defect T r R n F U x (f+g):=by
 apply born
 · simp only [Pi.add_apply,map_add]; exact h.before.add b.before
 · simp only [Pi.add_apply,map_add, add_sub_add_comm]; exact h.charge.add b.charge
 simp only [Pi.add_apply,map_add]; exact h.handy.add b.handy
lemma scal(h:Defect T r R n F U x f){e:Slate}(k:Plain T (-y) e):Defect T r R n F U (y+x) (play e f):=by
 obtain ⟨a,T'⟩:=k; have he:Local T r 0 (-y) e:=a.inherit (Eventually.of_forall (fun _ _ _=> trivial))
 apply born
 · simp only [play,map_smul,smul_eq_mul]; convert he.mul h.before using 1<;> abel -- tactic grouping
 · simp only [play,map_smul,smul_eq_mul,←mul_sub]; convert he.mul h.charge using 1<;> abel
 have ht:Streams T (fun p=>‖p‖<2*R) (-y) e:=fun y w _ k q=> T' y w trivial k q
 simp only [play,map_smul,smul_eq_mul]; rw [neg_add]; exact ht.mul h.handy
lemma multiply(h:Defect T r R n F U x f)(k:Defect T r R n F U y g):Defect T r R n F U (x+y) (f*g):=by
 apply born
 · simp only [Pi.mul_apply,map_mul]; rw [neg_add]; exact h.before.mul k.before
 · let A:Slate:= fun i z=>aeval (F i) (f i z); let B:Slate:=fun i z=> aeval (U i) (f i z)
   let C:Slate:= fun i z=>aeval (F i) (g i z); let E:Slate:=fun i z=> aeval (U i) (g i z)
   simp only [Pi.mul_apply,map_mul]; change Local _ _ _ _ (A*C-B*E); rw [show A*C-B*E=(A-B)*C+B*(C-E) from by ring]; apply Wall.add
   · have he : Local T r (n:ℤ) ((n:ℤ)-x) (A-B):=h.charge; have hk : Local T r 0 (-y) C:=k.before; convert he.mul hk using 1<;>abel
   have he : Local T r 0 (-x) B:=h.afterV; have hk : Local T r (n:ℤ) ((n:ℤ)-y) (C-E):= k.charge; convert he.mul hk using 1 <;> abel
 simp only [Pi.mul_apply,map_mul,neg_add]; apply h.handy.mul k.handy
lemma scale (h:Defect T r R n F U x f)(c:ℝ):Defect T r R n F U x (fun i p=> c • f i p):=by
 have H:= h.scal (y:=0) (show Plain T (-0) _ from (show -(0:ℤ)=0 from neg_zero) ▸ Plain.const c); rw [zero_add] at H; exact H
end Defect
end YM.SchemeRG11.Air
