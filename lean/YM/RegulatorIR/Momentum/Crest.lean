import YM.RegulatorIR.Momentum.Past

/-!
Rank-two affine-null with post/moment lattices; read inherited difference
in `readsP` currency, not assuming an output projection gain. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Budget Budget.Packet Budget.Tuple Lattice Laurent Geometry Spatial Sources Oracle Oracle.Quarry RG Bloch Precision Tree PertExtension Geometry.Field Exterior Work.F08
open scoped Topology ENNReal NNReal BigOperators Classical Matrix PowerSeries
variable {X Y:Type} {G:Gauge}{v p:ℕ}{σ τ A F:ℝ}{L:Layer (Long X) (Long X)}
section basis
variable {f:Cover→ℝ} (h:∀ a:Room,∀ n:ℕ,n ≤2→ Summable fun x=> f x*dial a x ^n) (H:∀ a n,n≤2→ recital f n a=0)
include h H
lemma pays_cross (a b:Room):
 Summable (fun x=>f x*(dial a x*dial b x))∧ ∑' x,f x*(dial a x*dial b x)=0:=by
 let F(c:Room)(x):= f x * dial c x^2; let M(c:Room): Summable (F c):= h c 2 le_rfl
 have hm(c:Room):∑'x,F c x=0:=H c 2 le_rfl
 have he x:f x*(dial a x*dial b x)=(2:ℝ)⁻¹*(F (a+b) x-F a x-F b x):=by
    unfold F; rw [dial_sum];ring
 simp_rw [he]; exact ⟨(((M _).sub (M _)).sub (M b)).mul_left _,by rw [tsum_mul_left, ((M _).sub (M _)).tsum_sub (M b),(M _).tsum_sub (M _),hm,hm,hm];ring ⟩
end basis

section stamps
def solo : Cover≃ MovesR 1 where
 toFun p a:= p a.2
 invFun p i:=p (0,i)
 left_inv _:=rfl
 right_inv p:=funext (fun z=>congr_arg p (show (0,z.2)=z from Prod.ext (Subsingleton.elim ..) rfl)) -- check
lemma shape1 (i:Long X)(A:Fin 1→Regalia X)(p): charges (area i) A (solo p) 0=ask (area i+p) (A 0):= rfl

def cell (x:Long X)(a:Regalia X) (T:Packet (Long X) 2) : Cover→ℝ:= fun p=> T (Fin.cons x fun _ : Fin 1=> ask (area x+p) a)
lemma cell_eq (x:Long X)(A:Fin 1→Regalia X)(T:Packet (Long X) 2) : cell x (A 0) T= anchored x T ∘ charges (area x) A ∘ solo:=by ext1 u; apply congr_arg T; ext1 i;fin_cases i <;> rfl

lemma post_time (T:Packet (Long X) 2) (h:∀ i j (a:Room),∀ n:ℕ,n≤ 2→Summable fun v=>cell i j T v*dial a v^n)(hp:∀ i j a n,n ≤ 2→ recital (cell i j T) n a=0) : MomentsP T 3 0:=by
 intro i j n hn x
 have hv v : (anchored i T∘ charges (area i) j) (solo v)=cell i (j 0) T v:=by rw [cell_eq]; rfl
 let P:= cell i (j 0) T
 apply le_of_eq; apply enorm_eq_zero.mpr;unfold readsP; rw [← solo.tsum_eq (fun z=>_*rateP n x z)]; simp_rw [hv];change ∑' v,P v*rateP n x (solo v)=0
 interval_cases n
 · simp [rateP]; have hx:= hp i (j 0) (a:=0) 0 (by omega);simpa only [recital,pow_zero,mul_one] using hx
 · have hx t : rateP 1 x (solo t)=dial (step (x 0).2) t ^1:=by rw [dial_probe]; simp only [pow_one,rateP,mul_one];rfl
   simp_rw [hx]; exact hp i _ _ 1 (by omega)
 let a:= (x 0).2;let b:= (x 1).2; let c:ℝ:=(hop (x 0) (x 1):ℤ)
 let l(t):= P t *(dial (step a) t*dial (step b) t)
 let q (t):= P t*dial (step a) t^1
 have hL t:P t*rateP 2 x (solo t)=l t-q t*c:=by
    unfold l q a b c; rw [rateP,rateP,rateP,dial_probe,dial_probe]; simp only [Pi.sub_apply,Int.cast_sub]; change P t*((t (x 0).2:ℝ)*(((t (x 1).2:ℝ)-(hop (x 0) (x 1):ℝ))*1))=_;ring
 simp_rw [hL]; obtain ⟨he,H⟩ := pays_cross (h i (j 0)) (hp i (j 0)) (step a) (step b)
 have hx: Summable q:= h _ _ _ 1 (by omega)
 change Summable l at he; rw [he.tsum_sub (hx.mul_right c),tsum_mul_right,show ∑' x,l x=0 from H, show ∑' x,q x=0 from hp _ _ _ 1 (by omega)];ring
end stamps
section K
-- K.Pulse

def lamp (L : Layer X X): Packet X 2:= fun x=> L (x 0) (x 1)

lemma tellCrust (x:Long G.ColorIndex)(i:Regalia G.ColorIndex)(H:Precision.Bed)(p:Cover): cell x i (lamp (crust G H)) p=colorK G (FreeResolvent.hBlock H.metric) (coord x.1.2,x.2) (coord i.1,i.2) p:=by
 change colorK G _ _ _ ((area x+p)-area x)= colorK G _ _ _ p
 rw [add_sub_cancel_left];rfl
variable {B D: Precision.Bed}{l s:Clip}{α δ:ℝ}
variable (H:Hall B σ F α l)(V:Hall D τ A δ s)
include H V
lemma neighboring (G:Gauge):MomentsP (lamp (crust G B-crust G D)) 3 0:=by
 let U:= min σ τ
 let M:=colorK G (FreeResolvent.hBlock B.metric);let N:=colorK G (FreeResolvent.hBlock D.metric)
 have hc:0<U:=lt_min H.pos V.pos
 have hp:M.strip U _:= strip_mono (color_strip G (FreeResolvent.hBlock B.metric) (FreeResolvent.hBlock_width H.pos.le H.stripP.2.1) (FreeResolvent.kinPrice_nn _ _ H.paid)) (min_le_left ..) le_rfl
 have hn:N.strip U _:= strip_mono (color_strip G (FreeResolvent.hBlock D.metric) (FreeResolvent.hBlock_width V.pos.le V.stripP.2.1) (FreeResolvent.kinPrice_nn _ _ V.paid)) (min_le_right ..) le_rfl
 have he(i: Long G.ColorIndex)(j:Regalia G.ColorIndex) : cell i j (lamp (crust G B-crust G D))= (minusRows M N (coord i.1.2,i.2) (coord j.1,j.2)) :=funext fun x=> congr_arg₂ (·-·) (tellCrust i j B x) (tellCrust i j D x)
 refine post_time _ (fun i j a x hx=> by rw [he];exact inhaled (strip_minus hp hn ..) hc ..) (fun i j a x hx=>?_)
 rw [he]; change wax (minusRows M N) x a _ _=0;rw [support_sub hp hc hn]; by_cases h:i.2=j.2
 · have ht(F:Row (TypeFace 1) (TypeFace 1)): wax (colorK G F) x a (coord i.1.2,i.2) (coord j.1,j.2)=wax F x a (coord i.1.2) (coord j.1):=congr_arg (fun v=>recital v x a) (funext (fun t=> if_pos h)) -- diff syntax
   unfold M N; rw [Matrix.sub_apply,ht,ht,wax_universal x a H hx, wax_universal x a V hx, sub_self]
 simp [M,N,wax,recital,colorK,h]
end K
end YM.RegulatorIR.Momentum
