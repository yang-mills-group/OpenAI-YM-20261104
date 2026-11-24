import YangMills.WilsonProof.NativeSupport.YM.MS.Cylinder.Variable
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! Analytic germ into *commuting* polynomial legs. When the test directions are
 zero on exterior/antifield legs this represents the physical chart. Work with derivatives
 not factorial powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder.Taylor
open Function Filter Set Finset Koszul
open scoped Topology ContDiff
variable {E X A J Z: Type*} [NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup X][NormedSpace ℝ X] [NormedAddCommGroup Z][NormedSpace ℝ Z]
variable {p:Sector A} (e:A→E) {f f':E→ℝ}
abbrev germ (f:E→Z): Prop:=ContDiffAt ℝ ω f 0
def layer (x:E)(f:E→Z)(a:E):= fderiv ℝ f a x
lemma germ_layer {f:E→Z}(h:germ f)(x:E): germ (layer x f):= (h.fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const
lemma alter (f:E→ Z)(h:germ f) (x y:E): layer x (layer y f) =ᶠ[𝓝 0] layer y (layer x f):= by
    filter_upwards [h.eventually (by simp)] with a h
    have ht:= (h.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
    have tt (p q:E) : layer p (layer q f) a = fderiv ℝ (fderiv ℝ f) a p q:= by
       change fderiv ℝ (fun a=> fderiv ℝ f a q) a p= _; rw [(ht.hasFDerivAt.clm_apply (u:=fun _=>q) (hasFDerivAt_const q a)).fderiv]; simp
    rw [tt,tt]; exact h.isSymmSndFDerivAt_of_omega x y
lemma sum_layers (x:E)(h:germ f)(h':germ f'): layer x (f+f')=ᶠ[𝓝 0] layer x f+layer x f':= by filter_upwards [h.eventually (by simp),h'.eventually (by simp)] with a h g; unfold layer; rw [fderiv_add (h.differentiableAt (by simp)) (g.differentiableAt (by simp))]; rfl
lemma mul_layers (x:E)(h:germ f)(h':germ f'): layer x (f*f')=ᶠ[𝓝 0] layer x f*f'+f*layer x f':= by
    filter_upwards [h.eventually (by simp),h'.eventually (by simp)] with a h g; unfold layer; rw [fderiv_mul (h.differentiableAt (by simp)) (g.differentiableAt (by simp))]; simp [add_comm,mul_comm]
lemma scale_layers (x:E)(h:germ f)(c:ℝ): layer x (c • f)=ᶠ[𝓝 0] c • layer x f:= by
    filter_upwards [h.eventually (by simp)] with a h; unfold layer; rw [fderiv_const_smul (h.differentiableAt (by simp))]; rfl

def ink (e:A→E)(f:E→ℝ): Raw A ℂ | []=> (f 0:ℂ) | j::l=> ink e (layer (e j) f) l
@[simp] lemma drip {f:E→ℝ}: ink e f []=(f 0:ℂ):= rfl
lemma inktip {f:E→ℝ}(i:A): D i (ink e f)= ink e (layer (e i) f):= rfl
lemma ink_const (c:ℝ): ink e (fun _=>c)=coin (c:ℂ) := by
    funext l; induction l generalizing c with
    | nil=> rfl
    | cons i l ih=> rw [D_eval i (ink _ _),inktip,show layer (e i) (fun _=>(c:ℝ)) =fun _=>0 by ext x; simp [layer], ih]; cases l <;> simp [coin]
@[simp] lemma ink_zero : ink e (0:E→ℝ)=0:= by change ink e (fun _=>0)=_; rw [ink_const e 0]; ext l; cases l <;> rfl
lemma ink_off {i:A}(hi:e i=0)(f:E→ℝ): D i (ink e f)=0:= by rw [inktip,hi,show layer 0 f=0 from funext fun x=> map_zero _,ink_zero]
lemma inkit (h:f=ᶠ[𝓝 0] f'): ink e f=ink e f':= by
    funext l; induction l generalizing f f' with
    | nil=> simp [h.eq_of_nhds]
    | cons i l ih=> simp_rw [D_eval i (ink _ _),inktip]; exact ih ((h.fderiv (𝕜:=ℝ)).mono (fun z h=> DFunLike.congr_fun h (e i)))
lemma ink_add (h:germ f)(hh:germ f') : ink e (f+f')= ink e f+ ink e f':= by
    funext l; induction l generalizing f f' with
    | nil=> simp
    | cons i l ih=> simp only [Pi.add_apply,D_eval i (ink _ _),inktip,inkit e (sum_layers (e i) h hh)]; exact ih (germ_layer h _) (germ_layer hh _)
lemma ink_smul (h:germ f)(c:ℝ): ink e (c • f)= (c:ℂ) • ink e f:= by
    funext l; induction l generalizing f with
    | nil=>simp
    | cons i l ih=> simp only [Pi.smul_apply,D_eval i (ink _ _),inktip,inkit e (scale_layers (e i) h c)]; exact ih (germ_layer h _)
lemma ink_sub (h:germ f)(hh:germ f'): ink e (f-f')= ink e f-ink e f':= by rw [sub_eq_add_neg,ink_add _ h (f':= -f') hh.neg,← neg_one_smul ℝ f',ink_smul e hh]; simp [sub_eq_add_neg]
lemma ink_sum {F:J→ E→ℝ}(s:Finset J)(h:∀ i∈s,germ (F i)): ink e (∑ i∈s,F i)=∑ i∈s, ink e (F i):= by
    classical
    induction s using Finset.induction_on with
    | empty=> simp
    | insert i s hi ih=>
       have he:=fun j hj=> h j (Finset.mem_insert_of_mem hj); rw [Finset.sum_insert hi, Finset.sum_insert hi, ink_add _ (h i (by simp)) (f':=∑ i∈s,F i) (by unfold germ; rw [show ∑ i∈s,F i=fun x=>∑ i∈s,F i x from funext fun x=> Finset.sum_apply ..]; exact ContDiffAt.sum he),ih he] -- adjust
lemma ink_uses (s:Set A)(h:∀ i,i∉s→e i=0)(f:E→ℝ): Uses s (ink e f):= by
    intro l i hi he; induction l generalizing f with
    | nil=> exact (List.not_mem_nil hi).elim
    | cons j l ih=> rcases List.mem_cons.mp hi with rfl|hj; exact congr_fun (ink_off _ (h _ he) _) l; exact ih _ hj -- order
lemma ink_s (e':∀ i,p i=true→e i=0) (h:germ f): Symm p (ink e f):= by
    intro l i j r; induction l generalizing f with
    | nil=>
       by_cases hv :(p i=true ∧ p j=true)
       · rw [ink_uses e {x|p x=false} (fun i hi=> e' i (by simpa using hi)) _ _ i (by simp) (by simp [hv.1]),ink_uses e {x|p x=false} (fun i hi=> e' i (by simpa using hi)) _ _ i (by simp) (by simp [hv.1]),mul_zero]
       simp_rw [List.nil_append,D_eval i (ink _ _), D_eval j (ink _ _),inktip]; simp_rw [D_eval i (ink e _), D_eval j (ink e _), inktip] -- inspect
       simp_rw [inkit e (alter f h (e i) (e j)),cross, Bool.and_eq_true,hv,if_false,one_mul]
    | cons j' l ih=> exact ih (germ_layer h _)
lemma ink_p (e':∀ i,p i=true→e i=0) (f:E→ℝ): Pure p false (ink e f):= by
   intro l hl; induction l generalizing f with
   | nil => contradiction
   | cons a l ih=>
       cases h:p a; swap; · exact congr_fun (ink_off _ (e' a h) _) l
       exact ih _ (by simpa [h] using hl)
lemma ink_mul (he:∀ i,p i=true→ e i=0)(h:germ f)(hh:germ f'): ink e (f*f')= product p (ink e f) (ink e f') := by
    funext l; induction l generalizing f f' with
    | nil=>simp
    | cons i l ih=> rw [D_eval i (product p _ _),D_product,D_eval i (ink e _),inktip,inktip,inktip,(ink_p e he _).signs, cross_false',one_smul,inkit e (mul_layers (e i) h hh), ink_add _ (f:=layer (e i) f*f') (f':=f*layer (e i) f') ((germ_layer h _).mul hh) (h.mul (germ_layer hh _)), Pi.add_apply,Pi.add_apply, ih (germ_layer h _) hh, ih h (germ_layer hh _)]
lemma ink_ctrl_one (F:E→L[ℝ] X) {f:X→ℝ} (h:germ f): ink e (f ∘ F)=ink (F ∘ e) f:=by
   funext l; induction l generalizing f with
   | nil=> simp
   | cons i l ih=> simp_rw [D_eval i (ink _ _),inktip]; refine (congr_fun (inkit (f':= layer (F (e i)) f ∘ F) e ?_) l).trans (ih (germ_layer h _));
                    filter_upwards [(show Tendsto F (𝓝 0) (𝓝 0) by simpa using F.continuous.tendsto 0).eventually (h.eventually (by simp))] with y hh; unfold layer; rw [fderiv_comp y (hh.differentiableAt (by simp)) F.differentiableAt,F.fderiv]; rfl
lemma tower (V:A→X)(K:E→L[ℝ] X)(hv:∀ i,K (e i)=V i)(f:X→ℝ)(h:germ f): ink e (f ∘ K)= ink V f:= by rw [ink_ctrl_one e K h, funext (show ∀ i,(K ∘ e) i=V i from hv)]
end YM.MS.Cylinder.Taylor
