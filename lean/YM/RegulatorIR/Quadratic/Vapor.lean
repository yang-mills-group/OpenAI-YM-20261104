import YM.RegulatorIR.Step.Grid

/-!
# Square completion after folding – matrix transport

Oriented tensor on each independent orbit. Finite orbit map respects
pointwise convolution whenever per-row absolute bills etc. No nondecaying
sum-of-repeat used. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Quadratic
open Lattice Function Budget Motion Budget.Layer Budget.Packet Budget.Deck Step Diagram
open scoped ENNReal NNReal BigOperators Classical Topology Matrix
variable {W X I J Z V: Type} {P:ℝ}
variable {A:Deck P W X}{B:Deck P I J}{C:Deck P Z V}

-- flat cap; exists uniformly over positions not regulator family. arithmetic transport

def Billed (t:Layer W X):Prop:=∃ c≠(⊤:ℝ≥0∞),∀ i,quota (t i) 1 ≤ c
def lap (L:Layer W I)(F:Layer I Z): Layer W Z:=fun w z=>∑'i,L w i*F i z
def ID (W:Type):Layer W W:=fun x y=>if x=y then 1 else 0
lemma id_ren (x:W) : quota (ID W x) 1=1:=by
 rw [quota_base,tsum_eq_single x]; simp [ID]; intro i hh; simp [ID,hh.symm]
lemma billed_id : Billed (ID W):=⟨1,ENNReal.one_ne_top,fun x=> (id_ren x).le⟩
lemma billed_supp {F:Layer W I}{q:Tariff Z}{x:W→Z}{y:I→Z}{w:ℝ≥0∞}(h:row F q x y w)(hh:w≠⊤):Billed F:=⟨w, hh,fun i=>le_trans (quota_mono (F i) (fun _=>q.unit ..)) (h i)⟩
namespace Billed
variable {F G:Layer W I}
lemma rows (h:Billed F)(w:W) : quota (F w) 1≠⊤:= let ⟨_,hh,hc⟩:=h; ne_top_of_le_ne_top hh (hc w)
lemma paints (h:Billed F) (A:Deck P W X)(B:Deck P I J)(w:W): Summable (paint A B F w):=by
 apply quota_summable (w:=1) (fun _=>le_rfl); rw [quota_eq _ (F w) 1 (fun i=> Layer.shade ..)]; exact h.rows w
lemma add (h:Billed F)(hh:Billed G):Billed (F+G):= by
 obtain ⟨c,hc,h⟩:=h; obtain ⟨b,hb,h'⟩:= hh; exact ⟨c+b,by finiteness,fun w=> (quota_add ..).trans (_root_.add_le_add (h w) (h' w))⟩
lemma neg (h:Billed F):Billed (-F):=by obtain ⟨c,hc,h⟩:=h; exact ⟨c,hc,fun w=>(quota_neg ..).trans_le (h w)⟩
lemma sub (h:Billed F)(hh:Billed G):Billed (F-G):=by rw [sub_eq_add_neg];exact h.add hh.neg
lemma smul (h:Billed F) (r:ℝ):Billed (r • F):=by obtain ⟨c,hc,h⟩:=h; exact ⟨‖r‖ₑ*c,by finiteness,fun i=>(quota_times ..).trans_le (mul_le_mul_right (h i) ‖r‖ₑ)⟩
variable {H : Layer I Z}
lemma lap_base {c:ℝ≥0∞}(h:∀ w,quota (H w) 1≤c)(w:W) : quota (fun p:I×Z=> F w p.1* H p.1 p.2) 1 ≤ quota (F w) 1*c:=by
 rw [show 1=(fun _:I×Z=> (1:ℝ≥0∞)) from rfl]
 rw [show quota _ _= _ from quota_prod (fun i v=>F w i*H i v) (fun _ _=>1)]
 simp_rw [quota_times,quota_base,← ENNReal.tsum_mul_right]
 apply ENNReal.tsum_le_tsum; intro b; exact mul_le_mul_right (h b) _
lemma lap (h:Billed F)(hh:Billed H) : Billed (lap F H):= by
 obtain ⟨c,hc,h⟩:=h; obtain ⟨b,hb,hb'⟩:=hh
 refine ⟨c*b,by finiteness,?_⟩
 intro w; have hx:= (lap_base (F:=F) hb' w).trans (mul_le_mul_left (h w) b)
 apply le_trans ?_ hx
 rw [quota_base,quota_base, ENNReal.tsum_prod (f:=fun i z=> ‖F w i * H i z‖ₑ)]; rw [ENNReal.tsum_comm]; exact ENNReal.tsum_le_tsum fun _=>enorm_tsum_le_tsum_enorm
end Billed

-- finite folded matrices act ordinarily on all real arrays
variable (A B C)
def fmat (L:Layer W I):Matrix X J ℝ:= wrapL A B L
lemma fmat_add {F G:Layer W I}(h:Billed F)(hh:Billed G): fmat A B (F+G)=fmat A B F+fmat A B G:=by
 ext i j; change Stalk.collect B.orbit _ j=_+_; let u:=A.place i;let U (T:Layer W I):=fun v:Stalk B.orbit j=> paint A B T u v.val
 change (∑'v,U (F+G) v)= _; rw [show U (F+G)=U F+U G from funext (fun v => by simp [U,paint,add_mul])]; refine ((?_ : Summable (U F)).hasSum.add (?_ : Summable (U G)).hasSum).tsum_eq
 · exact (h.paints A B u).comp_injective Subtype.val_injective
 exact (hh.paints A B u).comp_injective Subtype.val_injective
lemma fmat_neg (F:Layer W I): fmat A B (-F)= -fmat A B F:=by ext i j; change (∑'v:Stalk B.orbit j, _)= -_; simp only [paint,Pi.neg_apply,neg_mul,tsum_neg]; rfl
lemma fmat_sub {F G:Layer W I}(h:Billed F)(hh:Billed G): fmat A B (F-G)= fmat A B F-fmat A B G:=by rw [sub_eq_add_neg,sub_eq_add_neg,fmat_add A B h hh.neg,fmat_neg]
lemma fmat_scale (F:Layer W I) (r:ℝ):fmat A B (r • F)=r • fmat A B F:=by
 ext1 i j;change (∑'v:Stalk B.orbit j, _)=r*_; simp only [paint, Pi.smul_apply, smul_eq_mul,mul_assoc,tsum_mul_left]; rfl
lemma fmat_id [DecidableEq X] : fmat A A (ID W)=1:=by
 ext i j; rw [Matrix.one_apply]; let f(v:Stalk A.orbit j):= paint A A (ID W) (A.place i) v.val; change (∑'v,f v)= _
 by_cases h:i=j
 · subst j; rw [if_pos rfl,tsum_eq_single (⟨A.place i,A.placed i⟩:Stalk A.orbit i)]; simp [f,paint,ID,A.north]; intro v hp; simp [f,paint,ID,show A.place i≠v.val from fun h=>hp (Subtype.ext h.symm)]
 rw [if_neg h]; have ht (v:Stalk A.orbit j) : f v=0:= by
   have hx : A.place i≠ v.val:= by intro hh; apply h; rw [← A.placed i]; rw [hh,v.property]
   simp [f,paint,ID,hx]
 simp [ht]
lemma fmat_trans (F:Layer W I)(h:Sym A B F): fmat B A (Function.swap F)=(fmat A B F).transpose:= by ext1 i j; exact (other A B F h j i).symm
lemma fmat_sym {F:Layer W W}(h:Sym A A F)(hh:Function.swap F=F): (fmat A A F).transpose=fmat A A F:=by rw [← fmat_trans A A F h,hh]

variable [Fintype J]
lemma fmat_mul {F:Layer W I} {H:Layer I Z}(h:Billed F)(hh:Billed H)(he: Sym B C H): fmat A C (lap F H)=fmat A B F*fmat B C H:=by
 ext1 i j; rw [Matrix.mul_apply]; let w:=A.place i
 let t:=paint A B F w;let m:=paint A C (lap F H) w;let K:=paint B C H
 let u: I→ℝ:= fun b=> t b*fmat B C H (B.orbit b) j
 let v:=fun b (c:Stalk C.orbit j)=> t b*K b c.val
 have hz:Summable (fun p:I×Stalk C.orbit j=> v p.1 p.2):=by
    apply quota_summable (w:=1) (fun _=>le_rfl); obtain ⟨c,hc,h'⟩:=hh
    let s:I×Stalk C.orbit j → I×Z:=fun p=>(p.1,p.2.val)
    let f(x:I×Z):=F w x.1 * H x.1 x.2
    rw [quota_eq _ (f ∘ s) 1 (fun p=>by unfold v t K f s; rw [enorm_mul, Function.comp_apply,enorm_mul, Layer.shade, Layer.shade])]; exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (h.rows w) hc) ((quota_restrict s (fun _ _ e=>Prod.ext (congr_arg (Prod.fst : I×Z → I) e) (Subtype.ext (congr_arg (Prod.snd : I×Z → Z) e))) f 1).trans (Billed.lap_base h' w))
 have hU b : u b=∑'c,v b c:=by
    unfold u; rw [fmat,← from_proj B C H he,forwardCost,Stalk.collect, ← tsum_mul_left]
 have hT (x:J): fmat A B F i x*fmat B C H x j= Stalk.collect B.orbit u x:=by
    unfold Stalk.collect; simp_rw [u,show ∀ c:Stalk B.orbit x,B.orbit c.val=x from fun v=>v.property]; rw [tsum_mul_right];rfl
 have hV (z: Stalk C.orbit j) : m z.val=∑'b,v b z:=by
    unfold m paint lap v; rw [← tsum_mul_right];apply tsum_congr;intro b;unfold t K paint; generalize A.orient w=r; generalize C.orient z.val=s; calc
      _ = _*(B.orient b * B.orient b):= (show _= F w b * H b z.val * (r*s)*(B.orient b * B.orient b) by rw [B.sign_sq, mul_one])
      _ = _:=by ring
 change (∑'z:Stalk C.orbit j,m z.val)= _; rw [← tsum_fintype (L:=SummationFilter.unconditional _)]; simp_rw [hT, hV]; rw [Stalk.collected_sum]
 · simp_rw [hU]; exact hz.tsum_comm
 rw [show u= _ from funext hU]; exact hz.prod
end YM.RegulatorIR.Quadratic
