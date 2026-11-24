import YM.MS.Lifting.Fit
import YM.MS.Tone.Basis
import YM.MS.Wilson.Dressed
/-!
# Leading free symbols of dressed stencils

Use plane normalization to achieve *symbol* jets on all rational functions of rank variables,
 strict low-mom. Propagator interactions do not affect highest rank at birth. Newton Toda.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Lifting
open Function Filter Set Finset Plane Koszul Color Real Momentum Wire Tensor Book
open Landau Detect Detect.Mark MeasureTheory
open Cylinder Lab Taylor Native Draft Paint Sew Native.Chart Orient Wilsonian Studio
open Tone Tone.Frame Lattice
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge} {F S:Dot G Cover} {v q:ℤ} {H K:Law G} {r s:ℕ} (L:PlaqAxes)
lemma tipcost (i:CI G)(p: LightMode G QP): Tone.run (tipSeed idRail L (0:Cover) i) [p] = curl L p i:= by
   let f:=bolt1 i; let T := front L; let F:Cyl (Axis×Conn G) ℂ := region.symm (Cylinder.Taylor.ink priv f)
   let S:Finset (Axis × Conn G) := Finset.univ; have hS : Uses (S:Set _) F.val:= by simp [S,Uses.entire]
   change shade paywave (Ferry (knot T) F) [p] = _; rw [study,deriv_lum (fun p x=>paywave p (knot T x)) p F hS]; apply Finset.sum_congr rfl; intro j _; congr 1; rw [shade_nil]
   let Q:= priv j; change ((layer Q f 0:ℝ):ℂ)=_; unfold layer; congr! 1
   rw [← α_at]; have hv := ((α i).hasFDerivAt.comp_hasDerivAt (f:=fun t=> G.curvature (lime Q t)) 0 (Work.F03.curvature_of_hasDerivAt (limeD Q)))
   refine HasDerivAt.unique (f:=fun t:ℝ=> f (t • Q)) ?_ hv; let h := Bare.Mix.fstep (0:Lot G Axis) Q ((curvatureArt i).differentiableAt (by simp)); simpa using h
lemma clotStart (l:List Axis)(k:CI G)(x:Cover): clot idRail L l x k= Lab.Shift x (clot idRail L l 0 k):= by rw [show Lab.Shift x (clot idRail L l 0 k)=clot idRail L l (x+0) k from clot_go idRail L (fun y:Cover=>x+y) idRail (fun i j=> (add_assoc ..).symm) _ _ _, add_zero]
lemma cash_bank (x:Cover)(a:Axis)(i j:CI G): run (bankSeed x a i j) []= if i=j then 1 else 0:= by simp [run,bankSeed,onedge,Sew.art,region,apply_ite]; change (if i=j then (wc 1 i j).re=1 else (wc 1 i j).re=0); split_ifs <;> simp [*]
lemma speed (l:List Axis)(k:CI G)(i:Branch G Axis)(q:QP)(a:Axis): run (clot idRail L (a::l) 0 k) [(i,q)]=(bill q (embed (step a))-1)*run (clot idRail L l 0 k) [(i,q)]:= by
    rw [clot,map_sub,map_sum, Pi.sub_apply,Finset.sum_apply]; simp_rw [small _ (clot idRail L l _ _) _ (show run (clot idRail L l _ _) []=0 from clot_zero ..),cash_bank]; rw [zero_add]; simp_rw [mul_ite,mul_zero,mul_one,Fintype.sum_ite_eq']; nth_rw 1 [clotStart]; rw [movement]; simp [net,sub_mul,idRail]
lemma bankForm (p q:QP): ContDiff ℝ ∞ (fun t:ℝ=> bill (t • p) q):= by unfold bill pairing; exact ContDiff.cexp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ ∞ (fun t:ℝ=> ∑ i,(t • p i)*q i) by fun_prop)))
lemma stepForm (p:QP)(i:Axis): Rest (fun t:ℝ=>bill (t • p) (embed (step i))-1) 1 (inc i p):= by
    refine Rest.one ((bankForm ..).sub contDiff_const) (by simp) ?_; unfold bill pairing; simp only [Pi.smul_apply, emb_step, mul_ite, mul_one,mul_zero,Fintype.sum_ite_eq']
    let f t := Complex.I*(↑((t:ℝ) • p i):ℂ); have he : HasDerivAt f (I*(p i:ℂ)) 0:= (((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (f:=fun t :ℝ=> t*(p i)) 0 (by simpa using (hasDerivAt_id' (0:ℝ)).mul_const (p i)))).const_mul I)
    let FR:= fun t=> Complex.exp (f t); have hf : HasDerivAt FR (inc i p) 0:= by convert he.cexp using 1; simp [inc,f]
    exact hf.sub_const _
lemma waveFormR (p:QP)(i:Axis): Rest (fun t:ℝ=> (wave (t • p) i:ℂ)) 1 (p i:ℂ):= by
    unfold wave theta; simp only [Function.comp_apply,Pi.smul_apply,smul_eq_mul]
    refine Rest.one (Complex.ofRealCLM.contDiff.comp (show ContDiff ℝ ∞ (fun t:ℝ=>theta (t*p i)) by unfold theta; fun_prop)) (by simp) ?_; refine Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (f:=fun t:ℝ=>theta (t*p i)) 0 ?_
    have h : HasDerivAt (fun t:ℝ=> t*p i) (p i) 0:= by simpa using (hasDerivAt_id' (0:ℝ)).mul_const (p i)
    convert ((h.const_mul (2:ℝ)⁻¹).sin.const_mul 2) using 1 <;> first| rfl| (norm_num; ring)

lemma recall (i:CI G)(a:Axis)(j:CI G)(p: QP): Rest (fun t:ℝ=>curl L (waveForm (t • p) a j) i) 1 ((Plaq.mk L.val.1 L.val.2 []).mark i (waveForm p a j)):= by
   simp_rw [curl_piece]; unfold Plaq.mark; simp only [waveForm,Local.BV.gpath]; by_cases h:i=j; swap; · simp only [matchA,Ne.symm h,↓reduceIte]; exact Rest.zero _
   subst j; let X:= L.val.1; let Y:=L.val.2; have hx:X≠Y:= (show X<Y from L.property).ne; have hL : Rest (fun t:ℝ=> saw L (t • p)) 0 1:= Rest.level (bankForm ..) (by simp [saw])
   have ht x := hL.mul ((waveFormR p x).smul I); unfold matchA blade; simp only [if_true,der_nil,one_mul]
   by_cases hu : a=L.val.1; · subst a; simp only [(show L.val.1≠ L.val.2 from hx),↓reduceIte,zero_sub,mul_zero, mul_one,Complex.ofReal_neg,mul_neg]; simpa only [Y,zero_add,one_mul, neg_mul,neg_one_mul] using (ht Y).smul (-1) -- actually derivative index Y
   by_cases hk : a=L.val.2; · subst a; simp only [hu,↓reduceIte,mul_zero,mul_one,sub_zero]; simpa [X] using ht X
   simp only [hu,hk,↓reduceIte,mul_zero,sub_zero,Complex.ofReal_zero]; exact Rest.zero _
open Local.BV
lemma clot_rest (l:List Axis)(k:CI G)(a: Branch G Axis)(p:QP): Rest (fun t:ℝ=> run (clot idRail L l 0 k) [(a,t • p)]) (2+l.length-wfield a) ((Plaq.mk L.val.1 L.val.2 l).mark k (a,p)):= by
   induction l with
   | nil =>
            simp_rw [clot,tipcost]
            by_cases hv:∃ i,a.1=Landau.gauge i; · obtain ⟨v,hv⟩:=hv; rcases a with ⟨a,i⟩; change a=_ at hv; subst a; exact recall L k v i p
            push Not at hv; simp_rw [curl_off _ L k a hv]; rw [show Plaq.mark _ _ (a,p)=0 from ?_ ]; exact Rest.zero _
            rcases a with ⟨⟨_|a,_|_⟩,i⟩ <;> first | rfl| exact (hv a rfl).elim
   | cons i l ih=>
       rw [List.length_cons,Nat.cast_add,Nat.cast_one,show (2+(l.length+1)-wfield a:ℤ)=1+(2+(l.length:ℤ)-wfield a) by omega]; simp_rw [speed]; convert (stepForm p i).mul ih using 1; unfold Plaq.mark; rcases a with ⟨⟨_|a,_|_⟩,c⟩ <;> first | (solve| simp [gpath]) | simp [gpath,der_add,mul_assoc]
lemma rope_rest (D:Plaq)(k:CI G)(a:Branch G Axis)(p:QP): Rest (fun t:ℝ=>run (ropeV idRail D 0 k) [(a,t • p)]) (D.value-wfield a) (D.mark k (a,p)):= by
    unfold ropeV; by_cases hv:D.i<D.j; · simp_rw [dif_pos hv]; exact clot_rest (Studio.pos _ _ hv) ..
    simp_rw [dif_neg hv]; by_cases he:D.j<D.i; · simp_rw [dif_pos he,map_neg]; convert (clot_rest (Studio.pos _ _ he) D.jets k a p).smul (-1) using 1; ext; simp; rfl; change _= (-1:ℂ)*gpath D.j D.i k _ (a,p); rcases a with ⟨⟨_|x,_|_⟩,c⟩ <;> first| (solve| simp [Plaq.mark,gpath])| simp [Plaq.mark,gpath,← mul_neg, neg_sub]
    have hi:D.i=D.j:= le_antisymm (le_of_not_gt he) (le_of_not_gt hv)
    simp_rw [dif_neg he,map_zero]; rw [show D.mark k (a,p)=0 from by rcases a with ⟨⟨_|a,_|_⟩,c⟩ <;> simp [Plaq.mark,gpath,hi]]; exact Rest.zero _
end YM.MS.Lifting
