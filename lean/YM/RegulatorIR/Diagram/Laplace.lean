import YM.RegulatorIR.Diagram.Render

/-! Contractions read on finite polynomials: even when K kills some
modes, these formulas use the *same full Wick* covariance. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram
open MvPolynomial Function Budget Budget.Layer Budget.Tuple Budget.Packet
open scoped Topology BigOperators Classical
variable {I : Type} {r s: ℕ} [Fintype I]

-- no 1/2 in these two operators
def sweep (K:Layer I I)(p:Jet I) := ∑ i:I,∑ j:I, C (K i j)*pderiv i (pderiv j p)
def meet (K:Layer I I)(p q:Jet I) := ∑ i:I,∑ j:I, C (K i j)*pderiv i p * pderiv j q

lemma sweep_sum {Z : Type}(K:Layer I I)(s:Finset Z)(f: Z→Jet I): sweep K (∑ i∈s,f i) =∑ i∈s,sweep K (f i):= by
 induction s using Finset.induction_on with
 | empty=> simp [sweep]
 | insert i s h ih=>rw [Finset.sum_insert h,Finset.sum_insert h,← ih]; simp [sweep,map_add,mul_add,Finset.sum_add_distrib]
omit [Fintype I] in
lemma pderiv_cc (x:I)(y:ℝ)(p:Jet I): pderiv x (C y*p) = C y * pderiv x p := by rw [Derivation.leibniz,pderiv_C,smul_zero, add_zero]; rfl
lemma render_loop (K:Layer I I)(T:Packet I (r+2))(h:IsSym T) : sweep K (render T) = ((r:Jet I)+2)*((r:Jet I)+1)*render (loop T K):=by
 let Q:= (↑r+2:Jet I); let V:= (↑r+1:Jet I)
 have ht i j : pderiv i (pderiv j (render T)) = Q*V*render (slice (slice T i) j):= by
    rw [pderiv_render _ h]; rw [show ((r+1:ℕ):Jet I)+1=C ((r:ℝ)+2) by push_cast; rw [map_add,map_ofNat,map_natCast]; ring,
      pderiv_cc,pderiv_render _ (cons_symm T h j),second_symm T h]; simp only [Q,V,map_add,map_natCast,map_ofNat,mul_assoc]
 unfold sweep
 simp_rw [ht, show ∀ (i j:I) (b:Jet I), C (K i j)*(Q*V*b)=(Q*V)*(C (K i j)*b) from fun i j b=> by ring, ← Finset.mul_sum]
 congr 1
 unfold render
 simp_rw [Finset.mul_sum]
 rw [← Fintype.sum_prod_type']
 rw [Finset.sum_comm]; apply Finset.sum_congr rfl;intro z _
 rw [loop,tsum_fintype,map_sum,Finset.sum_mul]
 apply Finset.sum_congr rfl; intro a _
 rw [curve,map_mul];exact (mul_assoc ..).symm

lemma sweep_const (T:Packet I 0)(K:Layer I I) : sweep K (render T)=0 :=by simp [sweep,render,word]
lemma pderiv_scale_zero (T:Packet I 0)(i:I) : pderiv i (render T) = 0:=by simp [render,word]
lemma sweep_linear (T:Packet I 1)(K:Layer I I): sweep K (render T)=0:=by
 have h:IsSym T:= fun e z=>congr_arg T <| funext fun i=>congr_arg z (Subsingleton.elim _ _)
 unfold sweep; simp_rw [pderiv_render T h]; norm_num [pderiv_scale_zero]

lemma knot_formula (T:Packet I (r+1))(U:Packet I (s+1))(K:Layer I I)(p:Tuple I r)(q:Tuple I s) :
    knot K T U (Fin.append p q) = ∑ i:I,∑ j:I,K i j*T (Fin.cons i p)*U (Fin.cons j q):=by
 rw [knot,splice_at,tsum_fintype]
 apply Finset.sum_congr rfl;intro x _; simp_rw [lace,ray,tsum_fintype,Finset.mul_sum]
 apply Finset.sum_congr rfl; intro y _; unfold swivel; rw [Fin.cons_zero, show update (Fin.cons x q : Tuple I _) 0 y=Fin.cons y q from ?_]; ring
 ext1 i; induction i using Fin.cases <;> simp

lemma shifted_render (K:Layer I I)(T:Packet I (r+1))(U:Packet I (s+1)):
    (∑ i:I,∑ j:I, C (K i j)*render (slice T i)*render (slice U j))=render (knot K T U):=by
 unfold render
 rw [← (Fin.appendEquiv ..).sum_comp]
 let f (x : Tuple I r × Tuple I s) (a b:I) := C (K a b)* (C (T (Fin.cons a x.1))*word x.1) * (C (U (Fin.cons b x.2))*word x.2)
 have hh i j:C (K i j)*(∑ x:Tuple I r,C (T (Fin.cons i x))*word x)*(∑ y:Tuple I s,C (U (Fin.cons j y))*word y)=∑ x:Tuple I r×Tuple I s,f x i j:=by rw [Fintype.sum_prod_type]; simp only [Finset.mul_sum,Finset.sum_mul,f]; rw [Finset.sum_comm]
 change ∑ i:I,∑ j:I, C _ * (∑ x:Tuple I r,C _ * _) * (∑ x:Tuple I s,C _ * _) = ∑ x:Tuple I r × Tuple I s,C (knot K T U (Fin.append x.1 x.2))*word (Fin.append x.1 x.2)
 simp_rw [slice,hh]
 simp_rw [Finset.sum_comm (s:=Finset.univ) (t:=Finset.univ (α:=Tuple I r × Tuple I s))]
 apply Finset.sum_congr rfl; intro x _
 rw [knot_formula T U]; simp_rw [map_sum,Finset.sum_mul]
 refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>?_
 rw [map_mul,map_mul,show word (Fin.append x.1 x.2)=word x.1*word x.2 from ?_]; unfold f; ring
 unfold word; rw [Fin.prod_univ_add]; simp

lemma render_join (K:Layer I I)(T: Packet I (r+1))(U:Packet I (s+1))(h:IsSym T)(hh:IsSym U):
    meet K (render T) (render U) = (((r:Jet I)+1)*((s:Jet I)+1))*render (knot K T U):=by
 let p := ((r:Jet I)+1); let q:= ((s:Jet I)+1)
 rw [← shifted_render]; unfold meet;simp_rw [pderiv_render _ h,pderiv_render _ hh,Finset.mul_sum]
 exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=> by ring
end YM.RegulatorIR.Diagram
