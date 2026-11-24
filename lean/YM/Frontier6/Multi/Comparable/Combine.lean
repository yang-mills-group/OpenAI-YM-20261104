import YM.Frontier6.Multi.Comparable.Stock

/- Linear extension of permits, keeping fixed arities (number of terms never
   depends on scales). For null we need no Centered inference from empty L.val. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Set Finset Filter Lattice RG Wilson Extraction Cells Next.UVStress Bid Spec Platform Tale OS Word Fareway
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{I V:Type}{C:Family G}{H:Extraction.Order}{S:Table C.book}{K: Final C H S}
variable {T:Fareway I} {ξ:Ultrafilter (ℕ×ℕ)}{j k:I→ℕ}{a b:ℝ}
variable {P Q:Type}[Fintype P][Fintype Q]
section
variable {f:P→Type}{g:Q→Type}[_h:∀ i,Fintype (f i)][_hc:∀ i,Fintype (g i)]
namespace Plan
def duo (A:Plan C P f)(B:Plan C Q g): Plan C (P⊕Q) (Sum.elim f g) where
    point i:= i.rec (motive:=fun i=> Sum.elim f g i→ Cover) A.point B.point
    letter i:=i.rec (motive:=fun i=>Sum.elim f g i→C.book.Token) A.letter B.letter
    fee:= Sum.elim A.fee B.fee
@[reducible] def fsum : ∀ i:P⊕Q,Fintype (Sum.elim f g i):= fun i=> i.rec (motive:=fun i=>Fintype (Sum.elim f g i)) _h _hc
def marked (A:Plan C P f)(z:ℂ) : Plan C P f:= {A with fee:=fun i=> z*A.fee i}
end Plan
end
namespace Permit
variable {A B:BasisRay S I} (h:Permit K T ξ j k A a)
include h
lemma exceeds (he:a≤b):Permit K T ξ j k A b:= by obtain ⟨P,p,f,q,Y,w,hp,hq,hH⟩:=h.owns; exact ⟨P,p,f,q,Y,w,hp,hq.too he,hH⟩
lemma same (he:∀ᶠ i in T.via,∀ x,Congr K (A i x) (B i x)): Permit K T ξ j k B a:=by
   obtain ⟨P,p,f,q,Y,w,hp,hq,hW⟩:=h.owns; exact ⟨P,p,f,q,Y,w,hp,hq, (hW.and he).mono fun i hi=> ⟨hi.1.1, hi.1.2.1,hi.1.2.2.1,fun x=> (hi.1.2.2.2 x).trans K (hi.2 x)⟩⟩
lemma scale {z : I→ℂ}(he:T.Costs z b): Permit K T ξ j k (fun i x=> z i • A i x) (a+b):=by
   obtain ⟨P,p,f,q,Y,w,hp,hq,hW⟩:=h.owns
   let z'(i):= Plan.marked (Y i) (z i); let t' i:=‖z i‖*w i; have hv:T.Costs t' (b+a):=he.norm.mul hq
   refine ⟨P,p,f,q,z',t',hp,add_comm b a ▸ hv,?_⟩; filter_upwards [hW] with i ⟨hs,hG,hH,hE⟩; refine ⟨hs, mul_nonneg (norm_nonneg _) hG, ?_,fun x=>?_⟩
   · unfold Centered at *; filter_upwards [hH] with t h; obtain ⟨N,p'⟩:= t; obtain ⟨hN,hA,hT⟩:= h;
     refine ⟨hN,?_⟩; rw [show (z' i).cost (j i) N p'= z i • ((Y i).cost (j i) N p') from (by funext U; simp only [z',Plan.marked,Plan.cost,smul_eq_mul, Pi.smul_apply, mul_assoc, mul_sum])]; exact ⟨hA.scale _,by rw [Next.Extract.root_smul]; exact mul_le_mul_of_nonneg_left hT (norm_nonneg _)⟩
   rw [show (z' i).syntaxR (j i) x S= z i • (Y i).syntaxR (j i) x S from (by simp only [Plan.syntaxR,z',Plan.marked, smul_sum,mul_smul])]; exact (hE x).smul K _
lemma merge (he:Permit K T ξ j k B a): Permit K T ξ j k (fun i x=>A i x+B i x) a:=by
   obtain ⟨P,p,f,q,Y,w,hp,hq,hW⟩:=h.owns; obtain ⟨P',p',g,q',Y',w',hp',hq',hW'⟩:=he.owns
   let _ : ∀ i:P⊕P',Fintype (Sum.elim f g i):= Plan.fsum
   let Z i:= (Y i).duo (Y' i)
   refine ⟨P⊕P',inferInstance, Sum.elim f g,Plan.fsum,Z,w+w',fun i=> ?_,hq.add hq',?_⟩
   · cases i; exact hp _; exact hp' _
   filter_upwards [hW,hW'] with i ⟨hS,hA,hT,hG⟩ ⟨hs',hA',hT',hG'⟩
   refine ⟨fun i=>?_, add_nonneg hA hA',?_,fun x=> ?_⟩
   · cases i; exact hS _; exact hs' _
   · unfold Centered at *; filter_upwards [hT,hT'] with t h h'; obtain ⟨N,M⟩:=t; obtain ⟨hN,h₁,h₂⟩:=h; obtain ⟨hN',h₃,h₄⟩:=h'
     refine ⟨hN,?_⟩; rw [show (Z i).cost (j i) N M=(Y i).cost (j i) N M+(Y' i).cost (j i) N M from (by funext U; unfold Plan.cost; rw [Fintype.sum_sum_type]; rfl)]
     exact ⟨h₁.plus h₃, ((seamless K.room.cutoff N M).semi _ _ _ h₁ h₃).trans (add_le_add h₂ h₄)⟩
   rw [show (Z i).syntaxR (j i) x S=(Y i).syntaxR (j i) x S+(Y' i).syntaxR (j i) x S from (by unfold Plan.syntaxR; rw [Fintype.sum_sum_type];rfl)]; exact (hG _).add K (hG' _)
lemma minus (he:Permit K T ξ j k B a): Permit K T ξ j k (fun i x=>A i x-B i x) a:=by simpa only [sub_eq_add_neg,neg_one_smul] using h.merge (B:=fun i x=> (-1:ℂ) • B i x) ((add_zero a) ▸ he.scale (Fareway.Costs.const (-1:ℂ)))
omit h
lemma inactive (hξ:ξ.toFilter ≤ H.fuse) (h:H=H) : Permit K T ξ j k (fun _ _=>0) a:=by
   let Y:Plan C Empty (fun _=>Empty):=⟨Empty.elim,Empty.elim,Empty.elim⟩; refine ⟨Empty,inferInstance,(fun _=>Empty),fun _=>inferInstance,(fun _ : I=>Y),(fun _=>0),(fun (i:Empty)=> by cases i), Fareway.Costs.free, Eventually.of_forall fun i=>⟨(fun (i:Empty)=>(by cases i)),le_rfl,?_,fun x=>by simp_rw [Plan.syntaxR,Fintype.sum_empty]; exact Tale.almost K 0⟩⟩
   unfold Centered; filter_upwards [Eventually.filter_mono hξ (large_mesh H (k i))] with p hp; refine ⟨hp,?_⟩; rw [show Y.cost _ p.1 p.2=0 from (by unfold Plan.cost; simp; rfl)]; refine ⟨Interior.constant _ 0,?_⟩; -- root zero
   let Q':=center C.S p.2 hp 0; have hz:= Next.Extract.root_smul Q' (C.beta p.1 p.2) (c:=(0:ℂ)) (F:=(0:Config G (C.side p.1 p.2)→ℂ)); simpa using hz.le
lemma sums (hξ:ξ.toFilter ≤ H.fuse)(A : V→ BasisRay S I)(s:Finset V) (h:∀ i∈s,Permit K T ξ j k (A i) a): Permit K T ξ j k (fun i x=>∑ h∈s,A h i x) a:=by
   induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact inactive hξ rfl
   | @insert v s hp ih=> simp only [Finset.sum_insert hp]; exact (h _ (mem_insert_self ..)).merge (ih (fun i hi=> h _ (mem_insert_of_mem hi)))
end Permit
end YM.Frontier6.Road
