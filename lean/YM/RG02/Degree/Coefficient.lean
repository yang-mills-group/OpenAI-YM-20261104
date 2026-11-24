import YM.RG02.Wick.Board

/-!
Surface counts in the full polynomial space of torus arguments, any arity.
No coefficient price implied by being a bounded-degree polynomial here. Keep
the sum along covariance afterwards; exposed `Payment` can refer to any
charged presentation of the polynomial, not equality of its original supported
coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Shear
open MvPolynomial Finset Next.Rank Next.Rank.Normal Function Wick
open PertExtension
open scoped Classical BigOperators
variable {X E : Type} [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup E][NormedSpace ℝ E]

def Payment (n : ℕ)(f : X→ℂ) := ∃ p : poly (Module.Dual ℝ X), f=paint id p ∧ totalDegree p ≤ n
namespace Payment
variable {f g : X→ℂ}{n i : ℕ}
lemma raise (h : Payment n f)(hi:n≤ i) : Payment i f := by obtain ⟨p,h,hp⟩ := h; exact ⟨p,h,hp.trans hi⟩
lemma const (c:ℂ) (n:ℕ) : Payment n (fun _ : X=>c) := ⟨C c,funext fun _=>by simp [paint],by simp⟩
lemma comp (L : Module.Dual ℝ X) : Payment 1 fun x=> (L x:ℂ) := ⟨MvPolynomial.X L,funext fun _=>by simp [paint],by simp⟩
lemma mul (hf : Payment n f)(hg : Payment i g) : Payment (n+i) (f*g) := by
   obtain ⟨p,hp,hq⟩:=hf; obtain ⟨r,hr,hR⟩:=hg
   exact ⟨p*r,funext fun x=> by rw [hp,hr]; simp [paint], (totalDegree_mul p r).trans (add_le_add hq hR)⟩
lemma plus (hf : Payment n f)(hg : Payment n g) : Payment n (f+g) := by
   obtain ⟨p,hp,hq⟩:=hf; obtain ⟨r,hr,hR⟩:=hg
   exact ⟨p+r,funext fun x=> by rw [hp,hr]; simp [paint], (totalDegree_add p r).trans (sup_le hq hR)⟩
lemma scale (h : Payment n f)(c : ℂ) : Payment n (c • f) := by simpa only [zero_add] using! mul (const (X:=X) c 0) h
lemma sum {I : Type*}(s : Finset I)(f : I→ X→ℂ)(h : ∀ i∈s,Payment n (f i)) : Payment n (∑ i∈s,f i) := by
   induction s using Finset.induction_on with
   | empty => rw [sum_empty]; exact const 0 _
   | insert i s hi ih => rw [sum_insert hi]; exact (h i (mem_insert_self ..)).plus (ih fun i hi=>h _ (mem_insert_of_mem hi))
lemma plane {I : Type*}(s : Finset I)(f:I→ X→ℂ)(h : ∀ i∈s,Payment n (f i)) : Payment n (fun x=>∑ i∈s,f i x) := by
   convert sum s f h using 1; ext1 x; exact (Finset.sum_apply ..).symm
lemma product {I : Type*}(s : Finset I)(f : I→ X→ℂ)(d:I→ℕ) (h : ∀ i∈s,Payment (d i) (f i)) : Payment (∑ i∈s,d i) (∏ i∈s,f i) := by
   induction s using Finset.induction_on with
   | empty=> rw [prod_empty]; exact const 1 _
   | insert i s hi ih => rw [sum_insert hi,prod_insert hi]; exact (h i (mem_insert_self ..)).mul (ih fun i hi=>h _ (mem_insert_of_mem hi))

variable [FiniteDimensional ℝ X]
lemma smooth (h : Payment n f) : ContDiff ℝ ⊤ f := by
   obtain ⟨p,rfl,H⟩:=h; clear H; unfold paint
   induction p using MvPolynomial.induction_on with
   | C => simp; exact contDiff_const
   | add P Q h hp => simp_rw [map_add]; exact h.add hp
   | mul_X P a h => simp_rw [map_mul,MvPolynomial.aeval_X]; exact h.mul (Complex.ofRealCLM.contDiff.comp a.toContinuousLinearMap.contDiff)
end Payment

/-- One vertex budget from its expansion at a germ. c may have several
external polynomial presentations. M numbered Wick legs; same covariance
applied to each occurrence. -/
structure Vertex (X E : Type)[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup E][NormedSpace ℝ E] where
   n : ℕ
   c : X → ℂ
   legs : Fin n → Module.Dual ℝ E

namespace Vertex
def Counts (v : Vertex X E) (k : ℕ) := v.n≤k ∧ Payment (k-v.n) v.c
variable {v w : Vertex X E}{k i : ℕ}
lemma Counts.raise (h : v.Counts k)(ha:k≤ i) : v.Counts i := ⟨h.1.trans ha, h.2.raise (Nat.sub_le_sub_right ha _)⟩

def cost (v : Vertex X E) : X→ poly (Module.Dual ℝ E) := fun x => v.c x • glyphs v.legs univ

def eval (v : Vertex X E)(x : X×E) := Wick.paint id (cost v x.1) x.2

def renew (v w:Vertex X E) : Vertex X E := {
   n:=v.n+w.n
   legs:= Fin.append v.legs w.legs
   c:= v.c*w.c }
lemma full (h : v.Counts k)(hh : w.Counts i) : (renew v w).Counts (k+i) := by
   obtain ⟨he,h⟩:= h; obtain ⟨ht,hg⟩:=hh
   refine ⟨add_le_add he ht,?_⟩
   exact (h.mul hg).raise (by dsimp only [renew]; omega)

lemma value (v : Vertex X E) (x : X× E) : eval v x = v.c x.1 * ∏ i:Fin v.n, (v.legs i x.2:ℂ) := by simp [eval,cost,paint,glyphs]
lemma renew_cost (v w : Vertex X E) : cost (renew v w)=cost v*cost w := by
   funext x; unfold cost renew; simp only [glyphs,Pi.mul_apply]; rw [Fin.prod_univ_add]; simp; rw [mul_smul, smul_comm]
lemma renew_eval (v w : Vertex X E) : (renew v w).eval=v.eval*w.eval := by
   funext x; unfold eval; rw [renew_cost]; simp [paint]
end Vertex

/-- Ordered enumeration, can have repeated terms. -/
def Rolls (k : ℕ)(f : X× E→ℂ) :=
    ∃ (n : ℕ)(v : Fin n→ Vertex X E), f=∑ i,(v i).eval ∧ ∀ i, (v i).Counts k
namespace Rolls
variable {k w : ℕ}{f g : X× E→ℂ}
lemma rise (h : Rolls k f)(hw:k≤w) : Rolls w f := by obtain ⟨n,v,h,H⟩:=h; exact ⟨n,v,h,fun i=>(H i).raise hw⟩
lemma atoms (v : Vertex X E)(h : v.Counts k) : Rolls k v.eval := ⟨1,(fun _=> v), (by simp),fun _=>h⟩
lemma const (c:ℂ) : Rolls k (fun _ : X× E=> c) := by
   let v:Vertex X E:= ⟨0,fun _ => c,fun _=>0⟩
   convert atoms v ⟨Nat.zero_le k,Payment.const _ _⟩ using 1; funext x; simp [Vertex.value,v]
lemma add (h : Rolls k f)(H : Rolls k g) : Rolls k (f+g) := by
   obtain ⟨n,v,rfl,h⟩:=h; obtain ⟨m,w,rfl,H⟩:=H
   refine ⟨n+m,Fin.append v w,?_,?_⟩
   · rw [Fin.sum_univ_add]; simp
   refine Fin.addCases ?_ ?_
   · intro i; simpa using h i
   intro i; simpa using H i
lemma mul (h : Rolls k f)(H : Rolls w g) : Rolls (k+w) (f*g) := by
   obtain ⟨n,v,rfl,h⟩:=h; obtain ⟨m,w,rfl,H⟩:=H
   let e := Fintype.equivFin (Fin n× Fin m)
   let L (p : Fin n×Fin m):= Vertex.renew (v p.1) (w p.2)
   refine ⟨_, L ∘ e.symm,?_,fun i=>Vertex.full (h _) (H _)⟩
   rw [← Equiv.sum_comp e,Fintype.sum_prod_type]; simp only [Function.comp_apply,Equiv.symm_apply_apply,L, Vertex.renew_eval]; rw [sum_mul_sum]
lemma scale (h : Rolls k f)(c : ℂ) : Rolls k (c • f) := by simpa only [zero_add] using! (const (k:=0) c).mul h
lemma listed {I : Type*}(s : Finset I)(f : I→ X× E→ℂ)(h : ∀ i∈s,Rolls k (f i)) : Rolls k (∑ i∈s,f i) := by
   induction s using Finset.induction_on with
   | empty => rw [sum_empty]; exact const 0
   | insert i s hi ih => rw [sum_insert hi]; exact (h i (mem_insert_self ..)).add (ih fun i hi=>h _ (mem_insert_of_mem hi))
lemma groups {I : Type*}(s : Finset I)(f : I→ X× E→ℂ)(h : ∀ i∈s,Rolls 1 (f i)) : Rolls s.card (∏ i∈s,f i) := by
   induction s using Finset.induction_on with
   | empty => rw [prod_empty]; exact const 1
   | insert i s hi ih => rw [prod_insert hi,card_insert_of_notMem hi,add_comm _ 1]; exact (h i (mem_insert_self ..)).mul (ih fun i hi=>h _ (mem_insert_of_mem hi))
lemma linear (L : X× E →ₗ[ℝ]ℝ) : Rolls 1 fun x=> Complex.ofReal (L x) := by
   let a := L ∘ₗ LinearMap.inl ℝ X E; let b:= L ∘ₗ LinearMap.inr ℝ X E
   let v:Vertex X E:= ⟨0,(fun x=> Complex.ofReal (a x)), fun _=>0⟩
   let w:Vertex X E:= ⟨1,(fun _=>1),fun _=>b⟩
   have he : Rolls 1 v.eval := atoms v ⟨Nat.zero_le 1,Payment.comp a⟩
   have hh : Rolls 1 w.eval := atoms w ⟨le_refl _, Payment.const _ _⟩
   convert he.add hh using 1
   funext ⟨x,y⟩; rw [Pi.add_apply, Vertex.value,Vertex.value];
   have h : L (x,y)=a x+b y:= by unfold a b; simp only [LinearMap.comp_apply,← map_add]; simp
   simp [v,w,h]

set_option backward.isDefEq.respectTransparency false in
lemma allColor {Y : Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]
    (F : ContinuousMultilinearMap ℝ (fun _ : Fin k=>Y) ℂ)(L : X× E→ₗ[ℝ]Y)(a:Y) :
    Rolls k fun x => F fun _ => L x+a := by
   let B := Module.finBasis ℝ Y; let N := Module.finrank ℝ Y
   let g:= F.toMultilinearMap
   have hh x : F (fun _=>L x+a) = ∑ j : Fin k→ Fin N, (∏ i : Fin k,B.coord (j i) (L x+a)) • F fun i=>B (j i) := by
      change g _ = _
      nth_rw 1 [← show ∑ i:Fin N,B.coord i (L x+a) • B i= L x+a from B.sum_repr _]
      rw [g.map_sum]; apply sum_congr rfl; intro j _; rw [g.map_smul_univ]; rfl
   let u (j:Fin k → Fin N) i (x:X× E) := Complex.ofReal (B.coord (j i) (L x+a))
   have hu (j i) : Rolls 1 (u j i) := by
      change Rolls 1 fun x=> u j i x; simp_rw [u,map_add,Complex.ofReal_add]; exact (linear _).add (f:= fun x=> Complex.ofReal ((B.coord (j i) ∘ₗ L) x)) (const _)
   let H (j:Fin k→Fin N) := F (fun i=> B (j i)) • ∏ i:Fin k, u j i
   have hb j : Rolls k (H j) := by refine Rolls.scale ?_ _; simpa using! groups univ _ (fun i _=> hu j i)
   rw [show (fun x : X× E=> F fun _=> L x+a) =∑ j:Fin k→Fin N,H j from ?_]; exact listed _ _ (fun i _=>hb i)
   funext x
   rw [hh,Finset.sum_apply]; exact sum_congr rfl fun j _=> by unfold H; simp only [Finset.prod_apply,u, Pi.smul_apply,smul_eq_mul,← Complex.ofReal_prod,mul_comm]; rfl

lemma jets {Y : Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]
    (F : Y→ℝ)(k : ℕ)(L : X× E→ₗ[ℝ]Y)(a:Y) : Rolls k (fun x=> Complex.ofReal (Series.Radial.jet F k (L x+a))) := by
   simp_rw [Series.Radial.jet,Complex.ofReal_mul]
   exact (allColor (Complex.ofRealCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ k F 0)) L a).scale _
end Rolls
end YM.RG02.Shear
