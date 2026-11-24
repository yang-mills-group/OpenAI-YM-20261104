import YM.X.Try.Stomp
/-!
# Real radial powers, Complex sign. First two open jets of Pop before W price.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set Asymptotics Gauge
open Source PertExtension LatticePT Braid Gauss ProjectorNext.Calibration Bid
open Stems hiding X
open Heat.Top
open Jet hiding Word
open scoped Topology ContDiff BigOperators Pointwise Classical
variable {G:Gauge} {d n k:ℕ} {V I:Type*}{S:ℝ→ℂ}
lemma jo_cmplx {f g:ℝ→ℂ}(hf:ContDiffAt ℝ ω f 0)(hg:ContDiffAt ℝ ω g 0): someJ (f*g) n=∑ i∈Finset.range (n+1),someJ f i * someJ g (n-i):= by
   simp_rw [someJ,iteratedDeriv_mul (hf.of_le (show ↑n≤ω from le_top)) (hg.of_le le_top),RCLike.real_smul_eq_coe_smul (K:=ℂ), smul_eq_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; have h:i≤n:= Nat.le_of_lt_succ (Finset.mem_range.mp hi)
   have hh : ↑(n.choose i) * (i.factorial:ℂ) * (n-i).factorial =(n.factorial:ℂ):= by exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
   have hA : (↑(n.choose i):ℂ) ≠0:= by exact_mod_cast (Nat.choose_pos h).ne'
   have hB(k:ℕ): (↑k.factorial:ℂ) ≠0:= by exact_mod_cast k.factorial_ne_zero
   push_cast; rw [←hh]; field_simp
structure Plain (f:ℝ→ℂ)(d:ℕ)(p q:ℂ):Prop where
    ok : ContDiffAt ℝ ω f 0
    dune (i:ℕ)(he:i<d): someJ f i=0
    bare : someJ f d=p
    awake : someJ f (d+1)=q
variable {p p' q q':ℂ}
namespace Plain
variable {f g:ℝ→ℂ}
lemma caption (c:ℂ) (h:Plain f d p q): Plain (c • f) d (c • p) (c • q):= by
    have e(i:ℕ): someJ (c • f) i=c • (someJ f i):= by unfold someJ;rw [iteratedDeriv_const_smul_field]; exact smul_comm _ _ _
    refine ⟨h.ok.const_smul c,fun i hi=> by rw [e,h.dune i hi,smul_zero],by rw [e,h.bare],by rw [e,h.awake]⟩
lemma add (h:Plain f d p q)(he:Plain g d p' q'):Plain (f+g) d (p+p') (q+q'):= by
    have hg(k:ℕ):someJ (f+g) k=someJ f k+someJ g k:= by unfold someJ; rw [iteratedDeriv_add (h.ok.of_le (show (↑k:WithTop ℕ∞)≤ω from le_top)) (he.ok.of_le le_top),smul_add]; -- name
    exact ⟨h.ok.add he.ok,fun i hi=> by rw [hg,h.dune i hi,he.dune i hi, zero_add],by rw [hg,h.bare,he.bare],by rw [hg,h.awake,he.awake]⟩
lemma offset (h:Plain f d p q)(hi:n<d): Plain f n 0 (if n+1=d then p else 0):= ⟨h.ok,fun i hx=>h.dune _ (hx.trans hi),h.dune _ hi, by
    split
    next H=> rw [H,h.bare]
    next H=> exact h.dune _ (by omega)⟩ -- syntax
lemma zero : Plain (0:ℝ→ℂ) d 0 0:= by
    have h (i:ℕ): someJ (0:ℝ→ℂ) i=0:= by simp [someJ]
    exact ⟨contDiffAt_const,fun i _=> h i,h d,h _⟩
lemma one : Plain (1:ℝ→ℂ) 0 1 0:= by refine ⟨contDiffAt_const,fun _ h=> (Nat.not_lt_zero _ h).elim, by simp,?_⟩; rw [Gauss.jo_one, show (1:ℝ→ℂ)=(fun _=> 1) from rfl]; simp
lemma mult (h:Plain f d p q)(he:Plain g 1 p' q') : Plain (f*g) (d+1) (p*p') (q*p'+p*q'):= by
    refine ⟨h.ok.mul he.ok, fun i hi=>?_,?_,?_⟩
    · rw [jo_cmplx h.ok he.ok]; apply Finset.sum_eq_zero; intro b hb; by_cases hx:b<d; · rw [h.dune b hx,zero_mul]
      rw [he.dune _ (by omega),mul_zero]
    · rw [jo_cmplx h.ok he.ok, Finset.sum_eq_single d]; rw [h.bare, Nat.add_sub_cancel_left,he.bare]; intro b _ hp; by_cases hx:b<d; · rw [h.dune b hx, zero_mul]
      rw [he.dune _ (by omega),mul_zero]; simp
    let s:=Finset.range (d+1+1+1); let g(k:ℕ):= someJ f k * someJ g (d+1+1-k); let t:Finset ℕ:={d+1,d}; have h₀ : t⊆ s:= by intro i hi; simp [s]; simp [t] at hi; omega
    rw [jo_cmplx h.ok he.ok,← Finset.sum_subset (f:=g) h₀ ?_];
    · have hz:d+1≠ d:= by omega
      unfold t g; rw [Finset.sum_insert (by simpa), Finset.sum_singleton, h.awake, show d+1+1-(d+1)=1 by omega, h.bare, show d+1+1-d=1+1 by omega,he.bare,he.awake]
    intro i _ hi; simp only [t, Finset.mem_insert, Finset.mem_singleton,not_or] at hi; unfold g; by_cases hy:i<d; · rw [h.dune i hy,zero_mul]
    rw [he.dune _ (by omega),mul_zero]
lemma collect {f:I→ℝ→ℂ}{p q:I→ℂ}(s:Finset I)(h:∀i∈s,Plain (f i) d (p i) (q i)): Plain (∑ i∈s,f i) d (∑ i∈s,p i) (∑ i∈s,q i):= by induction s using Finset.induction_on with| empty=> rw [Finset.sum_empty,Finset.sum_empty,Finset.sum_empty]; exact zero| insert i s he IH=> rw [Finset.sum_insert he,Finset.sum_insert he,Finset.sum_insert he]; exact (h _ (by simp)).add (IH (fun j hj=> h j (by simp [hj])))
end Plain

def festival (x:Brush G) : poly (Atom G)→ₐ[ℂ] (ℝ→ℂ):= aeval (fun z:Atom G=> Complex.ofReal ∘ along (SlotV z) x)
def delve (z:Atom G): Curly G:= mark (SlotV z) (equipped z) 2
variable (F:V→Atom G)(x:Brush G)
lemma staple (i:Atom G): Plain (festival x (X i)) 1 (snap x (loom (X i))) (snap x (call loom delve (X i))):= by
    rw [call_X,festival,aeval_X]; let p:=along (SlotV i) x; have hg : ContDiffAt ℝ ω p 0:= along_zero (equipped i) x; let L:=Complex.ofRealCLM
    have he(k:ℕ): someJ (L ∘ p) k=L (someJ p k):= ((show Act k p (someJ p) from ⟨hg,fun _ _=> rfl⟩).linear (L:=L)).writes k le_rfl
    refine ⟨L.contDiff.contDiffAt.comp 0 hg,fun v hv=>?_,?_,?_⟩
    · have hz:p 0=0:= by simp [p,along,SlotV, RG.Slot.eval, faceValue,Pressure.one]
      rw [show v=0 by omega, show Complex.ofReal ∘ _=L ∘ p from rfl,he, someJ_zero,hz,map_zero]
    · have hp:= (EuclideanSpace.proj (𝕜:=ℝ) i.2).hasFDerivAt.comp_hasDerivAt (0:ℝ) (traveled x i.1); change someJ (L ∘ p) 1=_; rw [he,Gauss.jo_one, show deriv p 0= v x i.1 i.2 from hp.deriv, looms, aeval_X] -- typo
      rfl
    change someJ (L ∘ p) _= snap x _; rw [he,delve, mark_test]; rfl
lemma ceremony (p:poly V)(h:HC p d):
   let q:= rename F p; Plain (festival x q) d (snap x (loom q)) (snap x (call loom delve q)):= by
    intro q; let L:=(festival x).comp (rename F); let Y:=((snap x).comp (loom.comp (rename F))); let Y':=(snap x).toLinearMap ∘ₗ (call loom delve) ∘ₗ (rename F).toLinearMap
    have he (a b:poly V):Y' (a*b)=Y' a * Y b+Y a*Y' b:= by
       change snap x (call _ _ ((rename F) (a*b)))=_; rw [map_mul (f:=rename F),call_mul,map_add]; simp only [map_mul]; rfl
    have hx (k:ℕ)(v:Fin k→V)(s:Finset (Fin k)):let p:=glyphs v s; Plain (L p) s.card (Y p) (Y' p):= by
       induction s using Finset.induction_on with
       | empty=> simp only [glyphs,Finset.prod_empty, Finset.card_empty,map_one]; rw [show Y' 1=0 from ?_]; exact Plain.one; change snap x (call _ _ ((rename F) 1))=0; rw [map_one,call_1,map_zero]
       | insert i s ht IH=>
          let Q:= X (R:=ℂ) (v i); have hh:Plain (L Q) 1 (Y Q) (Y' Q):= by unfold L Y Y' Q; change Plain (festival x ((rename F) (X _))) _ (snap x (loom ((rename F) (X _)))) (snap x (call _ _ ((rename F) (X _)))); rw [rename_X]; exact staple ..
          rw [show glyphs v (insert i s)=glyphs v s*Q from (Finset.prod_insert ht).trans (mul_comm ..) , Finset.card_insert_of_notMem ht]; simp only [map_mul,he]; exact Plain.mult IH hh
    change Plain (L p) d (Y p) (Y' p); rw [p.as_sum,map_sum,map_sum,map_sum]; refine Plain.collect _ (fun i hi=>?_); obtain ⟨t,hz⟩:= Common.letter i; let n:= i.sum fun _ j=>j; have hh:n=d:= (Heat.Top.degree_eq i).symm.trans (h (mem_support_iff.mp hi)); rw [show monomial i (coeff i p) =coeff i p • monomial i (1:ℂ) from ?_,map_smul,map_smul,map_smul,hz];
    · exact Plain.caption _ (by convert! hx n t Finset.univ using 1; rw [Finset.card_univ, Fintype.card_fin, hh])
    rw [← map_smul, smul_eq_mul,mul_one]
end YM.PositionX.Tri
