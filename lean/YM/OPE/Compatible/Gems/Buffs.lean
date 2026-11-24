import YM.OPE.Compatible.Gems.Atlas
/-! # Lp books with summable leg cluster costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Finset Matrix
open scoped Topology BigOperators Classical ContDiff ENNReal
open Silt Cloud PertExtension Series Libra GaussianScore Stranded Radial Jargon Cinders Flock Lav
variable {X Y I:Type*}{t s:ℝ}{i j k:ℕ}[MeasurableSpace X]
abbrev price := ℕ→ℝ
variable {C D A:price}
section
variable [NormedAddCommGroup Y]{μ:Measure X}[IsProbabilityMeasure μ]
def Cane (μ:Measure X)(p:X→Y)(C:price):Prop:=∀ i:ℕ,0 < i → Fault μ i p (C i)
variable {f g:X→Y}
namespace Cane
lemma strong (h:Cane μ f C): Integrable f μ:= (h 1 zero_lt_one).rich.integrable (by simp)
lemma grow (h:Cane μ f C)(ht:∀ i:ℕ,0 < i → C i ≤ D i): Cane μ f D:=fun i hi=> (h i hi).mono le_rfl (ht i hi)
lemma Integral [NormedSpace ℝ Y](h:Cane μ f C): ‖∫ x,f x ∂μ‖ ≤ C 1:= (h 1 zero_lt_one).pays le_rfl
omit [IsProbabilityMeasure μ] in lemma add (h:Cane μ f C)(he:Cane μ g D): Cane μ (f+g) (C+D):=fun i hi=> (h i hi).add (he i hi) hi
omit [IsProbabilityMeasure μ] in lemma sub (h:Cane μ f C)(he:Cane μ g D): Cane μ (f-g) (C+D):=fun i hi=> (h i hi).sub (he i hi) hi
omit [IsProbabilityMeasure μ] in lemma normVal (h:Cane μ f C): Cane μ (fun x=> ‖f x‖) C:= fun i hi=> (h i hi).NormT
lemma constant {t:ℝ}(v:Y)(ht:‖v‖≤ t): Cane μ (fun _=>v) (fun _=>t):= fun _ _=>(Fault.constant (μ:=μ) v).mono le_rfl ht
lemma nil (C:price)(ht:∀ i:ℕ,0 < i → 0 ≤ C i): Cane μ (0:X→Y) C:= grow (constant (0:Y) (by rw[norm_zero (E:=Y)])) ht
omit [IsProbabilityMeasure μ] in lemma scal [NormedSpace ℝ Y] (h:Cane μ f C)(t:ℝ): Cane μ (t • f) (‖t‖ • C):=fun i hi=> (h i hi).scaling _
omit [IsProbabilityMeasure μ] in lemma sum (S:Finset I)(p:I→X→Y)(v:I→price)(h:∀ i∈S, Cane μ (p i) (v i)): Cane μ (∑ i∈S,p i) (∑ i∈S,v i):=by intro i hi; rw [Finset.sum_apply]; exact Fault.sum S p _ (fun j hj=> h j hj i hi) hi
omit [IsProbabilityMeasure μ][NormedAddCommGroup Y] in
lemma pu {p:X→ℝ}(h:Cane μ p C): Pu μ p:=fun i hi=> Exists.intro _ (h i hi)
end Cane
abbrev JumpP (C D:price):price:= fun i=> C (2*i)*D (2*i)
omit [NormedAddCommGroup Y] [IsProbabilityMeasure μ] in lemma Cane.mul {f g:X→ℝ}(h:Cane μ f C)(he:Cane μ g D): Cane μ (f*g) (JumpP C D):= fun i hi=> (h (2*i) (by omega)).double (he (2*i) (by omega)) hi
-- any finite monomial table. ∆ price with source.. Numeric scalings
abbrev hikeP (C:price):ℕ→price
     | 0=>fun _=>1
     | n+1=> JumpP C (hikeP C n)
abbrev reelP (C D:price):ℕ→price
     | 0=>fun _=>0
     | n+1=> JumpP D (hikeP C n) + JumpP C (reelP C D n)
section
omit [NormedAddCommGroup Y]
lemma dotP (x:Finset I)(f:I→X→ℝ)(h:∀ i∈x,Cane μ (f i) C): Cane μ (∏ i∈x,f i) (hikeP C x.card):=by
       induction x using Finset.induction_on with
       | empty=> rw [Finset.prod_empty,Finset.card_empty];exact Cane.constant 1 (norm_one.le)
       | insert i x hi ih=> rw [prod_insert hi,card_insert_of_notMem hi]; exact (h i (mem_insert_self ..)).mul (ih fun j hj=>h j (mem_insert_of_mem hj))
lemma craftP (x:Finset I)(f g:I→X→ℝ)(h:∀ i∈x,Cane μ (f i) C) (hp:∀ i∈x,Cane μ (g i) C) (hv:∀ i∈x,Cane μ (f i-g i) D) : Cane μ ((∏ i∈x,f i)-(∏ i∈x,g i)) (reelP C D x.card):=by
       induction x using Finset.induction_on with
       | empty=> simp only [Finset.prod_empty,sub_self,Finset.card_empty,reelP]; exact Cane.nil _ fun _ _=>le_rfl
       | insert i x hi ih=>
            let ht:=mem_insert_self i x; let p:=∏ j∈x,f j; let q:=∏ j∈x,g j; have hP(j)(hj:j∈x):=mem_insert_of_mem (a:=j) (b:=i) hj; have ht':=fun j hj=>h j (hP j hj); rw [prod_insert hi,prod_insert hi,card_insert_of_notMem hi,reelP]; rw [show f i*p-g i*q = (f i-g i)*p+g i*(p-q) from by ring]; exact ((hv i ht).mul (dotP x f ht')).add ((hp i ht).mul (ih ht' (fun j hj=>hp j (hP _ hj)) (fun j hj=>hv j (hP _ hj))))
end
lemma re_s (C D:price)(v:ℝ)(i:ℕ): reelP C (v • D) i=v • reelP C D i :=by
       induction i with
       | zero=> ext i; simp [reelP]
       | succ i ih=> rw [reelP,reelP,ih]; ext i; simp only [JumpP,Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring
end
end YM.OPE.Borealis.Galea
