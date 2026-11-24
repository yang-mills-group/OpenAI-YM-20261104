import YM.RG12.Strike.Sol
/-! # Trace-free test of the single barrage

Uses the rating on inputs to actually kill ALL but the leading spherical term;
always off 0. Does not even presume uniform equivariance for the evaluated kernels.
Dualizing harmonic tensors at output will therefore see only the resonant projection. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Strike
open Function Set Filter MeasureTheory Real Finset
open scoped Topology InnerProductSpace ContDiff BigOperators Classical

def link (i:Axis4)(P:Cells→ℂ)(v:Cells):=P (i::v)
lemma fitted (i:Axis4){n:ℕ}{P:Cells→ℂ}(hP:Rated (n+1) P):Rated n (link i P):=by
  refine ⟨fun h he=>(hP.sym (List.Perm.cons i h) (by simp only [List.length_cons,he])),fun {v} he=>?_⟩
  have h(j): P (i::j::j::v)=P (j::j::i::v):= hP.sym ((List.Perm.swap j i (j::v)).trans (List.Perm.cons j (List.Perm.swap j i v))) (by simp only [List.length_cons]; omega)
  unfold link;simp_rw [h]; exact hP.clean (by simp only [List.length_cons]; omega)

variable {n:ℕ}
lemma cons_bill {n:ℕ} (f:Strip (n+1)→ℂ):
    ∑ v:Strip (n+1),f v=∑i:Axis4,∑v:Strip n,f (Fin.cons (α:=fun _=>Axis4) i v):=by
   let e:=Fin.consEquiv (n:=n) (fun _=>Axis4); have he:= Fintype.sum_equiv e (fun v => f (e v)) f (fun _=>rfl)
   rw [Fintype.sum_prod_type] at he; exact he.symm
lemma essence (P:Cells→ℂ)(x:R): fall (gauge (n+1) P) x=∑i:Axis4,(x i:ℂ)*fall (gauge n (link i P)) x:=by
   unfold fall; rw [cons_bill]
   apply sum_congr rfl;intro i _;rw [mul_sum];apply sum_congr rfl;intro v _;simp only [gauge,Function.comp_apply,List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,rain, Fin.prod_univ_succ,link];ring -- syntax

def draw (i:Axis4)(v:Strip n)(x:R):ℂ:= ∑ j:Fin n,(∏ l ∈ univ.erase j,(x (v l):ℂ))*matchC (v j) i
lemma dripped (i:Axis4)(v:Strip n)(x:R) : HasDerivAt (fun t:ℝ=>rain v (palette i x t)) (draw i v x) 0:=by
   simpa only [rain,draw,born, matchC,smul_eq_mul] using!
    (HasDerivAt.fun_finsetProd (f:=fun j (t:ℝ)=>(palette i x t (v j):ℂ)) (u:=univ) (fun j _=>strike_leaf i (v j) x))
def drops (P:Strip n→ℂ)(i:Axis4)(x:R):ℂ:=∑ v:Strip n,P v*draw i v x
lemma shower (P:Strip n→ℂ)(i:Axis4)(x:R) : HasDerivAt (fall P ∘ palette i x) (drops P i x) 0:=by
   simpa only [fall,Function.comp_def, drops, zero_mul,zero_add] using! (HasDerivAt.fun_sum (u:=univ) (fun v (_:v∈_)=> (hasDerivAt_const (0:ℝ) (P v)).mul (dripped i v x))) -- Pi mul type rfl
variable (x:R){n:ℕ}{P:Cells→ℂ}(H:Rated (n+1) P)
include H
lemma clears : ∑ i:Axis4,drops (gauge n (link i P)) i x=0:=by
   unfold drops draw; simp_rw [mul_sum]; rw [sum_comm];
   simp_rw [sum_comm (f:=fun i (_:Fin n)=> (gauge _ (link i P) _)*_)]
   rw [sum_comm]; apply sum_eq_zero; intro j _
   let A(i:Axis4)(v:Strip n):= P (i::List.ofFn v)
   let b(v:Strip n):ℂ:= ∏ l∈ univ.erase j,(x (v l):ℂ)
   let f(v:Strip n):= A (v j) v * b v
   change ∑ v:Strip n,∑ i:Axis4,A i v*(b v*(if v j=i then 1 else 0))=0
   simp_rw [mul_ite, mul_one,mul_zero,Finset.sum_ite_eq,if_pos (Finset.mem_univ (_:Axis4))]
   change ∑ v:Strip n,f v=0
   have hz(v:Strip n):∑ t:Axis4,f (update v j t)=0:=by
      have hh(t:Axis4):b (update v j t)=b v:=by unfold b; refine prod_congr rfl ?_; intro l hl; rw [update_of_ne (ne_of_mem_erase hl)]
      unfold f; simp_rw [Function.update_self,hh,← Finset.sum_mul]
      apply mul_eq_zero_of_left
      cases n with
      | zero=>exact Fin.elim0 j
      | succ n=>
         let s:=Equiv.swap (0:Fin (n+1)) j;let u(k:Fin n):=v (s k.succ)
         have ha(t:Axis4):A t (update v j t)=P (t::t::List.ofFn u):=by
            unfold A;apply H.sym
            · have he:(fun k=> update v j t (s k)) = Fin.cons (α:=fun _=>Axis4) t u:=by
                 funext i; refine Fin.cases ?_ (fun l=>?_) i
                 · simp [s]
                 rw [Fin.cons_succ]; exact Function.update_of_ne (by have hh:=s.injective.ne (Fin.succ_ne_zero l); rwa [show s 0=j from Equiv.swap_apply_left ..] at hh) _ _
              apply List.Perm.cons; apply (s.ofFn_comp_perm (update v j t)).symm.trans
              rw [Function.comp_def,he,List.ofFn_succ]; simp
            simp
         simp_rw [ha]; exact H.clean (by simp)
   have hh':=soared j f; simp_rw [hz,sum_const_zero] at hh'; exact (mul_eq_zero.mp hh'.symm).resolve_left (by norm_num)

-- full linear propagation of single input along STF. unify `hit` and `barrage` calendars
def unionized (P:Cells→ℂ)(n:ℕ)(x:R):ℂ:=∑ v:Strip n, P (List.ofFn v) * barrage field (List.ofFn v) x
omit H in
lemma spill (n:ℕ)(P:Cells→ℂ){x:R}(hx:x≠0): unionized P (n+1) x = ∑ i:Axis4, hit i (unionized (link i P) n) x:=by
   unfold unionized; rw [cons_bill]; apply sum_congr rfl;intro i _
   let f(v:Strip n)(x:R):= (link i P (List.ofFn v))* barrage field (List.ofFn v) x
   rw [show (fun x=>∑ v:Strip n,f v x)=(∑v:Strip n,f v) from funext (fun x=>(by simp))]
   have hi(v:Strip n):silk puncture (f v):=fun y hy=> contDiffAt_const.mul (vellum punct_open punct_field _ y hy)
   rw [thread (show x∈puncture from hx) (T:=univ) f (fun i _=>hi i)]
   apply sum_congr rfl;intro v hv; unfold f; rw [Strike.spin]
   simp only [List.ofFn_succ, Fin.cons_zero,Fin.cons_succ,link,barrage]
   -- test list ofFn may need simp
omit H in
-- IH formula *at every x*, differentiated then dropping annih
lemma pose (n:ℕ):∀ P:Cells→ℂ, Rated n P→∀ x∈puncture,
   unionized P n x=coefficient n * (black x^(n+1))⁻¹ * fall (gauge n P) x:=by
   induction n with
   | zero=> intro P hP x hx; unfold unionized fall gauge; simp [field,barrage,coefficient,rain]; ring
   | succ n h=>
     intro P hP x hx
     let K(i):=link i P
     let f(i)(x:R):=coefficient n * (black x ^(n+1))⁻¹ * fall (gauge n (K i)) x
     rw [spill n P hx]
     let u:= (black x^(n+2))⁻¹; let c:=coefficient n; let F i:=fall (gauge n (K i)) x; let z:= -(2*((n+1:ℕ):ℂ)) *c*u
     let D i:=drops (gauge n (K i)) i x
     have he(i:Axis4): hit i (unionized (K i) n) x=z*((x i:ℂ)*F i)+c*(black x^(n+1))⁻¹*D i:=by
        rw [in_turn punct_open hx (g:=f i) i (h _ (fitted i hP))]
        have ht:= ((hasDerivAt_const (0:ℝ) c).mul (negative i x (n+1) hx)).mul (shower (gauge n (K i)) i x)
        unfold hit
        rw [show f i ∘ palette i x = (((fun _=>c)*((fun z=>(black z^(n+1))⁻¹) ∘ palette i x)) * (fall (gauge n (K i)) ∘ palette i x)) from rfl,ht.deriv]
        simp only [zero_mul,zero_add, Function.comp_apply,Pi.mul_apply,born]; unfold z c u F D; ring
     change (∑ i:Axis4, hit i (unionized (K i) n) x)= _
     simp_rw [he,Finset.sum_add_distrib, ← mul_sum]
     rw [show ∑ i:Axis4,D i=0 from Strike.clears x hP, mul_zero, add_zero, essence]
     congr 1; unfold z u c; simp [coefficient];try ring
end YM.RG12.Strike
