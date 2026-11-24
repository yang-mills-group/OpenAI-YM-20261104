import YM.MSbar.MeasureP.Condo
/-! Tensor transfer paying only low moments. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Measuring
open Function Filter Set Whisk
open scoped Topology BigOperators ContDiff Classical
variable {σ σ' ι e:Type}[Fintype σ][Fintype σ'][Fintype ι][Fintype e]
variable (F:σ→List ι→e→ℝ)(K: ℕ→ σ→σ'→ℝ)(T:List ι→e→σ'→ℝ)
noncomputable def parcel (F:σ→List ι→e→ℝ)(l:List ι)(i:e)(E : List σ→ℝ)(t:List σ):= ∑ h:σ,F h l i*E (h::t)
-- Actions on individual directions.Newton.* 
noncomputable def Conde(F:σ→List ι→e→ℝ)(H:ℝ): ℕ→ℕ→ (List σ→ℝ) → Prop
| 0,_,E=> |E []| ≤ H
| t+1,k,E=> ∀ (l:List ι)(i:e), l.length < k → Conde F H t (k-l.length) (parcel F l i E)
noncomputable def commit (K:ℕ→σ→σ'→ℝ)(p k:ℕ)(E:List σ→ℝ)(t:List σ'):= Yarn p (fun i=> arco K k i t*E i)
lemma poker(m:ℕ)(f:List ι→ℝ)(x:ℝ):Yarn m (fun i=> f i*x)= Yarn m f*x:=by simpa only [mul_comm x] using sheen m x f
variable (w:σ'→ℝ)(hw:∀ i,0≤w i) (a:ℝ)(k:ℕ)(p:ℕ)
variable (H:∀ q:ℕ,q≤k → ∀ i j, K q i j= Yarn q fun t=>∑ s:e,F i t s*T t s j)
include H
-- aggregation step (convert with p polynomial tags k max steps)
lemma letters {t l:ℕ}(ht:t+1≤k)(z:σ')(s:List σ')(h:s.length=l) (E:List σ→ℝ): commit K (l+1) (t+1) E (z::s)= ∑ p∈Finset.range (t+1), Yarn p (fun j=>∑ i:e,T j i z * commit K l (t+1-p) (parcel F j i E) s):=by
    let f(p:ℕ)(j:List ι)(i:e):=T j i z * commit K l (t+1-p) (parcel F j i E) s
    let g(x:σ)(m:List σ)(p:ℕ):= K p x z*arco K (t+1-p) m s*E (x::m)
    simp only [commit,twilled, arco,Finset.sum_mul]
    change (∑ j:σ,Yarn l fun m=>∑ p∈Finset.range (t+1),g j m p)=_ -- after change
    simp_rw [show ∀ i:σ,Yarn l (fun m=>∑ p∈Finset.range (t+1),g i m p)=∑ p∈Finset.range (t+1),Yarn l (fun m=>g i m p) from fun _=> franje ..]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun p hp=>?_
    let b(m):=arco K (t+1-p) m s; let P(x:σ)(j:List ι)(i:e)(m:List σ):= F x j i*T j i z*b m*E (x::m)
    have he(x:σ):Yarn l (fun m=>g x m p)= Yarn p (fun j=>∑ i:e,Yarn l (P x j i)):=by
        unfold g; simp_rw [H _ ((Finset.mem_range.mp hp).le.trans ht), ←poker, Finset.sum_mul]; rw [pool]; refine stitch p fun j _=>?_ ; rw [←scarves]
    simp_rw [he]; rw [←scarves]; refine stitch p fun j _=>?_; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; change _=T j i z *commit _ _ _ _ _
    rw [←scarves,commit,←sheen]; refine stitch _ fun m _=>?_ ; unfold parcel; rw [Finset.mul_sum,Finset.mul_sum]; refine Finset.sum_congr rfl fun x _=>?_ ; unfold P b; ring
variable (ha:0≤a) (hz:∀ l:List ι, l.length≤k → ∀ i:e,(∑ j:σ',w j*|T l i j|)≤a)
local notation "s₀"=> (max 1 (Fintype.card ι:ℝ))
local notation "m₀"=>(s₀^k * Fintype.card e * a)
include H hz hw ha -- typo
lemma score (t:ℕ)(ht:t≤k)(hh:0<t)(D:ℝ)(hD:0≤D)(E:List σ→ℝ)(he:Conde F D p t E): Yarn p (fun l:List σ'=> (l.map w).prod*|commit K p t E l|) ≤ (((k:ℝ)+1)*m₀)^p*D:=by
   let s:=((k:ℝ)+1)*m₀
   induction p generalizing t E with
   | zero=> obtain ⟨t,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : t≠0); simpa only [twillz,pow_zero,one_mul,List.map_nil,List.prod_nil,commit,arco,Conde] using he -- probably `he` not dsimp
   | succ p ih=>
       obtain ⟨t,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (by omega : t≠0); let t':= t+1; let A:=s^p*D; have hA:0≤A:=by unfold A s; positivity
       let I(q:ℕ)(z:σ')(m:List ι)(i:e)(l:List σ'):= commit K p (t'-q) (parcel F m i E) l
       let J(q:ℕ)(z:σ')(m:List ι)(i:e)(l:List σ'):= w z*|T m i z| *((l.map w).prod*|I q z m i l|)
       have hx(q:ℕ)(hq:q<t') : (∑ z:σ',Yarn p fun l:List σ'=> Yarn q fun m=>∑ i:e,J q z m i l) ≤ m₀*A:=by
           have hp(z:σ') : Yarn p (fun l:List σ'=> Yarn q fun m=>∑ i:e,J q z m i l)= Yarn q (fun m=>∑ i:e,Yarn p (J q z m i)):=by rw [pool]; refine stitch q fun m _=>?_ ; exact scarves ..
           have hM(m:List ι)(hh:m.length=q)(i:e):(∑ z:σ',Yarn p (J q z m i)) ≤ a*A:=by
               have he:= he m i (by omega); rw [hh] at he
               calc
                 _ ≤ ∑ z:σ',w z*|T m i z| * A :=by refine Finset.sum_le_sum fun z _=>?_ ; unfold J; rw [sheen]; refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hw z) (abs_nonneg _)); exact ih (t'-q) (by omega) (by omega) _ he
                 _ ≤ _:=by rw [←Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hz m (by omega) i) hA
           simp_rw [hp]; rw [←scarves]
           apply le_trans (b:=Yarn q (fun m:List ι=>∑ _i:e,a*A)) (shiny q ?_) ?_
           · intro m hh; rw [Finset.sum_comm]; exact Finset.sum_le_sum fun i _=> hM m hh i
           rw [total_books,Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; refine le_trans (b:=s₀^k*((Fintype.card e:ℝ)*(a*A))) (mul_le_mul_of_nonneg_right ?_ (by positivity : 0 ≤ (Fintype.card e:ℝ)*(a*A))) ?_
           · exact (pow_le_pow_left₀ (by positivity : 0 ≤ (Fintype.card ι:ℝ)) (le_max_right 1 _) q).trans (pow_le_pow_right₀ (le_max_left ..) (hq.le.trans ht))
           exact le_of_eq (by ring)
       let f(z:σ')(l:List σ')(q:ℕ):= Yarn q fun m=>∑ i:e,J q z m i l
       have ht'(z:σ')(l:List σ')(hp:l.length=p) : ((z::l).map w).prod*|commit K (p+1) t' E (z::l)|≤∑ q∈Finset.range t',f z l q:=by
           rw [letters F K T k H ht z l hp E]; let g(q:ℕ):=(Yarn q fun j=>∑ i:e,T j i z*I q z j i l)
           let y:= (l.map w).prod; have hy:0≤y:=lust _ _ hw
           simp only [List.map_cons,List.prod_cons]; change w z*y*|∑ q∈_,g q|≤_
           refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs g (Finset.range t')) (mul_nonneg (hw z) hy)).trans ?_; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun q hq=>?_ ; unfold g; refine (mul_le_mul_of_nonneg_left (polished ..) (mul_nonneg (hw z) hy)).trans ?_; unfold f; rw [←sheen]; refine shiny _ fun m he=>?_ ; refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (mul_nonneg (hw z) hy)).trans_eq ?_; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [abs_mul]; unfold J y; ring
       rw [twilled]; refine (le_trans (Finset.sum_le_sum (g:=fun z=>Yarn p fun l=>∑ q∈ Finset.range t',f z l q) fun z _=> shiny _ (ht' z)) ?_)
       simp_rw [show ∀ z,Yarn p (fun l=>∑ q∈Finset.range t',f z l q)=∑ q∈Finset.range t',Yarn p (fun l=> f z l q) from fun z=> franje ..]; rw [Finset.sum_comm]
       refine le_trans (Finset.sum_le_sum fun q hq=> hx q (Finset.mem_range.mp hq)) ?_
       rw [Finset.sum_const,nsmul_eq_mul,Finset.card_range]; refine (mul_le_mul_of_nonneg_right (c:=((k:ℝ)+1)) ?_ (by positivity : 0 ≤ m₀*A)).trans_eq ?_
       · exact_mod_cast (Nat.le_add_right k 1|>.trans' ht : t' ≤ k+1)
       unfold A s; ring
end YM.MSbar.Measuring
