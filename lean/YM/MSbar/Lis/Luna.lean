import YM.MSbar.Lis.Province
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk Push Uniform Lattice RG
open scoped Topology BigOperators ContDiff Classical
variable {σ : Type}[Fintype σ]{n:Side}
variable {t:σ→Site n}{k p m q N:ℕ}{a w B C:ℝ}{F:Positions σ→ℝ}
open Measuring Metric Set
local notation "bond₁"=>swipe t a p
-- extension of lower orders.
namespace JetTab
variable (h:JetTab t a p w (Metric.closedBall 0 w) F (m+1) B) (hp:JetTab t a p w {0} F m C) (hw:0<w)(ha:0≤a)
variable (hm:m+2≤k)(hf:∀ x∈Metric.closedBall 0 w, ContDiffAt ℝ k F x)
include h hp hw ha hm hf
lemma plume : JetTab t a p w (Metric.closedBall 0 w) F m (B+C):=by
    obtain ⟨hB,g,hg,hG⟩:=h; obtain ⟨hC,f,hf',hF⟩:=hp
    let X(i:List σ):=∑ z:σ,g (i++[z]); let S : Set (Positions σ):= Metric.closedBall 0 w
    refine ⟨add_nonneg hB hC,fun i=> X i+f i,fun i hi=>?_ ,fun i=>?_⟩
    · let b := w^(m+1); let c := w^(m+1+1); let l:= i.map (@bolt σ)
      have hb:0<b:= pow_pos hw _; have hc:0 < c:=pow_pos hw _
      have hL(z:σ) : (i++[z]).length=m+1+1:=by simp [hi]
      let f'(x:Positions σ) := buoy F x i; have h0:0≤X i:= Finset.sum_nonneg fun z _=> hg _ (hL z)|>.1
      refine ⟨add_nonneg h0 (hf' i hi).1,fun x hx=>?_⟩
      have hl:l.length+1=m+1+1:=by unfold l; simp [hi]
      have hf0(x)(hx:x∈S): ContDiffAt ℝ (↑(1:ℕ)) f' x:=(smooth k 1 l (hf x hx) (by omega)) -- lambda eta with i argument
      have hx' (x:Positions σ)(he:x∈ S): ‖fderiv ℝ f' x‖≤ X i/c:=by
          let K:= fderiv ℝ f' x; have hp(z:σ): K (bolt z)=buoy F x (i++[z]):=by
              unfold buoy; rw [List.map_append,List.map_cons,List.map_nil,fore k (hf x he) _ _ (by change l.length<k; omega)];rfl
          refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg h0 hc.le) fun v=> ?_
          nth_rw 1 [spiral v]; rw [map_sum]; apply (norm_sum_le ..).trans; refine (Finset.sum_le_sum (g:=fun z:σ=> g (i++[z])/c*‖v‖) ?_).trans_eq ?_
          · intro z _; rw [map_smul,norm_smul, mul_comm ‖v z‖, show K _= _ from hp z]; apply mul_le_mul; exact le_div_iff₀ hc|>.mpr (hg _ (hL z)|>.2 x he); exact norm_le_pi_norm v z; exact norm_nonneg _; exact div_nonneg (hg _ (hL z)|>.1) hc.le
          rw [←Finset.sum_mul,← Finset.sum_div]
      have hx0:0∈S:=Metric.mem_closedBall_self hw.le
      have he:|f' x-f' 0| *b ≤ X i:=by
          have he:= Convex.norm_image_sub_le_of_norm_fderiv_le (fun i hi=>(hf0 i hi).differentiableAt (by norm_num)) hx' (convex_closedBall 0 w) hx0 hx
          have hg1:‖x‖≤ w:= mem_closedBall_zero_iff.mp hx; rw [sub_zero] at he
          apply (mul_le_mul_of_nonneg_right (he.trans (mul_le_mul_of_nonneg_left hg1 (div_nonneg h0 hc.le))) hb.le).trans_eq; unfold b c; rw [pow_succ w (m+1)]; field_simp
      change |f' x| *b ≤ _; calc
          _ ≤ (|f' x-f' 0| +|f' 0|)*b:= mul_le_mul_of_nonneg_right (by simpa only [sub_add_cancel] using abs_add_le (f' x-f' 0) (f' 0)) hb.le
          _ ≤ _:=by rw [add_mul]; exact add_le_add he (hf' i hi|>.2 _ (mem_singleton 0)) -- simp
    change Yarn m (fun l=>(X (i::l)+f (i::l))*bond₁ (i::l))≤ _; simp_rw [add_mul,pockets]; refine add_le_add ?_ (hF i); unfold X
    simp_rw [Finset.sum_mul]; rw [scarves]; refine le_trans ?_ (hG i)
    let f(k:List σ):=g (i::k)*bond₁ (i::k); rw [show Yarn (m+1) _=∑ z:σ,Yarn m (fun L:List σ=> f (L++[z])) from (bothEnds ..).symm]; apply Finset.sum_le_sum; intro z _; refine shiny _ fun l hl=>?_ ; apply mul_le_mul_of_nonneg_left; refine w_more (intr ?_) ha _; unfold zone; gcongr; simp [List.map_append]; grind
structure RangeB (t:σ→Site n)(p:ℕ)(a w:ℝ)(F:Positions σ→ℝ)(m:ℕ)(C:ℝ) :Prop where
   peak : ∀ i≤m, JetTab t a p w (if i<4 then {0} else Metric.closedBall 0 w) F i C
-- requires m≥4.Stages.Enter.
include ha hw hf
omit hp hm h
lemma levelAll (hR: RangeB t p a w F N B)(hP:4≤ N)(he:N+1 ≤ k)(j:ℕ)(hh:j≤N): JetTab t a p w (Metric.closedBall 0 w) F j (5*B):=by
    have hp:0≤B:= (hR.peak _ hP).1
    have hv(i)(hh:i≤4): JetTab t a p w (Metric.closedBall 0 w) F i ((5-(i:ℝ))*B):=by
        induction hh using Nat.decreasingInduction with
        | self=> convert hR.peak 4 hP using 1 <;> norm_num
        | of_succ i hi ih=>
           apply JetTab.cast (plume ih (?_:JetTab t a p w {0} F i B) hw ha (show i+2 ≤ k from by omega) hf) _ Subset.rfl
           · simpa only [if_pos hi] using hR.peak i (by omega)
           · push_cast; apply le_of_eq; ring
    by_cases h:j≤4
    · exact (hv j h).cast (mul_le_mul_of_nonneg_right (by linarith only [Nat.cast_nonneg (α:=ℝ) j]) hp) Subset.rfl
    apply (hR.peak j hh).cast (by linarith only [hp]); rw [if_neg (by omega)]
end JetTab
end YM.MSbar.Lis
