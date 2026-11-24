import YM.MSbar.CrossH.Dough
import YM.MSbar.Lis.Pipes
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.CrossH
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice
open scoped Topology BigOperators ContDiff Classical
variable {σ ι β X:Type}[Fintype σ][DecidableEq σ][Fintype ι][DecidableEq ι][NormedAddCommGroup X][NormedSpace ℝ X]
open Polynomial MvPolynomial Matrix Rolling
local notation "P"=> Cacao.Pot σ
local notation "Ξ"=>Positions σ
local notation "∆"=>PowerSeries.coeff
variable {n:Side} (l:σ→Site n){L : ι→Site n}{a b w t u B:ℝ}{f g:Cacao.Pot σ}{m s k r v p:ℕ}
-- support template window. Grain incidence Bounds cards.S Use Gate.S templates locality incl. Need total scaling uProof.
variable {B :ℝ}
noncomputable def curbL (l:σ→Site n)(x:Site n)(v:ℕ): Finset σ:= Finset.univ.filter fun i=> separation (l i) x ≤ v
noncomputable def rugL (a t:ℝ)(s:ℕ)(B:ℕ)(i:ℕ)(A:ℕ):= (A:ℝ)^i*(t*liftW a s (2*B))
noncomputable def pulse {ι:Type} (s:Finset ι)(T:List ι):ℝ:=if ∀i∈T,i∈s then 1 else 0
lemma spooler (s: Finset σ) (t:ℕ) : Yarn t (pulse s) = (s.card:ℝ)^t:=by
   induction t with
   | zero=> rw [Yarn]; simp [pulse]
   | succ t ih=>
      rw [twilled]; have hp(v:σ)(l:List σ): pulse s (v::l)= if v∈s then (1:ℝ)*pulse s l else 0 * pulse s l:=by by_cases he:v∈s<;> simp [he,pulse];
      simp_rw [hp,←ite_mul,sheen,ih,ite_mul,one_mul,zero_mul]; rw [Finset.sum_ite_mem,Finset.sum_const,nsmul_eq_mul]; -- check
      simp [pow_succ,mul_comm]
lemma cols (B:ℕ)(F:Finset ι)(w:ι→ℝ)(f:ι→ℝ)(h:∀ i,(0<w i)→ i∈F)(hf:∀ i,w i ≤ f i) (hp:∀ i,f i≤t): (∑ i:ι, w i) ≤ (F.card:ℝ)*t:=by
    let g(i:ι):= if i∈ F then t else 0
    apply le_trans (b:=∑ i:ι,g i) (Finset.sum_le_sum ?_) (le_of_eq ?_); swap; · unfold g; rw [Finset.sum_ite_mem,Finset.sum_const,nsmul_eq_mul]; simp
    intro i hi; by_cases hx:i∈F; unfold g;rw [if_pos hx]; exact (hf i).trans (hp i)
    unfold g; rw [if_neg hx]; by_contra! ht; exact hx (h i ht)
structure Lumber (l:σ→Site n)(x:Site n)(B:ℕ)(f:Positions σ→ℝ)(i:ℕ)(D:ℝ) :Prop where
    zero :0≤ D
    smooth : ContDiffAt ℝ (↑(i+1:ℕ)) f 0
    cash (k:List σ)(h:k.length=i+1): |buoy f 0 k| ≤ D
    pace (k:List σ)(h:k.length=i+1) (hh:buoy f 0 k ≠0): ∀ j∈k,j∈ curbL l x B
variable {F:Positions σ→ℝ} (x:Site n){q M v N:ℕ}
variable (h:Lumber l x v F q t)(ha:0≤a)
include h ha
lemma vaultB (hK:(curbL l x v).card≤M)(j:σ): Yarn q (fun L:List σ=> |buoy F 0 (j::L)| *swipe l a s (j::L)) ≤ if j∈curbL l x v then rugL a t s v q M else 0:=by
    let C:=curbL l x v; have hC:(C.card:ℝ) ≤ M:=by exact_mod_cast hK
    have ht:=h.zero; let Z:= liftW a s (2*v); have hz:0 < Z:=wpos ..
    let H(j:σ)(T:List σ):= |buoy F 0 (j::T)| *swipe l a s (j::T)
    change Yarn q (H j) ≤ _
    split; next hv=>
       apply le_trans (b:=Yarn q fun L:List σ=> pulse C L*(t*Z)) (shiny q ?_) ?_
       · intro i hi; by_cases hx:buoy F 0 (j::i)=0
         · unfold H; rw [hx,abs_zero,zero_mul]; unfold pulse; split <;> positivity
         have hh:(j::i).length=q+1:=by simp only [List.length_cons,hi]
         have hp:=h.pace (j::i) hh hx; rw [pulse,if_pos (fun i hx=> hp i (List.mem_cons_of_mem _ hx)),one_mul]; refine mul_le_mul (h.cash _ hh) ?_ (effect ..|>.le) ht
         apply w_more _ ha; apply Whisk.yard; intro i' he j' hs
         have hh(b:Site n)(hv:b∈zone l ∅ (j::i)): separation b x ≤ v:=by obtain ⟨j,h₀,h⟩:= List.mem_map.mp (List.mem_toFinset.mp (show _ from (by simpa only [zone,Finset.empty_union] using hv))); rw [← h]; exact Finset.mem_filter.mp (hp j h₀)|>.2
         have h₁:=hh i' he; have h₂:=hh j' hs; apply (separation_triangle i' x j').trans; rw [separation_comm x]; omega
       rw [poker,spooler]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hC q) (by positivity)
    next he=>
       refine le_trans ?_ (spool (ι:=σ) q|>.le); apply shiny; intro i hi; have hp:buoy F 0 (j::i)=0:=by by_contra hv; exact he (h.pace _ (by simp [hi]) hv _ (List.mem_cons_self ..))
       unfold H; rw [hp,abs_zero,zero_mul]
omit h
variable (Z:ι→ Site n)(F:ι→ Cacao.Pot σ)(hp:∀ i:ι,Lumber l (Z i) v (clue (F i)) q t)
include hp
lemma logHome (he:∀ x:Site n,(curbL l x v).card≤ M)(hz:∀ x:Site n,(curbL Z x v).card≤ N)(ht:0≤ t)(i:σ) : cog l a s (∑ j:ι,F j) q i ≤ N *rugL a t s v q M:=by
    unfold cog; rw [_root_.map_sum]; let A:=rugL a t s v q M; have hA:0≤A:= mul_nonneg (by positivity : 0 ≤ (M:ℝ)^q) (mul_nonneg ht (wpos ..|>.le)); apply (lump.totals ..).trans
    let Q(j:ι):= if j∈curbL Z (l i) v then A else 0; calc
       _ ≤ ∑ j,Q j:= by
              refine Finset.sum_le_sum fun j _=>?_ ; have hx: (i∈curbL l (Z j) v) ↔ (j∈curbL Z (l i) v):=by simp [curbL,separation_comm (l i)] -- inspect instance
              unfold Q; simp only [← hx]; exact ((scored (F j) i).symm.trans_le (vaultB l _ (hp j) ha (he _) i))
       _ ≤ _:= by simp only [Q, Finset.sum_ite_mem, Finset.sum_const,nsmul_eq_mul]; simp; gcongr; exact hz _
end YM.MSbar.CrossH
