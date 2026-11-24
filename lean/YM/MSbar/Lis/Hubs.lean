import YM.MSbar.Lis.Franks
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Measuring Wave
open AnalyticBridge.VerifiedReset Native.Chart Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{a b C D:ℝ}{q p m:ℕ}
local notation "K"=>Primary n G
variable (F: List (Primary n G)→ℝ) (x j:Primary n G)
noncomputable def hits (j:Primary n G)(l:List (Primary n G)):ℝ:= if allot j l then 1 else 0
lemma same_sp (j: Primary n G)(f:G.ColorIndex→ℝ) : (∑ i:Primary n G,(if i.1=j.1 then f i.2 else 0))=∑ i,f i:=by
    unfold Primary; rw [Fintype.sum_prod_type,Finset.sum_eq_single_of_mem j.1 (Finset.mem_univ _)]; · simp
    intro b _ h; simp [h]
lemma hitsN(k:List (Primary n G)):0≤hits j k:=by unfold hits; split <;> norm_num
lemma counts (p:ℕ): Yarn p (hits j) = (Fintype.card G.ColorIndex:ℝ)^p:=by
    induction p with
    | zero=>rw [Yarn]; simp [hits,allot]
    | succ k ih=>
       have he (i:Primary n G) (l:List (Primary n G)):hits j (i::l)= (if i.1=j.1 then (1:ℝ) else 0)*hits j l:=by by_cases hx:i.1=j.1 <;> simp [hits,hx,allot,Ne.symm]
       rw [twilled]; simp_rw [he,sheen,ih,ite_mul,one_mul,zero_mul]; rw [same_sp j (fun _=> (Fintype.card G.ColorIndex:ℝ)^k),Finset.sum_const,nsmul_eq_mul,pow_succ]; simp only [Finset.card_univ]; ring
lemma heirs (T:List Bool)(l:List (Primary n G))(h:T.length=l.length)(hp:allot j (takeout true T l)) : Whisk.zone (Measuring.chart n G) ∅ l ⊆ Whisk.zone (Measuring.chart n G) ∅ (j::takeout false T l):=by
    intro i he; simp only [Whisk.zone,Finset.empty_union,List.mem_toFinset,List.mem_map] at he; obtain ⟨v,hv,rfl⟩:= he
    unfold Whisk.zone; rw [Finset.empty_union,List.mem_toFinset]; apply List.mem_map.mpr; obtain h'|h':= spark _ hv T h
    · exact ⟨j,List.mem_cons_self .., congrArg Prod.fst (hp v h')⟩
    exact ⟨v,List.mem_cons_of_mem _ h',rfl⟩
variable (T:List Bool)
local notation "take!"=> takeout true T
local notation "outs!"=> takeout false T
local notation "π"=> swipe (Measuring.chart n G) b p
local notation "ρ"=> tide
local notation "nG"=>(Fintype.card G.ColorIndex:ℝ)
lemma province_cap (t:List K)(hp:2≤p)(hb:0≤b): tide t * tide t ≤ swipe (Measuring.chart n G) b p t :=by
    have hh:1≤tide t:= by unfold tide; simp
    rw [← sq]; apply (pow_le_pow_right₀ hh hp).trans; change (tide t)^p ≤ (tide t)^p*Real.exp (b*dim t); exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hh) _) (Real.one_le_exp (by positivity))
-- group sum
variable (h:T.length=m)(hp:2≤p)(hb:0≤b)
include h hp hb
noncomputable def display (F:List (Primary n G)→ℝ)(x j:Primary n G)(t:List Bool)(l:List (Primary n G)):= tide (x::l)*(hits j (takeout true t (x::l))*tide [x,j]*|F (j::takeout false t (x::l))|)
local notation "V₀"=> parts false T
local notation "V₁"=> parts true T
lemma organ (hx:Yarn (parts false T+1) (fun l:List K=>|F (x::l)| *swipe (Measuring.chart n G) b p (x::l)) ≤ C)
    (ht:∀ (j:Primary n G),∀ l:List (Primary n G),l.length≤ m→ F (x::j::l)=F (j::x::l)) : (∑ j:Primary n G,Yarn m (display F x j (false::T)))≤nG^parts true T*C:=by
     let y(j:Primary n G) (l:List K):=display F x j (false::T) l
     let I(j:Primary n G)(l:List K):= |F (x::j::l)| *π (x::j::l)
     have he(j:K): Yarn m (y j) ≤ nG^V₁*Yarn V₀ (I j):=by
       rw [← counts j,← knot m T h]; refine shiny _ fun k hk=>?_ ; unfold y display; simp only [takeout, ↓reduceIte,Bool.false_eq_true]
       by_cases hg:allot j (take! k)
       · rw [show hits j _=1 from if_pos hg,one_mul,one_mul]; have hh: T.length=k.length:= by omega
         let B:= x :: j :: outs! k; have hB:ρ (x::k) ≤ ρ B:=by have hp:= heirs j T k hh hg; unfold tide; gcongr; apply intr; rw [Whisk.added,show Whisk.zone _ _ B= insert _ _ from Whisk.added ..]; exact Finset.insert_subset_insert _ hp
         have hr:tide [x,j] ≤ ρ B:= ppe x [x,j] B (by unfold B; grind)
         unfold I; rw [← ht j (outs! k) (by rw [sunset _ _ _ hh]; rw [←h]; exact part_le ..),←mul_assoc]
         exact mul_le_mul_of_nonneg_right ((mul_le_mul hB hr (by unfold tide; positivity) (by unfold tide; positivity)).trans (province_cap B hp hb)) (abs_nonneg _)|>.trans_eq (mul_comm ..)
       simp [hits,hg]
     calc
        _ ≤ ∑ j:K,nG^V₁*Yarn V₀ (I j):= Finset.sum_le_sum (fun i _=> he _)
        _ ≤ _:=by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hx (by positivity)
lemma organS (hx:∀ j:Primary n G,Yarn (parts false T) (fun l:List K=> |F (j::l)| * swipe (Measuring.chart n G) b p (j::l)) ≤ C) : (∑ j:Primary n G,Yarn m (display F x j (true::T))) ≤ nG^(parts true T+1)*C:=by
    let y(j:K)(l:List K) := display F x j (true::T) l
    have hp(j:K): Yarn m (display F x j (true::T)) ≤ if j.1=x.1 then nG^V₁*C else 0:=by
        split; next he=>
           let I(l:List K) := |F (j::l)| *π (j::l); have hI:Yarn V₀ I≤ C:= hx j
           apply le_trans _ (mul_le_mul_of_nonneg_left hI (show 0≤nG^V₁ by positivity)); rw [←counts j,← knot m T h]; apply shiny; intro l hl; unfold display; simp only [takeout, ↓reduceIte,Bool.true_eq_false]; by_cases hx:allot j (take! l)
           · rw [show hits j (x::take! l)=1 from (by unfold hits; rw [if_pos (by unfold allot; rintro i hi; rcases List.mem_cons.mp hi with hi|hi; exact hi ▸ he; exact hx i hi)]),one_mul,show hits j (take! l)=1 from if_pos hx,one_mul]; let B:=j::outs! l; have hh:T.length=l.length:=by omega
             have ha: Measuring.chart n G x=Measuring.chart n G j:=by unfold Measuring.chart; rw [he] -- orientation reversed
             have hb': tide (x::l)≤ tide B:=by unfold tide; gcongr; apply intr; rw [Whisk.added]; apply Finset.insert_subset; rw [ha]; exact Finset.mem_union_right _ (List.mem_toFinset.mpr (by simp [B])); exact heirs j T l hh hx
             have hf:tide [x,j]≤tide (j::outs! l):=by unfold tide; gcongr; apply intr; rw [Whisk.added,ha]; intro i h; simp [Whisk.zone] at h; rw [Whisk.added]; exact Finset.mem_insert.mpr (Or.inl h)
             rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right ((mul_le_mul hb' hf (by unfold tide; positivity) (by unfold tide; positivity)).trans (province_cap B hp hb)) (abs_nonneg _)|>.trans_eq (mul_comm ..)
           unfold hits; rw [if_neg,if_neg hx]; · simp
           intro hg; exact hx (fun i hi=>hg i (List.mem_cons_of_mem _ hi))
        next he=>
          apply le_trans _ (le_of_eq (Whisk.spool (ι:=K) m)); apply shiny; intro l hl; unfold display; rw [show takeout true _ _ = x::take! l from rfl,show hits j (x :: _) = 0 from if_neg (fun h=>he (h _ (List.mem_cons_self ..)))]; simp only [zero_mul,mul_zero,le_refl]
    refine le_trans (Finset.sum_le_sum fun i _=> hp i) (le_of_eq ?_); rw [same_sp x (fun _=> nG^V₁*C),Finset.sum_const,nsmul_eq_mul]; rw [Finset.card_univ,pow_succ]; ring
end YM.MSbar.Lis
