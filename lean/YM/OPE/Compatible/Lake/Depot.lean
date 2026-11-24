import YM.OPE.Compatible.Lake.Growth
/-!
# Isolation lemma. Low mass versus high mass; high replacement growth without e-step prefactor from strictly offgrade replenishment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot ContinuousLinearMap
open scoped Topology Classical BigOperators
variable {d:ℕ} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]
local notation "I"=> Fin (d+1)
abbrev courtyard (p:Dock E→L[ℂ]ℂ)(e:ℕ):= ∑ i:I with i.val<e,‖track p i‖
abbrev shelf (p:Dock E→L[ℂ]ℂ)(e:ℕ):= ∑ i:I with e ≤ i.val,‖track p i‖
lemma field_merger (p:Dock E→L[ℂ]ℂ)(e:ℕ): income p=shelf p e+courtyard p e:=by
    unfold shelf courtyard income; symm; rw [show (Finset.univ.filter (fun i:I=> i.val<e))=Finset.univ.filter (fun i:I=>¬ e ≤ i.val) by simp]; exact Finset.sum_filter_add_sum_filter_not ..
lemma row_orderPrice (p q:Dock E→L[ℂ]ℂ)(e:ℕ): shelf p e ≤ shelf q e + income (p-q):=by
    have hj(i:I): ‖track p i‖≤‖track q i‖+‖track (p-q) i‖:= by apply le_trans (b:=‖track q i + track (p-q) i‖) _ (norm_add_le ..); apply le_of_eq; congr 1; rw [show track (p-q) i= track p i-track q i by ext1;rfl]; abel
    have h': shelf p e ≤ shelf q e+shelf (p-q) e:=by unfold shelf; rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun j _=>hj j
    rw [field_merger (p-q) e]; apply h'.trans; have hc : 0≤ courtyard (p-q) e:= Finset.sum_nonneg fun _ _=> norm_nonneg _; linarith
namespace Split
variable {B η u:ℝ}{R U: Dock E≃L[ℂ]Dock E} (H:Split B η u R U)
variable (hb:16 ≤ B)(he:1 ≤ η)(hg: η≤3/2)(hu:u≤ ice d)
include H
open Finset
lemma incomePrice (p:Dock E→L[ℂ]ℂ) : income (p.comp R.toContinuousLinearMap-p.comp U.toContinuousLinearMap) ≤ income p *(((d+1:ℕ):ℝ)*u):=by
   apply (boardRowTicket _).trans; rw [show _-_ = p.comp (R.toContinuousLinearMap-U.toContinuousLinearMap) from Eq.symm (comp_sub ..),mul_left_comm]
   refine mul_le_mul_of_nonneg_left ((opNorm_comp_le ..).trans (mul_le_mul (boardRow p) H.drift (norm_nonneg _) (sum_nonneg fun _ _=>norm_nonneg _))) (by positivity : (0:ℝ)≤ ((d+1:ℕ):ℝ))
-- pure model estimate
include hb he
lemma high_column (e:ℕ) (i:I) (hi:e ≤ i.val) : (∑ j:I with e ≤ j.val, ‖route U.toContinuousLinearMap i j‖) ≤ B^(d-e)*η:=by
   let s:= univ.filter (fun j:I=>e ≤ j.val); let P:= U.toContinuousLinearMap
   change ∑ j∈s, ‖route P i j‖ ≤ _; rw [← add_sum_erase s (fun j=>‖route P i j‖) (mem_filter.mpr ⟨mem_univ _,hi⟩)]
   let n:ℝ := (d+1:ℕ); have hn:0<n:=by unfold n; positivity
   have hC:= H.advance i; change ‖route P i i‖≤_ at hC
   by_cases h: i.val=e
   · have he : ∑ j∈s.erase i, ‖route P i j‖=0:= sum_eq_zero fun j hj=> by
        have he : i < j:= by
            apply lt_of_le_of_ne _ (ne_of_mem_erase hj).symm; change i.val≤j.val; rw [h]; exact (mem_filter.mp (mem_of_mem_erase hj)).2
        rw [show route P i j=0 from H.heading _ _ he,norm_zero]
     rw [he,add_zero]; simpa only [h] using hC
   have hp: (∑ j∈s.erase i, ‖route P i j‖) ≤ n*ice d:=by
      apply (sum_le_sum (fun j hj=> H.side i j (ne_of_mem_erase hj).symm)).trans; rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right ?_ (by unfold ice; positivity); unfold n; exact_mod_cast (card_le_card (subset_univ (s.erase i))).trans_eq (show (univ:Finset I).card=d+1 from by simp)
   have hS:n*ice d=1/500:=by change n*(500*n)⁻¹=_; field_simp
   rw [hS] at hp
   have hv : 1 ≤ B:=by linarith
   have hz : B^(d-i.val)*B ≤ B^(d-e):=by rw [← pow_succ]; apply pow_le_pow_right₀ hv; omega
   have hx : 1 ≤ B^(d-i.val)*η := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hv) he
   linarith only [hC,hp,mul_le_mul_of_nonneg_right hz (show 0≤η by linarith), hx,mul_le_mul_of_nonneg_left hb (show 0 ≤ B^(d-i.val)*η by linarith only [hx])]
lemma highRight (e:ℕ) (p:Dock E→L[ℂ]ℂ) : shelf (p.comp U.toContinuousLinearMap) e ≤ shelf p e*(B^(d-e)*η):=by
   unfold shelf; let s:= univ.filter (fun i:I=> e ≤ i.val); let P:= U.toContinuousLinearMap
   change ∑ i∈s, ‖track (p.comp P) i‖ ≤ _; calc
      _ ≤ ∑ i∈s,∑ j∈s, ‖track p j‖ * ‖route P j i‖:=by
         apply sum_le_sum; intro i hi; rw [tracks]; apply (norm_sum_le ..).trans; apply (sum_le_sum (fun j _=> opNorm_comp_le (track p j) (route P j i))).trans_eq; symm; apply sum_subset (subset_univ s); intro j _ hj; have hx:e ≤ i.val:= (mem_filter.mp hi).2; rw [show route P j i=0 from H.heading _ _ (by refine lt_of_lt_of_le (α:=ℕ) (lt_of_not_ge ?_) hx; exact fun hh=> hj (mem_filter.mpr ⟨mem_univ _,hh⟩)),norm_zero,mul_zero]
      _ ≤ _:=by rw [sum_comm,sum_mul]; apply sum_le_sum; intro i hi; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (H.high_column hb he e i (mem_filter.mp hi|>.2)) (norm_nonneg _)
lemma spike (e:ℕ)(p:Dock E→L[ℂ]ℂ): shelf (p.comp R.toContinuousLinearMap) e ≤ shelf p e*(B^(d-e)*η)+ income p *(((d+1:ℕ):ℝ)*u):=
   (row_orderPrice (p.comp _) (p.comp U.toContinuousLinearMap) e).trans (add_le_add (H.highRight hb he e p) (H.incomePrice p))
lemma spikes (e:ℕ)(p:Dock E→L[ℂ]ℂ)(ht:courtyard p e ≤ shelf p e): shelf (p.comp R.toContinuousLinearMap) e ≤ shelf p e*(B^(d-e)* price d η u):=by
   apply (H.spike hb he e p).trans
   let a:= shelf p e;let b:= ((d+1:ℕ):ℝ)*u;let x:=B^(d-e)
   have ha : 0 ≤ a:= Finset.sum_nonneg fun _ _=> norm_nonneg _;have hv:0 ≤ b:=mul_nonneg (Nat.cast_nonneg _) H.fuelNN; have hu: 1 ≤ x := one_le_pow₀ (by linarith)
   have he' :income p≤ 2*a:=by rw [field_merger p e]; change a+_≤ _; linarith
   change _≤ _*(x*(η+_)); rw [mul_assoc 2]; change _ ≤ a*(x*(η+2*b)); change a*(x*η)+income p*b ≤ _; linarith only [mul_le_mul_of_nonneg_right he' hv,mul_le_mul_of_nonneg_right hu (mul_nonneg ha hv)]
end Split
end YM.OPE.Lake
