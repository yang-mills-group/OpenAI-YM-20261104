import YM.OPE.Compatible.Lake.Depot
/-! Isolation, converse lane. Costs as multiplicative slack at actual step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot ContinuousLinearMap
open scoped Topology Classical BigOperators
variable {d:ℕ} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]
local notation "I"=> Fin (d+1)
namespace Split
variable {B η u:ℝ}{R U: Dock E≃L[ℂ]Dock E} (H: Split B η u R U)
variable (hb:16 ≤ B)(he:1 ≤ η)(hg: η≤3/2)(hu:u≤ ice d)
open Finset
variable (p:Dock E→L[ℂ]ℂ){e:ℕ}
local notation "Q"=> (U.toContinuousLinearMap)
local notation "A"=> (R.toContinuousLinearMap)
include H he hb
lemma modal (i:I): ‖track p i‖*(B^(d-i.val)/η) ≤ ‖(track p i).comp (route Q i i)‖:=by
    by_cases hv:0<B; swap
    · -- include hb
      -- if not pos, h.diag bound eta with B^ exp => B^ exp nonneg; prove nonpos case. easier include hb
      exact False.elim (not_lt_of_ge (not_lt.mp hv) (by linarith))
    have hq:= teamTracks U _ _ rfl rfl H.heading H.oppose i
    let f:= track p i; let q:= route U.symm.toContinuousLinearMap i i
    have hs: f=(f.comp (route Q i i)).comp q:=by change f=f.comp ((route Q i i).comp q); rw [show (route Q i i).comp q=_ from hq]; simp
    have ht : ‖f‖ ≤ ‖f.comp (route Q i i)‖ * ((B^(d-i.val))⁻¹ * η):= by
       nth_rw 1 [hs]; exact (opNorm_comp_le ..).trans (mul_le_mul_of_nonneg_left (H.reverse i) (norm_nonneg _))
    field_simp at ht ⊢; linarith only [ht]

lemma lowGrow (hle:e≤d) : courtyard p e *(B^(d-e+1)/η) ≤ courtyard (p.comp Q) e + ice d*d*income p + ice d*income p:=by
   have he':0<η :=by linarith
   have h (i:I)(hi:i.val<e) : ‖track p i‖*(B^(d-e+1)/η) ≤ ‖track (p.comp Q) i‖ + ice d*income p:=by
      have hM:= H.modal hb he p i
      have ht : B^(d-e+1) ≤ B^(d-i.val):=pow_le_pow_right₀ (by linarith) (by omega)
      apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ht he'.le) (norm_nonneg _)).trans (hM.trans _)
      let c(j) := (track p j).comp (route Q j i); let u:=univ.erase i; let t:=(∑ j∈u,c j)
      rw [tracks,← add_sum_erase _ c (mem_univ i)]
      have hb : ‖c i‖≤ ‖c i+t‖+‖t‖:=by nth_rw 1 [← add_sub_cancel_right (c i) t]; exact norm_sub_le ..
      apply hb.trans; apply add_le_add le_rfl; apply (norm_sum_le ..).trans
      unfold income; rw [mul_sum]; apply (sum_le_sum (g:=fun i=> ice d * ‖track p i‖) (fun j hj=>?_)).trans (sum_le_sum_of_subset_of_nonneg (erase_subset i univ) (fun i _ _=> mul_nonneg (by unfold ice; positivity) (norm_nonneg _)))
      next j hj=>
         change ‖(track p j).comp (route Q j i)‖ ≤ _; rw [mul_comm]; exact (opNorm_comp_le ..).trans (mul_le_mul_of_nonneg_left (H.side j i (ne_of_mem_erase hj)) (norm_nonneg _))
   unfold courtyard; rw [sum_mul]; let a:= univ.filter (fun i:I=> i.val<e)
   apply (sum_le_sum (fun i hi=> h i ((mem_filter.mp hi).2))).trans
   rw [sum_add_distrib,sum_const,nsmul_eq_mul]; rw [add_assoc]; apply add_le_add le_rfl
   have hz:= sum_nonneg (s:=univ) (fun i _ => norm_nonneg (track p i)); refine (mul_le_mul_of_nonneg_right (show (a.card:ℝ)≤((d+1:ℕ):ℝ) from ?_) (mul_nonneg (by unfold ice; positivity) hz)).trans_eq ?_
   · exact_mod_cast (card_le_card (subset_univ a)).trans_eq (show (univ:Finset I).card=d+1 from by simp)
   push_cast; ring
include hu hg
lemma scrum (hle:e≤d) (hP:shelf p e<courtyard p e): courtyard p e*(B^(d-e)*Real.sqrt B) ≤ courtyard (p.comp A) e ∧ shelf (p.comp A) e<courtyard (p.comp A) e:=by
   have hc:0≤ courtyard p e:= Finset.sum_nonneg fun _ _=>norm_nonneg _; have hz:0≤ shelf p e:= sum_nonneg fun _ _=>norm_nonneg _; have ha:=lt_of_le_of_lt hz hP; cases e with
   | zero=> simp [courtyard] at ha
   | succ e =>
    let E0 := e+1; let n:ℝ:= (d+1:ℕ); have hn : 0<n:=by unfold n; positivity
    have hv' : n * ice d=1/500:=by change n*(500*n)⁻¹=_; field_simp
    have ht : courtyard (p.comp Q) E0 ≤ courtyard (p.comp A) E0 + income (p.comp A-p.comp Q):=by
      have hi i: ‖track (p.comp Q) i‖ ≤ ‖track (p.comp A) i‖ + ‖track (p.comp A-p.comp Q) i‖:=by rw [show track (p.comp A-p.comp Q) i = track (p.comp A) i-track (p.comp Q) i by ext1;rfl,norm_sub_rev]; linarith [norm_sub_norm_le (track (p.comp Q) i) (track (p.comp A) i)]
      have hq : courtyard (p.comp Q) E0 ≤ courtyard (p.comp A) E0 + courtyard (p.comp A-p.comp Q) E0:= by unfold courtyard; rw [← sum_add_distrib]; apply sum_le_sum fun i _=> hi i
      exact hq.trans (add_le_add_right (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=> norm_nonneg _)) _)
    let L:=courtyard p E0;let P:=shelf p E0
    have hp : income p ≤ 2*L:= by rw [field_merger p E0]; change P+L≤ _; linarith
    have hi:= H.incomePrice p
    have hl:= H.lowGrow hb he p hle
    have hx : n*u≤1/500:= hv' ▸ mul_le_mul_of_nonneg_left hu hn.le
    let x:=B^(d-E0); have hx':1 ≤ x:= one_le_pow₀ (by linarith)
    change L*(B^_/η) ≤ _ at hl; rw [pow_succ] at hl
    have hL:(income p)*(n*u) ≤ L * (1/250):= calc
       _ ≤ 2*L*(1/500):=mul_le_mul hp hx (mul_nonneg hn.le H.fuelNN) (mul_nonneg (by norm_num) hc)
       _ = _:=by ring
    have heL :ice d*d*income p+ice d*income p = income p*(n*ice d):=by unfold n; push_cast; ring
    have hs : L*(x*Real.sqrt B) ≤ courtyard (p.comp A) E0:=by
       rw [add_assoc,heL,hv'] at hl
       change L*(x*B/η)≤ _ at hl
       have hC: L ≤ L*x:= le_mul_of_one_le_right hc hx'; have Hx:= Real.sq_sqrt (show 0 ≤ B by linarith); have Hv:=Real.sqrt_nonneg B; have Hf : 4 ≤ Real.sqrt B := by nlinarith only [hb,Hv,Hx]
       have he' :0<η:=by linarith
       have hm: x*(Real.sqrt B+1) ≤ x*B/η:=by
          rw [le_div_iff₀ he']; have hZ : (Real.sqrt B+1)*η ≤ B:=by nlinarith only [Hx,Hf,mul_le_mul_of_nonneg_left hg (show 0 ≤ Real.sqrt B+1 by linarith only [Hv])]
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hZ (by linarith only [hx'])
       linarith only [hl,hC,mul_le_mul_of_nonneg_left hm hc,hi,hL,ht,hp, hc]
    refine ⟨hs,(lt_of_lt_of_le ?_ hs)⟩
    have hR:= H.spike hb he E0 p
    have hf: 4 ≤ Real.sqrt B := by nlinarith only [Real.sq_sqrt (show 0 ≤ B by linarith),hb, Real.sqrt_nonneg B]
    have hB:=mul_le_mul_of_nonneg_left hg (show 0 ≤ x by linarith only [hx']);change shelf (p.comp A) (e+1)<L*(x* _) -- parse
    have hJ : P*(x*η) ≤ L*(x*η):=mul_le_mul_of_nonneg_right hP.le (mul_nonneg (by linarith only [hx']) (by linarith))
    linarith only [hR,hL,hJ,mul_le_mul_of_nonneg_left hB hc,mul_le_mul_of_nonneg_left hf (mul_nonneg hc (show 0≤ x by linarith only [hx'])),mul_le_mul_of_nonneg_left hx' hc,ha]
end Split
end YM.OPE.Lake
