import YM.OPE.Compatible.Lake.Iso
/-!
# Matrix price. Common stencil, across E labels

Pi estimates on fixed-grade blocks after rescaling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot ContinuousLinearMap
open scoped Topology Classical BigOperators
variable {d:ℕ} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]
local notation "I"=> Fin (d+1)
-- floor softness by cardinal. For low region slack take L>=16 eventual? can request tend L; indeed logCost implies via columns. Use literal L≥8 eventually.
variable (d) in
abbrev ice := (500*((d+1:ℕ):ℝ))⁻¹
structure Split (B η u:ℝ)(R U: Dock E≃L[ℂ]Dock E):Prop where
    -- U model, R actual. B>=8 η inflated price factor both ways, u=error.
    -- model triangular
    heading : team U.toContinuousLinearMap
    oppose : team U.symm.toContinuousLinearMap
    advance (i:I): ‖route U.toContinuousLinearMap i i‖ ≤ B^(d-i.val)*η
    reverse (i:I): ‖route U.symm.toContinuousLinearMap i i‖ ≤ (B^(d-i.val))⁻¹*η
    side (i j:I):i≠j→ ‖route U.toContinuousLinearMap i j‖ ≤ ice d
    slide (i j:I):i≠j→ ‖route U.symm.toContinuousLinearMap i j‖ ≤ ice d
    drift : ‖R.toContinuousLinearMap-U.toContinuousLinearMap‖ ≤ u
    vanish : ‖R.symm.toContinuousLinearMap-U.symm.toContinuousLinearMap‖ ≤ u
abbrev price (d:ℕ)(b u:ℝ):ℝ:= b+2*((d+1:ℕ):ℝ)*u
namespace Split
variable {B η u:ℝ}{R U: Dock E≃L[ℂ]Dock E} (H: Split B η u R U)
variable (hb:16 ≤ B)(he:1 ≤ η)(hg: η≤3/2)(hu:u≤ ice d)
include H
lemma fuelNN :0≤ u:= (norm_nonneg _).trans H.drift
include hb he
-- column contraction for inverse tri with ε
open Finset
lemma inverses (i:I) : ∑ j:I, ‖route (R.symm.toContinuousLinearMap) j i‖ ≤ price d η u := by
   let T:= U.symm.toContinuousLinearMap; let X:= R.symm.toContinuousLinearMap; let Y:= X-T
   have hb' : 0 < B:=by linarith
   have hj (j:I): route X j i=route Y j i+route T j i:=by unfold Y; rw [tollDiff]; abel
   have ha (j:I): ‖route Y j i‖≤u:= (tolls Y ..).trans H.vanish
   have hC := add_le_add_left (Finset.sum_le_sum (g:=fun j=>u+‖route T j i‖) (s:=Finset.univ) (fun j _=> show ‖route X j i‖ ≤ _ by rw [hj j]; exact (norm_add_le ..).trans (add_le_add (ha _) le_rfl))) 0
   simp only [add_zero,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin] at hC
   change ∑ j:I, ‖route X j i‖ ≤ _
   apply hC.trans; rw [← add_sum_erase _ (fun j=> ‖route T j i‖) (mem_univ i)]
   let n:ℝ := (d+1:ℕ)
   have hh:0<n:=by unfold n; positivity
   by_cases h: i.val=d
   · have hx: ∑ j∈univ.erase i,‖route T j i‖ = 0 := sum_eq_zero fun j hj=> by
         have hv:= ne_of_mem_erase hj; have hw:j < i:=by apply lt_of_le_of_ne _ hv; change j.val ≤ i.val; omega
         change ‖route U.symm.toContinuousLinearMap j i‖=0; rw [H.oppose _ _ hw,norm_zero]
     rw [hx]; have ha:= H.reverse i; simp only [h,Nat.sub_self,pow_zero,inv_one,one_mul] at ha
     change n*u+(‖route T i i‖+0)≤ η + 2*n*u; linarith only [ha,mul_nonneg hh.le H.fuelNN]
   have hi:= i.isLt; have hw: B ≤ B^(d-i.val):=by nth_rw 1 [← pow_one B]; exact pow_le_pow_right₀ (by linarith) (by omega)
   let a:= ∑ j∈ (univ.erase i), ‖route T j i‖
   have hv': a ≤ n * ice d:=by
      apply (sum_le_sum (fun j hj=> H.slide j i (ne_of_mem_erase hj))).trans; rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right ?_ (by unfold ice; positivity); unfold n; exact_mod_cast (card_le_card (erase_subset _ _)).trans_eq (show (Finset.univ:Finset I).card=d+1 from by simp)
   have hd := H.reverse i; change n*u+(‖route T i i‖+a) ≤ η + 2*n*u
   have hy:n*ice d=1/500:=by change n*(500*n)⁻¹= _; field_simp
   rw [hy] at hv'
   have hW:= mul_le_mul_of_nonneg_right (inv_anti₀ (by norm_num: (0:ℝ)<16) (hb.trans hw)) (show 0≤η by linarith); change ‖route T i i‖ ≤ _ at hd
   linarith only [hd,hW,hv',mul_nonneg hh.le H.fuelNN,he]
lemma purchases (v:Dock E) : berth (R.symm v) ≤ berth v *price d η u:=by
   unfold berth; let q:= R.symm.toContinuousLinearMap; change ∑ i:I, ‖q v i‖ ≤ _; calc
     _ ≤ ∑ i:I,∑ j:I,‖route q i j‖ * ‖v j‖:= sum_le_sum (fun i _=> by rw [routed]; exact (norm_sum_le ..).trans (sum_le_sum fun _ _=> le_opNorm ..))
     _ ≤ _:=by rw [sum_comm,sum_mul]; apply sum_le_sum; intro i _; rw [← sum_mul,mul_comm]; exact mul_le_mul_of_nonneg_left (H.inverses hb he i) (norm_nonneg _)
end Split
end YM.OPE.Lake
