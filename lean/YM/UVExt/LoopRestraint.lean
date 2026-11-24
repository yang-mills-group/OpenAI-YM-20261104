import YM.UVExt.LoopShift
import YM.UVExt.LoopBill

/-! Affine-null price (α kinetic drift lives separately). -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open Function Filter Laurent Lattice RG Wilson Precision Exterior Bid Matrix Set
open scoped Classical Topology ContDiff BigOperators
variable {G : Gauge} {n : Side} (v : fieldDir G n 1)
private lemma mul_twins (a b : Fin 2→ℝ) (K₁ D T : ℝ) (hK : 0≤K₁) (ht : 0≤T) (hD : 0≤D)
    (hS : Fin 2→ℝ) (hP : ∀ i,0≤hS i) (h : ∀ i, |a i|≤K₁*T) (h' : ∀ i, |b i|≤K₁*T) (he : ∀ i, |a i-b i|≤K₁*hS i*D) :
    |(∏ i,a i)-∏ i,b i| ≤ (K₁^2)*(∑ i,hS i)*D*T := by
  simp only [Fin.prod_univ_two,Fin.sum_univ_two]
  calc
    _ ≤ |a 0-b 0| *|a 1|+|b 0| *|a 1-b 1| := by rw [show a 0*a 1-b 0*b 1=(a 0-b 0)*a 1+b 0*(a 1-b 1) from by ring,←abs_mul,←abs_mul]; exact abs_add_le ..
    _ ≤ K₁*hS 0*D*(K₁*T)+(K₁*T)*(K₁*hS 1*D) := add_le_add (mul_le_mul (he 0) (h 1) (abs_nonneg _) (by positivity [hP 0])) (mul_le_mul (h' 0) (he 1) (abs_nonneg _) (by positivity))
    _ = _ := by ring

set_option maxHeartbeats 200000 in
private lemma pair_frame (p : Token G 2) (x : Site n) :
   |(∏ i,sent v (p.1 i) (p.2 i) x)-∏ i,frozen v (p.1 i).plaq (p.2 i) x| ≤ (K G)^2*breath p* gradD v * ‖dColor G n 1 v‖ := by
   have h₁ := fun b j=> sent_price v x b j; have h₂ := fun b j=> frozen_price v x b j; have h₃ := fun b j=>coil_first_bound v x b j
   refine (mul_twins (fun i=> sent v (p.1 i) (p.2 i) x) (fun i=> frozen v (p.1 i).plaq (p.2 i) x) (hS:=fun i=>SlotSize (p.1 i)) (K G) (gradD v) (‖dColor G n 1 v‖) (zero_le_one.trans (K_pos _)) (norm_nonneg _) (norm_nonneg _) (fun j=>by positivity) (fun j=>h₁ _ _) (fun j=> h₂ _ _) (fun j=>h₃ _ _) ) |>.trans_eq ?_
   rw [breath,Nat.cast_sum]
set_option maxHeartbeats 200000 in
lemma twin_frame {Z : PathData G} {q σ C Λ} (h : Z.Bounds q σ C Λ) (x : Site n) :
    |tag 2 (song v x (wick Z).loop)| ≤ 2*(K G)^2*Λ*σ⁻¹ * gradD v * ‖dColor G n 1 v‖ := by
   have hg := shadow_pay Z h |>.coeffTwo.paid
   let b := (K G)^2; let D := gradD v; let H := ‖dColor G n 1 v‖
   have hD : 0 ≤ D := norm_nonneg _; have hT : 0≤H := norm_nonneg _
   rw [twin_freeze v x (show (wick Z).loop = necklace Z.loop from rfl) h.width h.two (fun p i=> (Eq.mp (congr_arg (HasSum (Z.loop_coeff p i)) (h.loop_normal p i).1) ((h.loopTerms p i).1.hasSum))),abs_mul]
   have hs := h.width
   let M i := (wick Z).loop i; let c i : ℝ := Real.exp (σ*breath i) * ‖M i‖
   let g := fun i : Token G 2=> M i *((∏ u,sent v (i.1 u) (i.2 u) x)-∏ u,frozen v (i.1 u).plaq (i.2 u) x)
   have hmax i : ‖g i‖ ≤ c i * ((b*σ⁻¹) * D * H) := by
       have hi : breath i ≤ σ⁻¹ * Real.exp (σ * breath i) := by
          rw [mul_comm,← div_eq_mul_inv]; refine (le_div_iff₀ hs).mpr ?_
          rw [mul_comm]; have hh := Real.add_one_le_exp (σ*breath i); linarith
       convert (show ‖g i‖ ≤ ‖M i‖ * (b* (σ⁻¹*Real.exp (σ*breath i))* D * H) by
           unfold g; rw [norm_mul]; exact mul_le_mul_of_nonneg_left ((pair_frame v i x).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi (show 0 ≤ b from by unfold b; positivity)) hD) hT)) (norm_nonneg _)) using 1 <;> first|rfl|unfold c; ring
   have ht : Summable (‖g ·‖) := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hmax (hg.2.1.mul_right ((b*σ⁻¹)*D* H))
   have hi := Summable.tsum_le_tsum hmax ht (hg.2.1.mul_right _)
   change _ ≤ ∑' i,c i * (b*σ⁻¹* D * H) at hi; rw [tsum_mul_right] at hi
   calc
         _ ≤ 2* ∑' i, ‖g i‖ := mul_le_mul (by norm_num) (norm_tsum_le_tsum_norm (f:=g) ht) (abs_nonneg _) (by norm_num)
         _ ≤ 2*(Λ*(b*σ⁻¹*D* H)) := mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_right hg.2.2 (by unfold b; positivity))) (by norm_num)
         _ = _ := by unfold b D H; ring
end YM.UVExt.Paths
