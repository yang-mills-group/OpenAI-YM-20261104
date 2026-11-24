import YM.RegulatorIR.Geometry.Poles

/-! Pay as powers of R/l. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Geometry
open Finset Function Lattice PertExtension Orb Gauge Budget Budget.Tuple Budget.Packet Motion Tariff Spatial Uniform ENNReal
open scoped ENNReal NNReal BigOperators Classical Topology
variable {n : Side} {l P R : ℝ}

def kilo (k:ℕ): ℝ≥0∞:= ENNReal.ofReal ((k+1:ℝ)^2)⁻¹ -- preced! choose explicit
lemma totalK : (∑' k:ℕ,kilo k)≠⊤:=by
 let f (k:ℕ):ℝ:= 1/( (k:ℝ)+1)^2
 have hf : Summable f := by
    have h:= (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num); convert h using 1; ext1 k; rw [abs_of_pos (by positivity : 0< (k:ℝ)+1), Real.rpow_two]
 have hp k: kilo k=‖f k‖ₑ:=by rw [kilo,← ofReal_norm, Real.norm_of_nonneg (by unfold f;positivity)]; simp [f]
 simp_rw [hp]; exact tsum_enorm_ne_top_iff_summable_norm.mpr hf.norm
lemma root_factor (hl:0<l)(hr:0<R)(j:ℕ): ENNReal.ofReal ((1+2*((j+1:ℝ)*R)/l)^4)* (ENNReal.ofReal ((j+1:ℝ)^6))⁻¹ ≤ ENNReal.ofReal ((1+2*R/l)^4) * kilo j:=by
 rw [← ENNReal.ofReal_inv_of_pos (by positivity),kilo, ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
 apply ENNReal.ofReal_le_ofReal; rw [show (1+2*R/l)^4*((j+1:ℝ)^2)⁻¹=((1+2*R/l)*(j+1:ℝ))^4*((j+1:ℝ)^6)⁻¹ from ?_]
 · apply mul_le_mul_of_nonneg_right _ (by positivity); apply pow_le_pow_left₀ (by positivity)
   calc
    _ ≤ ((j:ℝ)+1)+2*((j+1:ℝ)*R)/l:=by have he: (0:ℝ)≤(j:ℝ):=(by positivity);linarith
    _ = _:= by ring
 field_simp
lemma rain (hl:0<l)(hR:0<R)(P:ℝ) (p : Cover × Axis × ℕ):
   (∑' i:ticketPole (n:=n) l P R p,(amount R 6 (altitude P l i.val))⁻¹) ≤ ENNReal.ofReal ((1+2*R/l)^4)*kilo p.2.2:=by
 let V := ticketPole (n:=n) l P R p; let k:=p.2.2
 apply le_trans _ (root_factor hl hR k)
 apply le_trans _ (mul_le_mul_left (count_rim (n:=n) (P:=P) hl hR p) _)
 let c':=(ENNReal.ofReal ((k+1:ℝ)^6))⁻¹
 rw [tsum_fintype]; rw [show ((Fintype.card (ticketPole (n:=n) l P R p)):ℝ≥0∞)*_ = ∑ _:V,c' from ?_]
 · apply Finset.sum_le_sum; intro i _
   have he:rim l P R i.val=k:=congr_arg (fun q=>q.2.2) i.property
   apply ENNReal.inv_le_inv.mpr
   change ENNReal.ofReal ((k+1:ℝ)^6) ≤ ENNReal.ofReal (1+altitude P l i.val / R)^6
   rw [ENNReal.ofReal_pow (by positivity)]; apply pow_le_pow_left';apply ENNReal.ofReal_le_ofReal
   have hp:(k:ℝ) ≤ altitude P l i.val/R:=by rw [← he]; exact Nat.floor_le (div_nonneg (Spatial.singular_nonneg ..) hR.le)
   linarith
 simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,c',k]; rfl

lemma rootTax (hl:0<l)(hr:0<R)(he:l*n.val=P) :
   (∑' i:OEdge n,(amount R 6 (altitude P l i))⁻¹) ≤ (polygon.card:ℝ≥0∞)* (4* ENNReal.ofReal ((1+2*R/l)^4)) * ∑' k,kilo k:= by
 let f (x:OEdge n):= (peak P l x,x.val.2,rim l P R x)
 let C p:= ∑' i:Stalk f p,(amount R 6 (altitude P l i.val))⁻¹
 let H := ENNReal.ofReal ((1+2*R/l)^4)
 rw [← ENNReal.tsum_fiberwise _ f]; change ∑' p,C p ≤ _; rw [ENNReal.tsum_prod']
 have hh x (hx:x∉polygon) : (∑' (p:Axis × ℕ),C (x,p))=0 :=by
    have hv (p:Axis×ℕ): C (x,p)=0:=by
       haveI:IsEmpty (Stalk f (x,p)):= ⟨fun y=> hx ((show peak P l y.val=x from congr_arg Prod.fst y.property) ▸ eastP he hl y.val)⟩
       exact tsum_empty
    simp_rw [hv]; exact tsum_zero
 rw [tsum_eq_sum hh]; apply le_trans (Finset.sum_le_sum (g:=fun _=>4*H*∑' k,kilo k) (fun i _=>?_))
 · simp only [sum_const,nsmul_eq_mul,mul_assoc]; exact le_rfl
 rw [ENNReal.tsum_prod']; apply le_trans (ENNReal.tsum_le_tsum (g:=fun _=> H*∑' k,kilo k) (fun j=> (ENNReal.tsum_le_tsum fun k=> rain (n:=n) hl hr P (i,j,k)) |>.trans_eq ENNReal.tsum_mul_left))
 rw [tsum_fintype]; simp [Axis,nsmul_eq_mul, mul_assoc]
end YM.RegulatorIR.Geometry
