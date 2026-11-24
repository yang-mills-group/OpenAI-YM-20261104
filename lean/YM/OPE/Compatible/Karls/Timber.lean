import YM.OPE.Compatible.Karls.Fleece
/-! # homogeneous crowns, going backwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{m k i:ℕ}{q:ℝ}(p:E→L[ℝ] E)
local notation "X!"=> E→L[ℝ] E
open Filter Finset
open Quit.PriceZ
local notation "A!"=> Dice E
variable {G:Type}[NormedAddCommGroup G][NormedSpace ℝ G]
-- `thick` Pal stationary.H
variable (G:ℕ→ℕ→ Dice E) (L:ℕ→ E→L[ℝ] E)(Y:ℕ→Dice E) (T:E→L[ℝ] E) {b v u w:ℝ} {a d:ℕ}
-- error.Core
abbrev ErrS (p:ℕ→ℕ→Dice E) (L:ℕ→ E→L[ℝ] E)(i k:ℕ): Dice E:= p i (k+1) - pullD (L i) (p (i+1) k)
abbrev coreE (i:ℕ): Dice E:=Y (i+1)-pullD T (Y i)
lemma shrub (hs:∃ c,Hex b Y c)(hz:∃ c:ℝ,0≤c∧∀ i k, ‖G i k-Y k‖ ≤ c*b^k*u^i) (h:∃ c,Hex u (fun i=>L i-T) c)(hv:0 < b)(hp:0 < u)(hr:u<1):∃ c:ℝ, 0 ≤ c ∧∀ i k:ℕ, ‖ErrS G L i k-coreE Y T k‖ ≤ c*b^k*u^i :=by
    obtain ⟨c,hc,H⟩:=hz; obtain ⟨d,D⟩:=h; obtain ⟨t,B⟩:= hs; have hy:∀ i,‖L i‖≤ d+‖T‖:=fun i=>by nth_rw 1 [show L i=L i-T+T from (sub_add_cancel ..).symm]; exact (norm_add_le ..).trans (add_le_add_left ((D i).trans (mul_le_of_le_one_right D.price (pow_le_one₀ hp.le hr.le))) _)
    let q:= d+‖T‖; have hQ:=D.price; have ht:= B.price; have hh:0 ≤ q:=(by unfold q;positivity); refine ⟨c*b+c*u*q^2+(t*d*q+t*‖T‖*d),(by positivity),fun i j=>?_⟩
    let P:=L i; let A:=b^j; let U:=u^i; let Z:= Y j; have hx:0≤A:=(by unfold A; positivity); have hv:0≤U:=(by unfold U; positivity); have ha:= H (i+1) j
    have hX : ‖G i (j+1)-Y (j+1)‖≤ c*b*A*U:=(H i _).trans_eq (by unfold A U; rw [pow_succ]; ring)
    have h₁: ‖pullD P (G (i+1) j)-pullD T (Y j)‖≤ c*u*q^2*A*U+(t*d*q+t*‖T‖*d)*A*U:=by
         rw [show pullD P (G (i+1) j)-pullD T (Y j)=pullD P (G (i+1) j-Z)+(rollD (P-T) P Z + rollD T (P-T) Z) from ?_]; swap
         · unfold pullD; rw [drag,←scorp P P T T Z]; change (pullD P _) - (pullD T Z)= (pullD P _)-(pullD P Z)+((pullD P Z)-pullD T Z); abel
         apply (norm_add_le (pullD P (G (i+1) j-Z)) (rollD (P-T) P Z + rollD T (P-T) Z)).trans; refine add_le_add ?_ ?_
         · apply (segment P P _).trans; apply le_trans (mul_le_mul (mul_le_mul ha (hy i) (norm_nonneg _) (by positivity)) (hy i) (norm_nonneg _) (by positivity)); rw [pow_succ]; unfold q A U; exact le_of_eq (by ring)
         have he := (norm_add_le (rollD (P-T) P Z) (rollD T (P-T) Z)|>.trans (add_le_add (segment (P-T) P Z) (segment T (P-T) Z))); apply he.trans; apply le_trans (add_le_add (show ‖Z‖*‖P-T‖ * ‖P‖≤ t*A*(d*U)*q from mul_le_mul (mul_le_mul (B j) (D i) (norm_nonneg _) (by positivity)) (hy i) (norm_nonneg _) (by positivity)) (show ‖Z‖*‖T‖*‖P-T‖ ≤ t*A*‖T‖*(d*U) from mul_le_mul (mul_le_mul_of_nonneg_right (B j) (norm_nonneg _)) (D i) (norm_nonneg _) (by positivity))); apply le_of_eq; ring
    rw [ErrS,coreE,sub_sub_sub_comm (G i (j+1)) (pullD (L i) _) (Y _) (pullD T _)]; apply (norm_sub_le (G i (j+1)-Y (j+1)) (pullD (L i) (G (i+1) j)-pullD T (Y j))|>.trans (add_le_add hX h₁)).trans_eq; unfold A U; ring
-- station witness
structure Punch (G:ℕ→ℕ→ Dice E) (L:ℕ→ E→L[ℝ] E)(Y:ℕ→Dice E) (T:E→L[ℝ] E)(u b w:ℝ):Prop where
     west :0 < w
     cap : ∃ c:ℝ, Hex b Y c
     fees : ∃ c:ℝ,0 ≤ c∧∀ i l, ‖G i l-Y l‖ ≤ c*b^l*u^i
     bonds : ∃ c,Hex u (fun i=> L i-T) c
     bu:0 < b
     pu:0 < u
     hu:u<1
     bill : ∃ c:ℝ,∀ i j,‖ErrS G L i j‖≤ c*w^j
namespace Punch
variable (h:Punch G L Y T u b w)
include h
omit h [NormedSpace ℝ E] in lemma mAv (p:ℕ→ E)(b:E)(h: Tendsto (fun i=>‖p i-b‖) atTop (𝓝 0)): Tendsto p atTop (𝓝 b):= tendsto_iff_norm_sub_tendsto_zero.mpr h
omit h [NormedSpace ℝ E] in lemma mN (p:ℕ→ E)(b:E)(h:Tendsto p atTop (𝓝 b)): Tendsto (fun i=>‖p i‖) atTop (𝓝 ‖b‖):= h.norm
lemma edgeR (i:ℕ): Tendsto (fun j=>ErrS G L j i) atTop (𝓝 (coreE Y T i)):=by
     obtain ⟨c,hc,H⟩:= shrub G L Y T h.cap h.fees h.bonds h.bu h.pu h.hu; let t:= tendsto_pow_atTop_nhds_zero_of_lt_one h.pu.le h.hu; have hx:= t.const_mul (c*b^i); rw [mul_zero] at hx; apply (mAv (E:=Dice E) (fun j=>ErrS G L j i) _); exact squeeze_zero (fun j=>norm_nonneg (ErrS G L j i-coreE Y T i)) (fun j=>H j i) hx
lemma edgeV :∃ c,Hex w (coreE Y T) c:=by
     obtain ⟨c,hc⟩:= h.bill; refine ⟨c,fun i=>?_ ⟩; have he:Tendsto (fun j:ℕ=>‖ErrS G L j i‖) atTop (𝓝 ‖coreE Y T i‖):= (show Tendsto _ _ _ from mN (E:=Dice E) _ _ (h.edgeR G L Y T i)); apply le_of_tendsto' he; exact fun j=> hc j i
lemma sugar (a:ℝ)(ha:w<a):∃ t b':ℝ,0<t∧t<1∧0<b' ∧ b'< a∧ ∃ c:ℝ,0 ≤ c ∧∀ i j, ‖ErrS G L i j-coreE Y T j‖ ≤ c*b'^j*t^i:=by
    obtain ⟨c,hc,H⟩:= shrub G L Y T h.cap h.fees h.bonds h.bu h.pu h.hu; obtain ⟨d,D⟩:= h.edgeV G L Y T; obtain ⟨r,B⟩:=h.bill; exact Hull h.west h.bu h.pu h.hu ha (fun i j=> ErrS G L i j-coreE Y T j) ⟨r+d,fun i j=>((norm_sub_le (ErrS G L i j) (coreE Y T j)).trans (add_le_add (B i j) (D j))).trans_eq (add_mul ..).symm⟩ ⟨c,H⟩
end Punch
end YM.OPE.Hark
