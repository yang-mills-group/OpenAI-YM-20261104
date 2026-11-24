import YM.GradedFar.Fourteen
/-!
# Derive the physical upper log operator costs consumed by G.6

This proves the two directions, only requiring Stamp at p=1, plus frame compatibility at h.
(We don't need and don't claim the strictly-lowering part's better g^L price.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Neighbor
open Function Filter Finset Set PowerSeries
open Extraction Table Spec OPE.Orbits Climb Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize MS MS.Native MS.Land MS.Book MS.Fleet MS.Tide FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar
open Fork (Coat)
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}
   (F:Final C fo S)(J:ℝ→tower S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) {h:ℕ}
local notation "Role" => Fork.Cast F R h
local notation "Φ" => Fork.Cast.cost F R
local notation "judge" => Fork.Cast.judge F R
local notation "Actor" => Fork.Cast.push F R

lemma front_cost {r b:ℝ}(H:Exposure F J R h r b)(hb:0≤b): ‖Fork.Z F R J h r‖ ≤ (∑ i:Role,‖(judge i).toContinuousLinearMap‖)*b:= by
   let Z:=Fork.Z F R J h r
   have hh (i:Role):‖Z (Actor i)‖ ≤ b := (pi_norm_le_iff_of_nonneg hb).2 fun j=>by
     change ‖Fork.Z F R J h r (Actor i) j‖ ≤ b; rw [Z_front]; exact (H i j).1
   refine ContinuousLinearMap.opNorm_le_of_unit_norm ?_ ?_
   · exact mul_nonneg (sum_nonneg fun i _=>ContinuousLinearMap.opNorm_nonneg _) hb
   intro x hx; conv_lhs=> rw [← Fork.Cast.produce F R x];
   rw [map_sum,sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun i _=>?_)
   rw [map_smul,norm_smul]; have hv:= (judge i).toContinuousLinearMap.le_opNorm x; rw [hx,mul_one] at hv
   exact mul_le_mul hv (hh i) (norm_nonneg _) (ContinuousLinearMap.opNorm_nonneg _)
lemma after_cost {r b:ℝ}(H:Exposure F J R h r b)(hb:0≤b):‖Fork.Zopp F R J h r‖ ≤
    (∑ i:Role,‖Actor i‖)*Fintype.card (Toon G h)*b:= by
   let M i:=columns G h (theory i); let Z := Fork.Zopp F R J h r; let w:=∑ i: Role, ‖Actor i‖
   have hw : 0 ≤ w := sum_nonneg fun i _=>norm_nonneg _
   have hv(k: Toon G h): ‖Z (M k)‖ ≤ w*b := by
     rw [← Fork.Cast.produce F R (Z (M k)), show w= _ from (rfl:w=∑i:Role,‖Actor i‖),sum_mul]
     refine (norm_sum_le ..).trans (sum_le_sum fun i _=>?_); rw [norm_smul]
     change ‖judge i (Fork.Zopp F R J h r (columns G h (theory k)))‖*_≤_; rw [Z_after,mul_comm ‖Actor i‖]
     exact mul_le_mul_of_nonneg_right (H i k).2 (norm_nonneg _)
   refine ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg (mul_nonneg hw (Nat.cast_nonneg _)) hb) ?_
   intro x hx
   let z := (columns G h).symm x
   have hz: width z≤ 1:= by unfold width z; rw [LinearEquiv.apply_symm_apply,hx]
   have he:x=∑ i: Toon G h, coord i z • M i:= by
    rw [(show ∑ i:Toon G h, coord i z • M i=(columns G h) z from
     Eq.trans (b:=columns G h (∑ i:Toon G h, coord i z • theory i)) (by rw [map_sum]; exact Finset.sum_congr rfl fun i _=> (map_smul ..).symm)
      (congr_arg (columns G h) (all_sig z)))]
    exact ((columns G h).apply_symm_apply x).symm
   rw [he,map_sum]; refine (norm_sum_le ..).trans (le_trans (b:=∑ _ : Toon G h,w*b) (sum_le_sum
     fun i _=>?_) ?_)
   · rw [map_smul,norm_smul]; exact (mul_le_mul ((coord_le i z).trans hz) (hv i) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
   · rw [sum_const,card_univ,nsmul_eq_mul]; change _ ≤ w * _ * b; exact (by ring_nf; exact le_rfl)
variable (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
    {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)}(H:Main.Match Z hG M σ true)
include H
/-- Polynomial portion of (G.2), needed for G.6. This theorem also makes clear the remaining
physical-neighbor requirement in that result. Here and throughout use the one prescribed physical
frame, the `Coat` budget is on its operators to every layer. -/
theorem Z_estimate {t:ℝ→ℝ}(heard:∀ i (hi:i≤h), Included F J i h hi)(stamp:Stamp J Z M ν t h 1):
    Coat F R J h:=by
   obtain ⟨C,hC,p,H'⟩:= envelope F J R Z M ν H heard stamp
   let a:= ∑ i:Role,‖(judge i).toContinuousLinearMap‖; let b:= (∑ i:Role,‖Actor i‖)*Fintype.card (Toon G h)
   have ha: 0 ≤ a:= sum_nonneg fun i _=>ContinuousLinearMap.opNorm_nonneg _
   have hb: 0 ≤ b:=mul_nonneg (sum_nonneg fun i _=>norm_nonneg _) (Nat.cast_nonneg _)
   refine ⟨p,(a+b)*C,by positivity,?_⟩
   filter_upwards [H', (ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hr ht (hp:0<r)
   have h : 0 ≤ C*OPE.Log.badge r^p:= mul_nonneg hC (pow_nonneg
      (add_nonneg zero_le_one (neg_nonneg.mpr (Real.log_nonpos hp.le ht))) _)
   exact (add_le_add (front_cost F J R hr h) (after_cost F J R hr h)).trans_eq (by rw [mul_assoc (a+b),add_mul])
end YM.Integration.GradedFar.Neighbor
