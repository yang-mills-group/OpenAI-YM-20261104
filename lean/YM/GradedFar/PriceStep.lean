import YM.GradedFar.Neighbor
import YM.GradedFar.Recycle
/-!
# Engineering earnings envelope for the *physical* fields from first-order stamps

One-neighbor recurrence for each scaled column and inverse entry, plus support lower triangle.
By writing both directions this avoids having to pay more singular cross-sector hidden entries.
Will use to prove (polynomial part) of G2. Orientation of actor projection at weight j, not scale
of chosen exterior polls. The estimates in use here are *compact (G.1)* prices; no high-order
Q1 or moving GC collision needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
namespace Neighbor
open Function Filter Finset Set PowerSeries
open Extraction Table Spec OPE.Orbits Climb Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize MS MS.Native MS.Land MS.Book MS.Fleet MS.Tide FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar
open Fork (Coat)
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}
   (F:Final C fo S)(J:ℝ→tower S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
   {h:ℕ}
local notation "g" => strength G
local notation "Role" => Fork.Cast F R h
local notation "Φ" => Fork.Cast.cost F R
local notation "Actor" => Fork.Cast.push F R

def front (r:ℝ)(a:Role)(i: Toon G h) := (r:ℂ)^Φ a * coord i ((assign J r h).symm (Actor a))
def after (r:ℝ)(a:Role)(i: Toon G h) := (r:ℂ)⁻¹^Φ a * Fork.Cast.judge F R a (assign J r h (theory i))
def defect (r s:ℝ)(i k: Toon G h):= coord k (delta J h r s (theory i))
lemma Z_front (p:Role)(i: Toon G h)(r:ℝ): Fork.Z F R J h r (Actor p) i=front F J R r p i:=by
  change coord i ((assign J r h).symm ((Fork.Cast.lift F R h r) _)) = _; rw [Fork.Cast.lift_apply,map_smul,map_smul]
  rfl
lemma Z_after (p:Role)(i: Toon G h)(r:ℝ): Fork.Cast.judge F R p (Fork.Zopp F R J h r (columns G h (theory i)))=after F J R r p i:=by
  change Fork.Cast.judge F R p ((Fork.Cast.lift F R h r⁻¹ ∘ₗ (assign J r h).toLinearMap)
    ((columns G h).symm (columns G h (theory i))))=_
  rw [LinearEquiv.symm_apply_apply, LinearMap.comp_apply,Fork.Cast.lifted_grade,Complex.ofReal_inv]
  rfl
lemma admit_front {r:ℝ}(p:Role) (hd:∀ u: Sec G (Φ p), assign J r h (up (p.costs F R) u)=
       F.sector.derivatives.rise (p.costs F R) (assign J r (Φ p) u))(i: Toon G h) (hp:Φ p < heft (Dframe.flash i)):
    front F J R r p i=0:=by
  let x:= (assign J r (Φ p)).symm (R.actor (Φ p) p.snd)
  have hv:(assign J r h).symm (Actor p)= up (p.costs F R) x:= ((assign J r h).symm_apply_eq).mpr (by simp only [hd, x, LinearEquiv.apply_symm_apply]; rfl)
  have hc(j: Toon G (Φ p)) : Dframe.enroll (p.costs F R) j ≠ i := by
    intro he; rw [← he] at hp; exact (Dframe.size_le j).not_gt hp
  unfold front; rw [hv,(all_sig x).symm]; simp only [map_sum,map_smul,lift_sig,pivotδ,if_neg (hc _),smul_zero,Finset.sum_const_zero,mul_zero] -- Dependent rebasing σ
lemma admit_after {r:ℝ}(i:Toon G h) (hd:∀ u: Sec G (heft (Dframe.flash i)), assign J r h (up (Dframe.size_le i) u)=
       F.sector.derivatives.rise (Dframe.size_le i) (assign J r (heft (Dframe.flash i)) u))(p:Role)(hp:heft (Dframe.flash i)<Φ p): after F J R r p i=0 := by
   have hj: ∀ u, Fork.Cast.judge F R p (F.sector.derivatives.rise (Dframe.size_le i) u)=0:= by
      intro a; unfold Fork.Cast.judge; rw [LinearMap.comp_apply]; exact Eq.trans (congrArg ((R.basis _).coord p.snd)
        (Subtype.ext (Eq.trans (R.cut_rise ..) (R.kills_lower _ _ hp _)))) (map_zero _)
   unfold after; rw [include_sig i, hd,hj,mul_zero]

lemma rel_step {r s:ℝ}(hr:0<r)(hs:0<s)(i:Toon G h):
    relative J r s h (theory i) = ((s:ℂ)/ (r:ℂ))^(heft (Dframe.flash i)) • theory i + ∑ k: Toon G h, defect J r s i k • theory k := by
   rw [show ∑ k: Toon G h, defect J r s i k • theory k= _ from (all_sig (delta J h r s (theory i)))]
   rw [delta,LinearMap.sub_apply,weightAt (div_pos hs hr),Complex.ofReal_div,add_sub_cancel]
   rfl
lemma priced_step {r s D:ℝ}(H:opField (delta J h r s) ≤ D)(i k: Toon G h): ‖defect J r s i k‖ ≤ D :=
  (coord_le _ _).trans ((op_use _ _).trans ((mul_le_mul_of_nonneg_right H (width_nn _)).trans_eq (by rw [basis_width,mul_one])))

lemma front_rule {r s:ℝ}(hr:0<r)(hs:0<s)(a:Role)(i:Toon G h):
    front F J R s a i =
    ((s:ℂ)/(r:ℂ))^Φ a * (((r:ℂ)/(s:ℂ))^(heft (Dframe.flash i))*front F J R r a i +
      ∑ k:Toon G h, defect J s r k i * front F J R r a k) := by
   let y:= (assign J r h).symm (Actor a)
   unfold front; rw [show (assign J s h).symm (Actor a)=relative J s r h y from by unfold relative y;simp]
   let H j:=coord i (relative J s r h (theory j))
   have he : coord i (relative J s r h y) = (↑r/↑s:ℂ)^(heft (Dframe.flash i))* coord i y + ∑ k, defect J s r k i*coord k y:= by
     have hv (p:Toon G h): H p= (if i=p then (↑r/↑s:ℂ)^(heft (Dframe.flash i)) else 0)+defect J s r p i:= by
        unfold H defect; unfold delta; rw [LinearMap.sub_apply, map_sub,weightAt (div_pos hr hs),Complex.ofReal_div, map_smul,smul_eq_mul,pivotδ]
        by_cases hi : i=p; subst i; · simp
        simp only [if_neg hi,if_neg (Ne.symm hi),mul_zero,sub_zero,zero_add]; rfl
     conv_lhs=> rw [← all_sig y,map_sum,map_sum];
     rw [show (∑ j:Toon G h,coord i (relative J s r h (_ • theory j)))= ∑ j, H j * coord j y from ?_];
     simp_rw [hv,add_mul,ite_mul,zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
     apply Finset.sum_congr rfl; intro j _; rw [map_smul,map_smul,mul_comm]; rfl
   rw [he]; unfold y; simp_rw [div_pow,mul_add,Finset.mul_sum]; congr 1
   · field_simp [show (r:ℂ) ≠ 0 by exact_mod_cast hr.ne', show (s:ℂ) ≠ 0 by exact_mod_cast hs.ne']
   apply Finset.sum_congr rfl; intro j _; field_simp [show (r:ℂ) ≠ 0 by exact_mod_cast hr.ne', show (s:ℂ) ≠ 0 by exact_mod_cast hs.ne']
lemma after_rule {r s:ℝ}(hr:0<r)(hs:0<s)(a:Role)(i:Toon G h):
    after F J R s a i =
    ((r:ℂ)/(s:ℂ))^Φ a * (((s:ℂ)/(r:ℂ))^(heft (Dframe.flash i))*after F J R r a i +
      ∑ k:Toon G h, defect J r s i k * after F J R r a k) := by
    unfold after; rw [← atHome J r s (theory i), rel_step J hr hs, map_add,map_smul, map_sum, map_add, map_smul,map_sum, smul_eq_mul]; simp_rw [div_pow,inv_pow,mul_add,Finset.mul_sum]; congr 1
    · field_simp [show (r:ℂ) ≠ 0 by exact_mod_cast hr.ne', show (s:ℂ) ≠ 0 by exact_mod_cast hs.ne']
    apply Finset.sum_congr rfl; intro j _; rw [map_smul,map_smul,smul_eq_mul]; field_simp [show (r:ℂ) ≠ 0 by exact_mod_cast hr.ne', show (s:ℂ) ≠ 0 by exact_mod_cast hs.ne']
end Neighbor
end YM.Integration.GradedFar
