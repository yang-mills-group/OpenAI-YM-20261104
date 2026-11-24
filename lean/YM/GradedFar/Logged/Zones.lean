import YM.GradedFar.Logged.Deck

/-!
# Terminal (G.6) fixed-field costs before H-normalization
 (Beside actual scaling, uniform for even broader radius ranges.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Logged.Zones
open Finset Filter Function Set Spec Table Extraction OPE.Log Asymptotics Orbits MeasureTheory
open scoped Topology Classical BigOperators ContDiff
open Seats Stroke Fork Deck
open Economy (Paint)
variable {I J L:Type} [Fintype I][Fintype J]
variable (D : Pitch L)
variable (x:L→I→E4)(y:L→J→E4)(o:L→E4) (M δ:ℝ)
  (hm:0 ≤ M)(hd:0<δ) (hx:∀ᶠ i in D.p, Landed (D.r i) (D.s i) M δ (x i) (y i))
variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}(F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {d:I→ℕ}{e:J→ℕ} (v:Labels S d)(w:Labels S e) (u:L→Viewers F) (P:LogTrace F R.port) (simple:G.Simple) (h:ℕ)
local notation "X"=> inlay D x o
local notation "Y"=> outlay D y o
local notation "Q"=> F.sector.derivatives
local notation "T"=>spectator F
local notation "R0"=> Rnow D d e
local notation "s"=>D.s
local notation "r"=>D.r
local notation "stamp"=>D.toSmall

abbrev A (i:L):= discrepancy (spectator F (u i)) h (X i) (o i) v (R.packet h (X i) v (o i)) (Y i) w
local notation "Gap"=>radius D h
include hm hd hx P simple F R
-- variant `Paint.contract_linear` could put in Tips. use std Fields.
lemma upon_v (U:L→ S.Field h){B:L→ℝ}(hp:Paint D.toSmall B U) : Paint D.toSmall (fun i=> B i*frameCost e (D.s i) h)
    (fun i=> upon (T (u i)) h (o i) (Y i) w (U i)) := by
    let V i:=upon (T (u i)) h (o i) (Y i) w; let T':=Module.finBasis ℂ (S.Field h)
    have he j:= Deck.upon_fixed D x y o M δ hm hd hx F R w u P simple h (T' j)
    have H i : upon (T (u i)) h (o i) (Y i) w (U i)=
        ∑ j,(T'.coord j (U i)) • V i (T' j):=by
      conv_lhs => arg 2; rw [← T'.sum_repr (U i)]
      simp_rw [map_sum,map_smul]; rfl
    simp_rw [H]; exact Paint.sum _ fun j _=> (he j).scales (Paint.linear_c (T'.coord j) hp)

lemma fresh_paid : Paint stamp (fun i=> Deck.radius D h i/Rnow D d e i) (A D x y o F R v w u h) := by
    have hd0 := old_step D x y o M δ hm hd hx F R v w u P simple h
    let Z i := R.packet h (X i) v (o i); let W i:= Orbits.shadowOld R.port h (X i) (o i) v
    have hs:= (Trace.shadow_pair F R _ hm hd (X) o (whole_room D x y o M δ hm hd hx) P v h)
    have hz:= upon_v D x y o M δ hm hd hx F R w u P simple h (fun i=> Z i-W i) hs
    have hk : ∀ᶠ i in D.p, |Stroke.lifetime d h (r i)* Deck.frameCost e (s i) h| ≤ |Gap i/R0 i| := by
      filter_upwards [D.cost, D.toSmall.positive,D.outer.positive] with i hi hr (ht : 0 < s i)
      let a:= r i; let b:= s i; let j:=∑ i,d i; let k:=∑ i,e i
      have hp:0<a :=hr; have hq:0<b:=ht
      change |a^(h+1)/a^j*b⁻¹^(h+k)|≤|(b+(a/b)^(h+1))/(a^j*b^k)|
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]

      calc
        a^(h+1)/a^j*b⁻¹^(h+k) = b/(a^j*b^k)*(a/b)^(h+1):=by rw [inv_pow,div_pow,pow_add b h k,pow_succ b]; field_simp
        _ ≤ b/(a^j*b^k)*1:= mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) ((div_le_one ht).2 hi)) (by positivity)
        _ ≤ _:= by rw [mul_one]; gcongr; exact le_add_of_nonneg_right (by positivity)
    have H:= hz.eases (U:=fun i=>Gap i/R0 i) hk
    refine (hd0.minus H).assists (Eventually.of_forall fun i=>?_); unfold A discrepancy; rw [map_sub]; unfold W Z; abel

-- (G.6) also needs size of Ywide, not just the signed residual.
-- easiest bound after G5/7 price on the acted `fresh` then each term by moving `upon`.
lemma full_priced : Paint stamp (fun i=> (1+Gap i)/R0 i) (fun i=> Orbits.whole (T (u i)) (X i) v (Y i) w) := by
    have hc:= fresh_paid D x y o M δ hm hd hx F R v w u P simple h
    let Z (j:Fin (h+1))(i:L):= upon (T (u i)) j.val (o i) (Y i) w (R.fresh j.val (X i) (o i) v)
    let E i:=(1+Gap i)/R0 i
    have hs (j:Fin (h+1)): Paint stamp (fun i=> Trace.core d j.val (r i) * frameCost e (s i) j.val) (Z j) :=
       upon_v _ x _ _ M δ hm hd hx F R w u P simple _ _ (Trace.current F R _ hm hd (X) o (whole_room D x y o M δ hm hd hx) P v _)
    have hG i (hp:0<r i) (ht:0 < s i): 0≤Gap i := by unfold Deck.radius; positivity
    have hU i (hp:0<r i) (ht:0 < s i):0<R0 i:=by unfold Rnow; positivity
    have he i (hp:0<r i) (ht:0 < s i) : 0≤ E i:= by unfold E; positivity
    have hw (j:Fin (h+1)): Paint stamp E (Z j):=(hs j).eases (by
      filter_upwards [D.cost,D.toSmall.positive,D.outer.positive] with i hi (hp:0<r i) (ht:0 < s i)
      rw [abs_of_nonneg (he i hp ht), abs_of_nonneg]; swap; · unfold frameCost Trace.core; positivity
      have hW:(D.r i)^j.val*(D.s i)⁻¹^j.val≤1:=by
        rw [← mul_pow]; exact pow_le_one₀ (by positivity) ((div_eq_mul_inv (D.r i) (D.s i)) ▸ (div_le_one ht).2 hi)
      unfold Trace.core frameCost E Rnow; calc
          _ = ((r i)^j.val*(s i)⁻¹^j.val)/R0 i:=by unfold Rnow; rw [pow_add,inv_pow,inv_pow]; field_simp
          _ ≤ _:= div_le_div_of_nonneg_right (hW.trans (le_add_of_nonneg_right (hG i hp ht))) (hU i hp ht).le )
    refine (Paint.plus (hc.eases (U:=E) (?_)) (Paint.sum Finset.univ (fun i _=> hw i))).assists ?_
    · filter_upwards [D.toSmall.positive,D.outer.positive] with i (hi:0<r i) (ht:0 < s i)
      rw [abs_of_nonneg (he i hi ht), abs_of_nonneg (div_nonneg (hG _ hi ht) (hU _ hi ht).le)]; unfold E; gcongr; norm_num
    filter_upwards [hx] with i hi
    unfold Z A discrepancy Reader.packet; rw [map_sum]; rw [show (∑ j:Fin (h+1), (upon (T (u i)) h (o i) (Y i) w) (F.sector.derivatives.rise (d:=j.val) (Nat.le_of_lt_succ j.isLt) (R.fresh j.val (X i) (o i) v)))= _ from Finset.sum_congr rfl (fun (j:Fin (h+1)) _=> upon_rise F R (Nat.le_of_lt_succ j.isLt) (R.fresh j.val (X i) (o i) v) _ _ _ w (Fork.unique_root hi _ hd))]; abel
end YM.OPE.Logged.Zones
