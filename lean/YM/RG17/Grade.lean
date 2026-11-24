import YM.RG17.Layout

/-!
# Engineering scaling rate for the actual full V_d canonical sublimit

Engineering estimate in the actual filtration split. The comparison of
letters/regulators and frame production are separate. Scaling here to
continuum already after fixed-m chart limits. Not λ or a coupling error.
Uses the same whole-origin and quotient-plane estimates as in exact OPE.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits
open RG12 OPE.Columns
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}
    (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (L:Layout F)
    (H:Reach C L.level) (h:Services C f S)
set_option quotPrecheck false
local notation "ρ" => OPE.run
local notation "a" => C.S.a
local notation "m"=> L.level
local notation "look"=> L.charts
local notation "τ"=> C.path.levels

include H in
lemma lengthLevels : RateIs home ρ (fun r=> a (m r)) (-1) := by
    simpa only [mul_one] using (Columns.rescale (YM.MergeProof.Ribbons.Note.note_a C.S) H.growing H.nearby)

include H L P h
lemma engineeringUpper (d j:ℕ) (u:ℝ→ C.label d)
    (hu : RateLE home ρ u 0): RateLE home ρ (fun r=> P.cutTest j d (engineering (S:=S) L.charts d (L.level r) (u r))) (-(j:ℝ)) := by
    letI : L.lens.NeBot := L.notbot
    -- price before engineering: whole at j=0; otherwise remove the j-1 plane
    let Q: C.label d→L[ℂ] S.Field j:= LinearMap.toContinuousLinearMap <|
        (P.cutTest j d).comp (S.project d)
    have hh := lengthLevels L H
    let M i:= mass C d (u i)
    have hm : RateLE home ρ M 0 := by
        let D :ℝ:=((C.labels.level d).extra+1:ℕ)
        have hw : RateLE home ρ (fun i=> D* ‖u i‖) (0+0):=
          (RateLE.const D ageLarge).mul hu.norm
        apply RateLE.transfer (F:=fun i=> D* ‖u i‖) (by simpa using hw) <| Eventually.of_forall fun i=> ?_
        change ‖mass C d (u i)‖ ≤ _
        rw [Real.norm_of_nonneg (mass_nonneg ..)]; exact (mass_le_norm ..).trans (Real.le_norm_self _)
    by_cases hl:j ≤ d; swap
    · have hl:d<j:=Nat.lt_of_not_ge hl
      simpa only [P.kills_lower j d hl] using! RateLE.zero home ρ (-(j:ℝ)) (X:= S.Field j)
    suffices hv : RateLE home ρ (fun r=> Q (L.charts d (L.level r) (u r))) ((d:ℝ)-j) by
       have hw: RateLE home ρ (fun r=> ((a (m r) ^ d : ℝ):ℂ)) (-(d:ℝ)) := by
            refine RateLE.transfer (F:=fun r=> a (m r)^d) ?_ (Eventually.of_forall fun _=> (Complex.norm_real ..).le)
            simpa only [mul_neg, mul_one] using! ((hh.power d).pays ageLarge)
       have hx:= hw.smul hv
       simp_rw [engineering_at,map_smul]
       exact hx.mono (le_of_eq (by ring))
    obtain ⟨_,hsimple,⟨W,r,D,hT⟩,M',V,E,B,hB⟩:= h
    let Y x:= look d (m x) (u x)
    cases j with
    | zero=>
       let c(x):=juice τ (m x)*(a (C.ref d)/a (m x))^d
       have hv : RateIs home ρ (fun _=> a (C.ref d)) 0:= RateIs.const ageLarge (C.S.a_pos _)
       have hc: RateIs home ρ c (d:ℝ):= by
          simpa only [mul_one, sub_neg_eq_add, zero_add] using! ((juice_rate_seq C H.growing H.nearby).mul ((hv.div hh).power d))
       simp only [Nat.cast_zero, sub_zero] at *
       apply (RateLE.of_norm_le (F:=fun r=> Q (L.charts d (m r) (u r))) (f:= fun i=> ‖Q‖*(c i*M i)) ?_ ?_ )
       · simpa only [add_zero,zero_add] using! ((RateLE.const ‖Q‖ ageLarge).mul ((hc.pays ageLarge).mul hm))
       filter_upwards [H.growing.eventually_ge_atTop (C.ref d)] with i hi
       apply (Q.le_opNorm _).trans
       refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
       obtain ⟨q,hq,hz⟩:= L.observes.purchase d (m i) hi (l:=L.lens) le_rfl (u i)
       apply le_of_tendsto hq.norm
       filter_upwards [hz,L.observes.grows.eventually_ge_atTop (m i)] with w hw hl
       exact (whole_origin hB (q w) hi hl).trans
           (mul_le_mul_of_nonneg_left hw (mul_nonneg (zero_le_one.trans (juice_pos ..)) (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _)))
    | succ j=>
       let c(i):=fare C (m i) d j
       have hj:j<d:=hl
       have hk:↑(d-(j+1))=(d:ℝ)-(j+1:ℕ) := Nat.cast_sub hl (R:=ℝ)
       have hc: RateIs home ρ c ((d:ℝ)-(j+1:ℕ)) := by
          rw [← hk]
          simpa only [mul_one] using (Columns.fare_rate (d:=d) (e:=j) hT.toTableTickets H.growing ageLarge H.nearby)
       apply RateLE.of_norm_le (f:= fun i=> ‖Q‖*(c i*M i))
       · simpa only [add_zero,zero_add] using! ((RateLE.const ‖Q‖ ageLarge).mul ((hc.pays ageLarge).mul hm))
       filter_upwards [H.growing.eventually_ge_atTop (C.ref d)] with i hi
       obtain ⟨q,hq,hz⟩:= L.observes.purchase d (m i) hi (l:=L.lens) le_rfl (u i)
       obtain ⟨y,⟨x,hx⟩,hv⟩:= Columns.limit_cap hT.toTableTickets hsimple hB P.lifts hj q (Y i) L.certified hi hz hq
       change F.sector.derivatives.rise hj.le x= _ at hx
       have hp: Q y=0:= by
          change P.cutTest _ _ (S.project _ _)=_
          rw [←hx,P.cut_rise,P.kills_lower (j+1) j (by omega)]
       refine le_trans ?_ (mul_le_mul_of_nonneg_left hv (norm_nonneg Q))
       exact (by simpa only [map_sub,hp,sub_zero] using! Q.le_opNorm (Y i-y))

-- after currency conversion, or taking the measuring frame in the
-- independent alphabet (composition from lower horizons allowed)
omit H in
lemma masterUpper (loc:Located L) (d j:ℕ) (u:ℝ→ C.label d)
    (hu : RateLE home ρ u 0): RateLE home ρ (fun r=> P.cutTest j d (master L d r (u r))) (-(j:ℝ)) := by
    let Z(r):= (L.shift d r).toContinuousLinearEquiv.toContinuousLinearMap
    have he:= (loc.rebased d).bil (u:=fun i=>Z i (u i)) hu (Eventually.of_forall fun i=> (Z i).le_opNorm _)
    rw [add_zero] at he
    exact engineeringUpper P L loc.level h d j _ he

omit H in
lemma inputUpper (loc:Located L) (d j:ℕ) (u:Slot C d) :
    RateLE home ρ (fun r=> P.cutTest j d (input L r d u)) (-(j:ℝ)) := by
   rcases u with u|v
   · exact masterUpper P L h loc d j (fun _=>u) (RateLE.const _ ageLarge)
   obtain ⟨p,hp,hP⟩:= loc.built d v
   apply RateLE.congr (RateLE.sum ageLarge (S:=Finset.univ)
       (fun i _=> masterUpper P L h loc i.val j (p i) (hp i)))
   filter_upwards [hP] with i hi
   change _ = P.cutTest j d (L.frame d i v)
   rw [hi,map_sum]
   exact Finset.sum_congr rfl (fun j _=> (P.cut_rise ..).symm)

end YM.RG17

