import YM.MS.High.Ribbon
/-!
# One step yielding closure and slice tests

Caps slicing for windows all t; actual cost forward/backwards. Assemble in
rank-inductive scheme after exhibiting Taylor coefficients & updating.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.High
open Function Filter Set Finset Real Plane Wire Flux Domain LogTime LogTime.IntervalFamily Momentum
open Landau Detect Koszul Logarithm Color
open scoped Topology ContDiff
variable {G:Gauge} {B B' F F': Recount G}
variable {h q v:ℤ} {d n s j:ℕ}
section
variable {c:ℂ} {b:Bool} {u:ℤ} {r:ℕ}
    (P : Spheres wave (spaceL G) B F c d b) (Q:Spheres id (spaceD G) B' F' c d b)
    (QG : Good b G h F')
-- grouping to reduce repeated compilation; structural premises remain. Include to list below.
structure Earlier (B B' F F' : Recount G) (b : Bool) (h : ℤ) (n d r:ℕ): Prop where
    prev (i:ℕ) (p : i∈paths n d) s :Trust b h (F i) (F' i) (s+1)
    prior (i:ℕ) (p : i∈paths n d) s : Trust true 4 (B (n-i)) (B' (n-i)) (s+1)
    loop : Trust b h (F n) (F' n) (r+2)

variable (hr : d≤ n) (hL : fig b r) (EE : Earlier B B' F F' b h n d r)
include hr hL EE P Q
private lemma understands {E} [NormedAddCommGroup E] [NormedSpace ℝ E] (w : Wire (Branch G Axis) E FourP) (hw : Course b w) (hp:w.length=r):
    Track b (F n) ((spaceL G).recu d c B F n) w ∧ Track b (F' n) ((spaceD G).recu d c B' F' n) w ∧ Light meet.primary (rate meet eps_gain) wfield (lane meet ((spaceL G).recu d c B F n)) (lane meet ((spaceD G).recu d c B' F' n)) w h :=
 ⟨P.road E w n hr (show fig b w.length from hp ▸ hL), Q.road E w n hr (show fig b w.length from hp ▸ hL), first_rhs hw (hp ▸ EE.loop) EE.prior EE.prev⟩
lemma advanced : Mature (F n-F' n) b r h where
    smooth E _ _ w hx hv x t:= by obtain ⟨ha,hb,hc⟩:= understands P Q hr hL EE w hx hv; exact ((ha hx).1 (x,t)).sub ((hb hx).1 (x,t))
    needs E _ _ w hw hv j hz x := by
       obtain ⟨ha,hb,hc⟩:= understands P Q hr hL EE w hw hv; exact origin_limit hw meet_start ha hb hc j ((int_need p_gain s_gain).mpr (by omega)) x

include QG
lemma closes (hx : u≤h) (he:Absent (F n-F' n) b r u) (v:ℝ) (w : List (Lane4 G)) (hp:Course b w): natQ (slice (F n-F' n) b r u v) w=0:= by
    let R:=advanced P Q hr hL EE; have HM E [NormedAddCommGroup E] [NormedSpace ℝ E] := R.smooth E
    let M := F n-F' n; let K:= slice M b r u v
    have ht l (h: l.length≠r) (hx : Course b l) : K l=0:= rank_slice _ hx h
    change natQ K w=0
    by_cases hw:w.length=r; swap
    · rw [natQ,visit_Z]; have hz : ∀ l i k, l++i::k=w→ ∑ j:Branch G Axis,(send id).table i.1 j i.2*K (l++(j,i.2)::k)=0:= by
         intro l i k hi; exact Finset.sum_eq_zero fun j hj=> mul_eq_zero_of_right _ (ht _ (by simpa only [← hi, List.length_append,List.length_cons] using hw) (visit_course b l k i (hi ▸ hp) j)) -- curry args
      rw [visit_agree _ _ (V:=fun _ _ _=>0) hz,visit_zero]
    let H:= criterion (R:=meet) (C:=G.ColorIndex) (A:= Axis) (primary_large s_gain.le)
    have hT : Frozen b wfield w.length M K u v:= hw ▸ (Mature.uses R hx he v)
    apply class_kernel H meet_start p_gain s_gain u hx hp (fun i hi hi' t=>HM ℝ (ray i) (ray_course hi) ((ray_len ..).trans (hi'.trans hw)) t.1 t.2) v hT
    rw [← ray_dim (m:=wfield) w]
    refine burn_cost H (ray_course hp) (F:=F n)  (H:=Ward wave (spaceL G) n d c B F) (K:=Ward id (spaceD G) n d c B' F') (G:=F' n) ?_ ?_ ?_ ?_
    · exact fun t i hi hi' => P.qfm n t i hr (by rw [hi',ray_len,hw]; exact hL) hi
    · exact fun t i hi hi' => Q.qfm n t i hr (by rw [hi',ray_len,hw]; exact hL) hi
    · exact second_rhs (ray_course hp) (by rw [ray_len,hw]; exact EE.loop) EE.prior EE.prev
    exact fun w hw' h=> QG ℝ n w hw' (by rw [h,ray_len,hw]; exact hL)
lemma terminal (hs : Rising b F) (hq : Rising b F') (hl : Absent (F n-F' n) b r (h+1)): Trust b h (F n) (F' n) r:= by
   intro E _ _ w hw hE
   obtain ⟨ha,hb,hc⟩:= understands P Q hr hL EE w hw hE; have hv:=advanced P Q hr hL EE
   refine orient hw meet_start ha hb hc p_gain.le ?_ (QG E n w hw (hE ▸ hL)) (fun j hj i=> hv.enough hl hw hE hj i)
   unfold Open; convert! (hs E n w hw (hE ▸ hL)).sub (hq E n w hw (hE ▸ hL)) using 1; ext; simp only [pays,t,start,meet, mul_zero,exp_zero,mul_one]
end
end YM.MS.High
