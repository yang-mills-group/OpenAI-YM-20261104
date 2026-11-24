import YM.X.Chir.Flocks
/-!
# Large triangle bounds architecture: z at remote, pathwise fees. lens. Site metric
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Imprint
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R t c:ℝ}
local notation "S"=> Site n
local notation "D"=>Interval.mass
local notation "p"=>fund
variable (x y z:Site n)
-- white Plateau D(z,x) width. in physical potential lessons seven order
def clipY (d:ℝ):ℝ:= min 1 (max 0 d)
lemma clip_back (a b R:ℝ)(h:a-b≤R)(hv:R≥0): clipY a-clipY b ≤ R:= by unfold clipY; simp only [min_def,max_def]; split_ifs <;> linarith
lemma clip_n  (a:ℝ):0≤clipY a ∧ clipY a≤1:= ⟨le_min zero_le_one (le_max_left ..),min_le_left ..⟩
def lens (d:ℝ)(x i:S) : ℝ:= clipY ((d/4-D x i)/(d/8))
lemma lenses : 0≤lens r x z ∧ lens r x z≤1:= clip_n _
lemma lens_white (hr:r>0)(hx:D x z ≤ r/8): lens r x z=1:= by
    have hh : (r/4-D x z)/(r/8)≥ 1:= by rw [ge_iff_le,le_div_iff₀ (by positivity)]; linarith
    rw [lens,clipY,min_eq_left (le_trans hh (le_max_right ..))]
lemma lens_off (hr:r>0)(hx:r/4 ≤ D x z): lens r x z=0:= by rw [lens,clipY,max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (by positivity)),min_eq_right zero_le_one]
lemma flux_l (hr:r>0)(i:Axis): ‖lens r x z-lens r x (z+step i)‖≤ 8*r⁻¹:= by
     unfold lens; rw [Real.norm_eq_abs]; have hx:=stride x z i; have hh :8*r⁻¹=1/(r/8):= by field_simp
     rw [hh]; apply abs_le.mpr; constructor; rw [neg_le,neg_sub]; all_goals apply clip_back; rw [← sub_div]; gcongr; linarith; positivity -- syntax
abbrev PreachY (d:ℕ)(x:S)(F:S→ℝ)(c:ℝ):=∀ i:Axis, Paying x d c (fun z=> F (z+step i)-F z)
-- within cost during walk if lower distance fixed.We don't require constant turns.
lemma telescope (T:Lattice.Walk) (F:S→ℝ)(Y:PreachY k z F c) (ht:r>0)(hc:c≥0)(hr:T.length+r ≤ D z x) : ‖F (stop x T)-F x‖ ≤ T.length*(c*r⁻¹^k) := by
    induction T generalizing x with
    | nil=>simp [stop]
    | cons i T IH=>
       let t:= T.length; have he : ((t:ℝ)+1)+r≤D z x:=by simpa using hr
       let u:Site n:=x+i.vec; have hg : D z u+1 ≥ D z x:= by
          unfold u Step.vec; split; next=> have hh:=(stride z (x-step i.dir) i.dir).2; rwa [sub_add_cancel,sub_eq_add_neg] at hh -- negative
          next=> exact (stride z x ..).1
       have hy: t+r ≤ D z u:=by linarith only [he,hg]
       have hq : ‖F u-F x‖ ≤ c*r⁻¹^k:= by
          have hl : ∀ v:Site n,r ≤ D z v→ ‖F (v+step i.dir)-F v‖ ≤ c*r⁻¹^k:= fun v hv=>(Y i.dir v).trans (mul_le_mul_of_nonneg_left (by simpa using (charge (k:=k) z v (R:=r) (c:=1) (by simpa) ht)) hc);
          have hv:r ≤ D z u:= by linarith only [hy,Nat.cast_nonneg (α:=ℝ) t]
          unfold u Step.vec at hv ⊢; cases he:i.neg <;> simp only [he,Bool.false_eq_true,if_false, if_true] at hv ⊢
          · exact hl x (by linarith only [show ((t:ℝ)+1)+r≤D z x from by assumption, Nat.cast_nonneg (α:=ℝ) t])
          · specialize hl (x + -step i.dir) hv; rw [add_assoc,neg_add_cancel,add_zero] at hl; rwa [norm_sub_rev] at hl
       rw [stop,List.length_cons,Nat.cast_add, Nat.cast_one,add_mul,one_mul]; exact (norm_sub_le_norm_sub_add_norm_sub (F (stop u T)) (F u) (F x)).trans (add_le_add (IH u hy) hq) -- reorder
-- route length check from Stationary
lemma route_len : ∃ L:Lattice.Walk, stop x L=y ∧ L.length≤4* separation x y:= by
    let v:= lift (y-x); let a:=route (0:Cover) v 1; have hx(l:Lattice.Walk)(z:S):stop (x+z) l=x+stop z l:= by induction l generalizing z with|nil=>rfl| cons a l ih=> rw [stop,stop, add_assoc,ih]
    have he : stop x a=y:= by rw [← add_zero x, hx, ← map_zero (wrap n), ← wrap_stop_cover,show stop (0:Cover) a= v from route_end ..,wrap_lift,add_sub_cancel]; -- check
    refine ⟨a,he,?_⟩; unfold a; rw [Stationary.route_length,sub_zero, separation_comm]; exact round_lift _ -- context import
lemma postage (F:S→ℝ)(he:c≥0)(h8:D x y ≤ D x z / 16)(hp : PreachY 5 z F c): ‖F y-F x‖ ≤ (128*c) * p 5 x z * D x y:= by
    obtain ⟨T,rfl',hT⟩:= route_len x y; let a:=D x y; let b:=D x z; have hb:0 < b:= pay_pos x z; have hl : (T.length:ℝ)≤4*D x y:= by
        apply le_trans (b:=4*(separation x y:ℝ)) (by exact_mod_cast hT); unfold Interval.mass ticketN; push_cast; linarith
    refine le_trans (b:=T.length * (c*(b/2)⁻¹^5)) ?_ ?_; · rw [← rfl']; apply telescope x z T F hp (by positivity) he; rw [comm z x]; linarith only [hl,h8,hb,show b=D x z from rfl]
    refine le_trans (mul_le_mul_of_nonneg_right hl (by positivity : 0≤ c*(b/2)⁻¹^5)) (le_of_eq ?_); unfold b fund; field_simp; ring
end YM.PositionX.Chir.Imprint
