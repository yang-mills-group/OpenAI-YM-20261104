import YM.XSpace.PolePoint

/-!
# Nonzero leading null residues on the diagonal basis of curvature axes

It's enough that *some* axis-pair works for both endpoints. A complex polarization or spin
basis isn't needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Traverse
open Function Set Filter Maxwell Maxwell.Free Legs
open Polynomial hiding funext
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G : Gauge} {v u : E4} (H : Wheel v u)

def timer (v u : E4):= realLine ((interval v u)^3)
include H in
lemma zero_timer : Landing (timer v u) 0:=by
  rw [show Landing (timer v u) 0 ↔ Landing (timer v u) (jump ((interval v u)^3)) from ?_]; exact polynomial _
  rw [jump,eval_pow,show (interval v u).eval _=0 from H.spoke]; norm_num
lemma clock_at (t : ℝ): timer v u t=(rad 3 (course v u t):ℂ):=by unfold timer realLine; rw [eval_pow,show (interval v u).eval _= _ from along_square v u t]; simp only [rad,Complex.ofReal_pow]
include H in
lemma timer_back : timer (-v) u=timer v u:=by
  unfold timer; congr 2; unfold interval; rw [norm_neg,H.cross,H.back.cross]

-- moving K against Flavor(0). a reference color c chosen once
abbrev fresh (c : G.ColorIndex) (p q : Flavor 0) (v u : E4):= fun t=> timer v u t * (fare c p q (course v u t) : ℂ)
include H in
lemma feasible (c : G.ColorIndex) (p q : Flavor 0) : ∃ z,Landing (fresh c p q v u) z:=by
  let I (p : Flavor 0) : Paint G := ((⟨0,p⟩ : Key),c)
  obtain ⟨T,h⟩:= line_numerator (I p) (I q) v u; refine ⟨jump T,(polynomial T).congr ?_⟩
  filter_upwards [sliding (v:=v) H.runs] with t ht; rw [fresh,clock_at,h _ ht, Complex.ofReal_mul]; rfl

def flash (c : G.ColorIndex) (p : Flavor 0): Flavor 0 →ₗ[ℝ] ℂ where
  toFun q := (feasible H c p q).choose
  map_add' q q':=by
    have hf:= ((feasible H c p q).choose_spec).add (feasible H c p q').choose_spec
    refine (feasible H c p (q+q')).choose_spec.unique (hf.congr ?_)
    filter_upwards [sliding (v:=v) H.runs] with t ht; unfold fresh; rw [← mul_add, ← Complex.ofReal_add, ← show fare c p (q+q') (course v u t)= fare c p q (course v u t) + fare c p q' (course v u t) from _root_.map_add (assay c ht 0 0 p) q q']
  map_smul' a q:=by
    refine (feasible H c p (a • q)).choose_spec.unique ?_; rw [RingHom.id_apply,Complex.real_smul]
    refine ((constant (a:ℂ)).mul (feasible H c p q).choose_spec).congr ?_
    filter_upwards [sliding (v:=v) H.runs] with t ht; unfold fresh; rw [show fare c p (a • q) _=a* fare c p q _ from _root_.map_smul (assay c ht 0 0 p) a q]; push_cast; ring
lemma flashed (c : G.ColorIndex) (p q : Flavor 0): Landing (fresh c p q v u) (flash H c p q):= (feasible H c p q).choose_spec

private lemma face_lamp (c : G.ColorIndex) (i j : Axis) (h : i≠j) {x : E4} (hx:x≠0):
    rad 3 x * fare c (cell i j) (cell i j) x= 4*normal*(‖x‖^2- 2*(x i^2+x j^2)):=by
  let s:= omegaLeg c i j
  rw [show fare c (cell i j) (cell i j) x=K s s x 0 by rw [K,sub_zero]; rfl, omega_K_eq _ _ _ _ _ _ hx, if_pos rfl,sub_zero,bare_formula _ _ _ _ hx]
  have hk := norm_pos_iff.mpr hx; simp [wedge,house,houseM,kr_eq,h,h.symm,rad]; field_simp; ring

def forwards (i:Axis) (v u : E4):= C (v i:ℂ) + X*C (u i:ℂ)
def bulb (i : Axis) (v u : E4):= jump (forwards i v u)
lemma lamp (c : G.ColorIndex) (i j : Axis) (h : i≠j):
    flash H c (cell i j) (cell i j) = -8 * normal * (bulb i v u^2+ bulb j v u^2) :=by
  let P := (C ((4*normal:ℝ):ℂ))*(interval v u-C 2*(forwards i v u^2+ forwards j v u^2)); apply (flashed ..).unique
  have hf a t : realLine (forwards a v u) t=(course v u t a:ℂ):=by simp [realLine,course,forwards,eval_mul]; ring
  rw [← show jump P= -8 * normal * (bulb i v u^2+ bulb j v u^2) from ?_]; swap
  · unfold jump P bulb; simp only [eval_mul,eval_C,eval_sub,eval_add,eval_pow, show (interval v u).eval Complex.I=0 from H.spoke]; unfold jump; push_cast; ring
  refine (polynomial P).congr ?_; filter_upwards [sliding (v:=v) H.runs] with t ht
  unfold fresh; rw [clock_at, ← Complex.ofReal_mul, face_lamp _ _ _ h ht]; unfold realLine P; simp only [eval_mul, eval_C, eval_sub,eval_add,eval_pow,show (interval v u).eval _ = _ from along_square v u t]; simp_rw [show ∀ a,(forwards a v u).eval (t:ℂ)= (course v u t a:ℂ) from fun a=> hf a t]; push_cast; rfl
lemma bulb_back (i : Axis): bulb i (-v) u= -star (bulb i v u):=by simp [bulb,jump,forwards,eval_mul]; ring

lemma nonsingular (c : G.ColorIndex): ∃ p : Flavor 0, flash H c p p≠0 ∧ flash H.back c p p≠0:=by
  classical
  obtain ⟨i,j,hi,he⟩: ∃ i j,i≠j ∧ bulb i v u^2+bulb j v u^2 ≠0:=by
    by_contra h; push Not at h
    apply H.starts; ext i; change v i=0
    have hh : bulb i v u=0:=by
      obtain ⟨b,d,hb,hd,hg⟩ : ∃ b d:Axis,i≠b ∧ i≠d ∧ b≠d:= (by decide : ∀ i:Axis, ∃ b d: Axis,i≠b ∧ i≠d ∧ b≠d) i
      apply eq_zero_of_pow_eq_zero (n:=2); linear_combination ((h i b hb)+(h i d hd)-(h b d hg))/2
    simpa [bulb,jump,forwards,eval_mul] using congr_arg Complex.re hh
  let p:=cell i j
  have hk : (-8:ℂ)*(normal:ℂ) ≠0:=mul_ne_zero (by norm_num) (by exact_mod_cast normal_pos.ne')
  refine ⟨_, lamp H c i j hi |>.symm ▸ mul_ne_zero hk he,?_⟩
  rw [lamp H.back c i j hi]; apply mul_ne_zero hk; rw [bulb_back, bulb_back,neg_sq,neg_sq, ← star_pow, ← star_pow,← star_add]; exact star_ne_zero.mpr he
end YM.XSpace.Traverse
