import YM.Lattice.Site
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Physical mesh comparison geometry

Length units supplied by the caller. A deck motion may reflect and/or wind by
any whole period. Use sup norm on physical positions here (equivalent up to
prelength constant to manuscript convention). Inversion fixed-point distance
is distance to the grid of half-periods. A bridge detecting nontrivial
holonomy must actually pay such a distance.
-/

set_option autoImplicit false
noncomputable section

namespace YM.RegulatorIR
open Lattice Metric Function
open scoped Topology BigOperators Classical

abbrev Room := Axis → ℝ

inductive Motion
| across (v : Cover)
| turn (v : Cover)

namespace Motion
variable {P : ℝ}

def slide (P : ℝ) : Cover →+ Room where
  toFun x i := P * x i
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp [mul_add]

@[simp] theorem slide_apply (x:Cover) (i) : slide P x i = P * x i := rfl

def loc (P : ℝ) : Motion → Room → Room
 | across v, x => slide P v + x
 | turn v, x => slide P v + -x

def undo : Motion → Motion
 | across v => across (-v)
 | turn v => turn v

/-- deck sign - acts with - on positive-link coordinates relative to edge representatives -/
def sign : Motion → ℝ
| across _ => 1
| turn _ => -1

def combine : Motion → Motion → Motion
| across v, across w => across (v+w)
| across v, turn w => turn (v+w)
| turn v, across w => turn (v-w)
| turn v, turn w => across (v-w)

lemma sign_sq (τ:Motion) : sign τ * sign τ=1 := by cases τ <;> simp [sign]
@[simp] lemma undo_undo (t: Motion): undo (undo t)=t:=by cases t <;> simp [undo]
@[simp] lemma undo_loc (P) (t: Motion) (x): loc P (undo t) (loc P t x)=x:=by
  cases t <;> simp [loc,undo]
@[simp] lemma neutral_loc (P x) : loc P (across 0) x=x:=by simp [loc]
lemma combine_loc (P) (t u:Motion)(x) : loc P t (loc P u x)= loc P (combine t u) x := by
  cases t <;> cases u <;> simp [loc,combine] <;> abel
lemma cost_loc (P) (t:Motion)(x y) : dist (loc P t x) (loc P t y)=dist x y:=by
  cases t <;> simp [loc]
lemma cost_undo (P) (t:Motion)(x y) : dist (loc P t x) y= dist x (loc P (undo t) y):=by
  conv_lhs => rw [← cost_loc P (undo t),undo_loc]
end Motion

namespace Spatial
open Motion

def nearest (P : ℝ) (x : Room) : Cover := fun i=> round (x i / P)

/-- torus and quotient distances in physical units -/
def halfwidth (P : ℝ) (x : Room) := ‖x - slide P (nearest P x)‖ -- distance-to-zero modulo P
def wheel (P:ℝ) (x y : Room) := halfwidth P (x-y)
def distance (P:ℝ) (x y : Room) := min (wheel P x y) (wheel P x (-y))
def singular (P:ℝ) (x : Room) := halfwidth (P/2) x

lemma norm_near (h : ℝ) (hh : 0<h) (x : Room) (v : Cover) : halfwidth h x ≤ ‖x - slide h v‖:=by
  unfold halfwidth; apply (pi_norm_le_iff_of_nonempty ..).mpr
  intro i
  have hz : ‖(x-slide h (nearest h x)) i‖ ≤ ‖(x-slide h v) i‖:=by
    simp only [Pi.sub_apply, slide_apply, Real.norm_eq_abs]; unfold nearest
    have he (w : ℤ) : |x i - h*w| = h*|x i/h - w|:= by
      rw [show x i - h * w = h*(x i/h - w) by field_simp,abs_mul,abs_of_pos hh]
    simp_rw [he]; exact mul_le_mul_of_nonneg_left (round_le ..) hh.le
  exact hz.trans ((pi_norm_le_iff_of_nonempty _).mp le_rfl i)
lemma halfwidth_le (h : ℝ) (hh : 0<h) (x : Room) : halfwidth h x ≤ h/2 :=by
  unfold halfwidth; apply (pi_norm_le_iff_of_nonempty ..).mpr; intro i
  simp only [Pi.sub_apply,slide_apply,Real.norm_eq_abs,nearest]
  have he (w:ℤ) : |x i-h*w|= h*|x i/h-w|:=by
    rw [show x i-h*w=h*(x i/h-w) by field_simp,abs_mul,abs_of_pos hh]
  rw [he]
  exact (mul_le_mul_of_nonneg_left (abs_sub_round ..) hh.le).trans_eq (by ring)
variable {P : ℝ} (hp:0<P)

lemma wheel_eq (P : ℝ) (x y : Room) : wheel P x y=dist x (slide P (nearest P (x-y)) + y) := by unfold wheel halfwidth; rw [dist_eq_norm,show x - (slide P (nearest P (x-y))+y) = x - y - slide P (nearest P (x-y)) by abel]
lemma realizes (P : ℝ) (x y : Room) : ∃ d : Motion, distance P x y = dist x (loc P d y) := by
  unfold distance; rcases le_total (wheel P x y) (wheel P x (-y)) with h|h
  · rw [min_eq_left h]; exact ⟨across _,wheel_eq P x y⟩
  rw [min_eq_right h]; exact ⟨turn _,wheel_eq P x (-y)⟩

lemma distance_nonneg (P : ℝ) (x y : Room) : 0≤distance P x y:= le_min (norm_nonneg _) (norm_nonneg _)
lemma singular_nonneg (P : ℝ) (x : Room) : 0≤singular P x := norm_nonneg _
include hp
lemma wheel_le (x y v) : wheel P x y ≤ dist x (slide P v + y) := by
  unfold wheel; rw [dist_eq_norm,show x - (slide P v + y) = x-y-slide P v by abel]; exact norm_near P hp (x-y) v
lemma distance_le (x y d) : distance P x y ≤ dist x (loc P d y) := by
  cases d
  · exact le_trans (min_le_left ..) (wheel_le hp ..)
  exact le_trans (min_le_right ..) (wheel_le hp ..)
lemma distance_self (x : Room) : distance P x x=0 :=
  le_antisymm ((distance_le hp x x (across 0)).trans_eq (by simp)) (distance_nonneg ..)
lemma distance_comm (x y) : distance P x y=distance P y x := by
  have h (x y : Room) : distance P x y ≤ distance P y x := by
    obtain ⟨v,hv⟩ := realizes P y x
    rw [hv,dist_comm y _,cost_undo]; exact distance_le hp _ _ _
  exact le_antisymm (h _ _) (h _ _)
lemma distance_triangle (x y z : Room) : distance P x z ≤ distance P x y + distance P y z := by
  obtain ⟨d,he⟩:= realizes P x y
  obtain ⟨c,hc⟩:= realizes P y z
  rw [he,hc,← cost_loc P d y _,combine_loc]; exact le_trans (distance_le hp _ _ _) (dist_triangle ..)
lemma distance_deck (x y d): distance P x (loc P d y) = distance P x y:= by
  have H (x y d) : distance P x y ≤ distance P x (loc P d y) := by
     obtain ⟨f,h⟩:=realizes P x (loc P d y)
     rw [h,combine_loc]; exact distance_le hp _ _ _
  have h := H x (loc P d y) (undo d)
  rw [undo_loc] at h
  exact le_antisymm h (H x y d)
omit hp in
private lemma step_twice (v : Cover) : slide P v= slide (P/2) (v+v):=by ext i; simp only [slide_apply,Pi.add_apply,Int.cast_add]; ring
lemma singular_deck (x d) : singular P (loc P d x) = singular P x := by
  let h:=P/2; have he : 0<h:=half_pos hp
  have H (z:Room) (w : Motion) : singular P (loc P w z) ≤ singular P z := by
    cases w with
    | across v =>
      apply le_trans (norm_near h he _ (v+v+nearest h z))
      rw [loc,map_add,← step_twice]; unfold singular halfwidth; apply le_of_eq; congr 1; dsimp [h]; abel
    | turn v =>
      apply le_trans (norm_near h he _ (v+v-nearest h z)); rw [loc,map_sub,← step_twice]
      rw [← norm_neg (slide P v + _ - _)]; unfold singular halfwidth; apply le_of_eq; congr 1; dsimp [h]; abel
  exact le_antisymm (H x d) (by simpa only [undo_loc] using H (loc P d x) (undo d))
lemma singular_lip (x y : Room) : singular P x ≤ singular P y + distance P x y := by
  obtain ⟨f,h⟩:=realizes P x y
  rw [h, ← singular_deck hp y f]
  let v:=loc P f y; let n:=nearest (P/2) v
  apply (norm_near (P/2) (half_pos hp) x n).trans
  change ‖_‖ ≤ ‖v-slide (P/2) n‖ + dist x v
  rw [dist_eq_norm, add_comm]; apply (le_of_eq (congr_arg _ _)).trans
  · exact norm_add_le (x-v) (v-slide (P/2) n)
  abel
lemma across_far (x : Room) {v : Cover} (hn : v ≠ 0) : P ≤ dist x (loc P (across v) x) := by
  unfold loc
  rw [dist_eq_norm,show x- (slide P v + x)= -slide P v by abel,norm_neg]
  obtain ⟨i,hi⟩:= Function.ne_iff.mp hn
  apply le_trans ?_ ((pi_norm_le_iff_of_nonempty (slide P v)).mp le_rfl i)
  rw [slide_apply,norm_mul,Real.norm_of_nonneg hp.le,Real.norm_eq_abs, ← Int.cast_abs]; exact le_mul_of_one_le_right hp.le (by exact_mod_cast Int.one_le_abs hi)
lemma turn_far (x v) : 2*singular P x ≤ dist x (loc P (turn v) x) := by
  rw [dist_eq_norm,loc,show x- (slide P v + -x)=(2:ℝ) • (x-slide (P/2) v) by
    ext i; simp; ring,norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (norm_near (P/2) (half_pos hp) x v) (by norm_num)
lemma singular_bound (x) : singular P x ≤ P := (halfwidth_le _ (half_pos hp) x).trans (by linarith)
lemma holonomy (x) {t} (ht:t≠Motion.across 0) : singular P x ≤ dist x (loc P t x) := by
  cases t with
  | across v => exact le_trans (singular_bound hp x) (across_far hp x (fun h=>ht (h ▸ rfl)))
  | turn v => linarith only [singular_nonneg P x,turn_far hp x v]
end Spatial
end YM.RegulatorIR
