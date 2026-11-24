import YM.XSpace.Island
/-! # Three-line distributional integral point prescription

 Its value under ANY clearance cutoff. `source` spells out ordinary product derivatives with their integration-by-parts sign, local chart centered at first argument only. No volume in the exact theory. Uses absolute and signed moves from **bare path diagrams**; does NOT adjust contact terms since this computes *the invariant* diagnostic (used next in the registered scene). See §iv/tri and `Normal` later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Season
open Function MeasureTheory Filter Set Relief Sail Playpen Trace Litter Octave Lattice Further.FreeCovariance.KP Tide
open scoped Topology BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x y z:ι→Cover}{u v b:E4} {A B C:Toe} {f g h:Breeze}
variable (c:Shade.Cut)
private lemma chain (k:ℕ) (x y z:Cover)(p:ℝ)(hx:A∈Terrain k)(hy:B∈Terrain 3)(hz:C∈Terrain 3)(hk:4<k+3):Summable fun w:Cover=> A (w-x)*chart c p x y z B C w:=by
  apply Summable.of_norm_bounded (form_sum hx hy hz hk x y z).norm; intro w; unfold chart Form string; rw [mul_left_comm (A _),norm_mul,mul_assoc (A _)]; exact mul_le_of_le_one_left (norm_nonneg _) (cash_fee ..)
lemma share (x y z:Cover)(p:ℝ)(t:Axis)(hx:A∈Terrain 3)(hy:B∈Terrain 3)(hz:C∈Terrain 3):(∑' w:Cover,uses p x (D t A) (chart c p x y z B C) w)=∑' w:Cover,uses p x A (η t (chart c p x y z B C)) w:=by
  unfold uses; rw [tsum_mul_left,tsum_mul_left]; apply congr_arg; let f(w:Cover):= A (w-x); let g:=chart c p x y z B C; rw [← duet_dual f g t (by apply (chain c 3 x y z p (slide_hill hx (step t)) hy hz (by norm_num)).congr; intro w; change A (step t+(w-x))*_ = A (w+step t-x)*_; congr 2; abel) (chain c 3 x y z p hx hy hz (by norm_num))] -- rhs match
  apply tsum_congr; intro i; change (A (i-x+_)-_)*_=(A (i+_-x)-_)*_; rw [sub_add_eq_add_sub]
private lemma opposite (p:ℝ)(x y w:Cover)(h:4*c.rOut≤ ‖actual p (x-y)‖): cash c p (w-x)=0 ∨ cash c p (w-y)=0:= by
  by_contra! hh; have hx:=status c _ _ hh.1; have hy:=status c _ _ hh.2; rw [show x-y=w-y-(w-x) by abel, ar_sub] at h; linarith [norm_sub_le (actual p (w-y)) (actual p (w-x)), c.rOut_pos]
private lemma globe (p:ℝ)(x y z:Cover)(A B C:Toe)(w:Cover)(h:4*c.rOut ≤ ‖actual p (x-y)‖)(h':4*c.rOut ≤ ‖actual p (x-z)‖)(h'':4*c.rOut ≤ ‖actual p (y-z)‖) : p⁻¹^6* Form x y z A B C w= drape c p x y z A B C w + uses p x A (chart c p x y z B C) w+ uses p y B (chart c p y x z A C) w+uses p z C (chart c p z x y A B) w:=by
  unfold Form drape uses chart string later strip -- strip order?
  rcases opposite c p x y w h with e|e <;> rcases opposite c p x z w h' with hh|hh <;> rcases opposite c p y z w h'' with he|he <;> simp only [e,hh,he] <;> ring
lemma stellar (p:ℝ)(x y z:Cover)(hx:A∈Terrain 4)(hy:B∈ Terrain 3)(hz:C∈Terrain 3)(h:4*c.rOut ≤ ‖actual p (x-y)‖)(h':4*c.rOut ≤ ‖actual p (x-z)‖)(h'':4*c.rOut ≤ ‖actual p (y-z)‖): p⁻¹^6* Trail x y z A B C=(∑' w:Cover, drape c p x y z A B C w)+(∑' w:Cover, uses p x A (chart c p x y z B C) w)+(∑' w:Cover,uses p y B (chart c p y x z A C) w)+∑' w:Cover,uses p z C (chart c p z x y A B) w:=by
  have a:= sums_ext c x y z p hx hy hz; have b:= (chain c 4 x y z p hx hy hz (by norm_num)).mul_left (p⁻¹^6); have he:= revel c p y x z hy hx hz (by norm_num); have H:=revel c p z x y hz hx hy (by norm_num); unfold Trail; rw [← tsum_mul_left]; change _= ((∑' w:Cover,drape c p x y z A B C w) +(∑' w:Cover,p⁻¹^6*(A (w-x)*chart c p x y z B C w)))+_+_; -- syntax
  rw [← a.tsum_add b, ← (a.add b).tsum_add he, ← ((a.add b).add he).tsum_add H]; exact tsum_congr fun w=> globe c p x y z A B C w h h' h''
-- distribution integral in the position Taylor extension for single lines
variable (t:Axis)
def visible (u v b:E4)(f g h:Breeze): Breeze:=suburb c u v b (Maxwell.grad t f) g h
def sample (u v b:E4)(f g h:Breeze):Breeze:=fun w=>g w* green c v u b (Maxwell.grad t f) h w
def idle (u v b:E4)(f g h:Breeze):Breeze:=fun w=> f w * source c t u v b g h w
structure Pays₃ (u v b:E4)(f g h:Breeze): Prop where
 out: Integrable (visible c t u v b f g h)
 primary: Integrable (idle c t u v b f g h)
 second: Integrable (sample c t u v b f g h)
 third: Integrable (sample c t u b v f h g)
def moving (u v b:E4)(f g h:Breeze): ℝ:= (∫ i:E4,visible c t u v b f g h i)+(∫ i:E4,idle c t u v b f g h i) +(∫ i:E4, sample c t u v b f g h i)+ (∫ i:E4, sample c t u b v f h g i)
variable (s: Stage L a)(X:distance L a x u)(Y:distance L a y v)(Z:distance L a z b) (R:range c u v)(S:range c u b)(O:range c v b)
include s X Y Z R S O in
lemma lights [L.IsCountablyGenerated][NeBot L](hx:Beam 3 A f)(hy:Beam 3 B g)(hz:Beam 3 C h):
  Pays₃ c t u v b f g h ∧ Tendsto (fun i=> (a i)⁻¹^6* Trail (x i) (y i) (z i) (D t A) B C) L (𝓝 (moving c t u v b f g h)):=by
  have he:= suburb_cost c s X Y Z (hx.step_forth t) hy hz; have he':=emergence c s X Y Z R S hx hy hz t; have hh:=patron c s Y X Z (range_sym c R) O hy (hx.step_forth t) hz; have h':=patron c s Z X Y (range_sym c S) (range_sym c O) hz (hx.step_forth t) hy; refine ⟨⟨he.2,he'.2,hh.2,h'.2⟩,(((he.1.add he'.1).add hh.1).add h'.1).congr' ?_⟩; filter_upwards [toll c R X Y,toll c S X Z,toll c O Y Z] with i hi ht hv; rw [stellar c _ _ _ _ (steps_hill hx.glows t) hy.glows hz.glows hi ht hv,share c _ _ _ _ _ hx.glows hy.glows hz.glows]; rfl
end YM.XSpace.Season
