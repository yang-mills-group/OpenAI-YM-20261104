import YM.XSpace.Screening
/-!
# Local issuance (with three distinct positions)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Season
open Function MeasureTheory Filter Set Relief Sail Playpen Trace Litter Octave Lattice Further.FreeCovariance.KP Tide
open scoped Topology BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x y z:ι→Cover}{u v b:E4} {A B C:Toe} {f g h: Breeze} {k j:ℕ}
variable (c:Shade.Cut)
def chart (a:ℝ)(x y z:Cover)(B C:Toe): Toe:= fun w=> cash c a (w-x)*string B C y z w
def green (u v b:E4)(g h:Breeze)(w:E4):ℝ:= c w * (g (w+u-v)* h (w+u-b))
def uses (a:ℝ)(x:Cover)(A B:Toe):Toe := fun w=> a⁻¹^6* (A (w-x)*B w)
-- real sector estimator
variable (s:Stage L a)(X:distance L a x u)(Y:distance L a y v)(Z:distance L a z b) (R:range c u v)(R':range c u b)
include s in
lemma stormy (P:ι→Toe) (p:Breeze)(h0:∀ᵐ w:E4,Tendsto (fun i=> (a i)⁻¹^7 * P i (mark (a i) w+x i)) L (𝓝 (p w))) (hX:Beam 3 A f)
     (T:∃ C:ℝ,0≤C∧∀ᶠ i in L,∀ w,P i w≠0→perch c (a i) (w-x i) ∧ ‖P i w‖ ≤ C* a i^7) [L.IsCountablyGenerated][NeBot L]:
      Consummate L (fun i=> uses (a i) (x i) A (P i)) (fun x=> f x*p x):=by
  obtain ⟨D,hD,H⟩:= T; obtain ⟨C,hC,J⟩:=sonar (show A∈Terrain 3 from hX.glows); apply located (x:=x); apply price s (C*D) (3*c.rOut) (mul_nonneg hC.le hD); swap
  · filter_upwards [h0,almost_all] with w hw hf; refine ((shines s (marks w s.zero s.good) hf hX).mul hw).congr fun i=>?_; unfold down uses; dsimp only; rw [add_sub_cancel_right]; ring
  filter_upwards [H,s.good,s.zero.eventually (ge_mem_nhds c.rOut_pos)] with i hi hh ht w hw; unfold uses at * -- painful
  obtain ⟨hQ,hx⟩:= hi (w+x i) (right_ne_zero_of_mul (right_ne_zero_of_mul hw)); rw [add_sub_cancel_right] at hQ; refine ⟨perch_cost c hh ht hQ,?_⟩; rw [add_sub_cancel_right,norm_mul,norm_mul,Real.norm_of_nonneg (pow_nonneg (by positivity) _ )]; exact (mul_le_mul_of_nonneg_left (mul_le_mul (J w) hx (norm_nonneg _) (mul_nonneg hC.le (sound ..).le)) (by positivity)).trans_eq (by field_simp <;> ring)
include c in
lemma revel (p:ℝ)(x y z:Cover)(hx:A∈Terrain 3) (hy:B∈Terrain k)(hz:C∈Terrain j)(h:4<3+k) : Summable fun w:Cover=> uses p x A (chart c p x y z B C) w:= by
  apply Summable.mul_left; refine Summable.of_norm_bounded (form_sum hx hy hz h x y z).norm fun w=>?_ ; unfold Form chart string; rw [mul_left_comm (A _),mul_assoc (A _),norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (cash_fee ..)
lemma noncash (p:ℝ)(x y z w:Cover)(Q:chart c p x y z B C w≠0): perch c p (w-x):= starter c _ _ (left_ne_zero_of_mul Q)
def ae_clear (u v b:E4)(w:E4):Prop:= w≠0 ∧ w+u-v≠0∧w+u-b≠0
lemma clear_all (u v b:E4): ∀ᵐ w:E4, ae_clear u v b w:=by filter_upwards [remaining (v-u),remaining (b-u),almost_all] with w hv hw hV; exact ⟨hV, sub_ne_zero.mpr (fun h=> hv (eq_sub_of_add_eq h)), sub_ne_zero.mpr (fun h=>hw (eq_sub_of_add_eq h))⟩
include s X Y Z R R' in
lemma patron (hx: Beam 3 A f)(hy: Beam 4 B g)(hz: Beam 3 C h)[L.IsCountablyGenerated][NeBot L]:
  Consummate L (fun i=> uses (a i) (x i) A (chart c (a i) (x i) (y i) (z i) B C)) (fun w=> f w * green c u v b g h w):=by
  refine stormy c s _ _ ?_ hx ?_; swap
  · obtain ⟨D,hD,H⟩:= teaches _ (show B∈Terrain 4 from hy.glows) _ c.rOut_pos; obtain ⟨C,hC,J⟩:= teaches _ (show C∈ Terrain 3 from hz.glows) _ c.rOut_pos; refine ⟨D*C,(mul_pos hD hC).le,?_⟩; filter_upwards [s.good,toll c R X Y, toll c R' X Z] with i hi hh hz w hw; let p:= a i; have he:=noncash c _ _ _ _ _ hw; refine ⟨he,?_⟩; unfold chart string; rw [norm_mul]; apply (mul_le_of_le_one_left (norm_nonneg _) (cash_fee c _ _)).trans; rw [norm_mul]; exact (mul_le_mul (H _ _ hi (resolved c _ _ _ _ hh he)) (J _ _ hi (resolved c _ _ _ _ hz he)) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  refine (clear_all u v b).mono fun w ⟨_,hv,hb⟩=>?_ ; have he:= since (marks w s.zero s.good) X; have hh:= ((shines s (value he Y) hv hy).mul (shines s (value he Z) hb hz)); refine ((shuffled c (marks w s.zero s.good)).mul hh).congr fun i=>?_; unfold chart string; rw [add_sub_cancel_right]; ring
-- terminology care: f(x)* limit.
end YM.XSpace.Season
