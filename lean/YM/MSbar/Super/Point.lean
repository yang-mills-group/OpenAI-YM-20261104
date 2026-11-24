import YM.MSbar.Super.Drift

/-!
# Cross contraction calculus

Supersymmetry, derivation in the second slot; include inputs of both grades.
Useful also for nonlinear drives. No restriction on the specific masks beyond
chargedness and/or exchange as needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Super
open Function Finset
open scoped BigOperators
variable {α : Type*} [Fintype α] {p : α → Bool}
variable {f g h : Term α} {d r s : Bool} {B C : Mask α}

omit [Fintype α] in
lemma twist_cube (x y r s : Bool) : twist y (x.xor r)* (twist x y * twist (x.xor r) (y.xor s)) = twist r s * twist x (y.xor s) := by cases r <;> cases s <;> cases x <;> cases y <;> simp
lemma Grade.cross_comm (F : Grade p r f) (G : Grade p s g) (H : Exchange p C) : Super.cross p C f g=twist r s • Super.cross p C g f := by
  unfold Super.cross; rw [sum_comm]; simp only [smul_sum]; apply sum_congr rfl; intro y hy; apply sum_congr rfl; intro x hx
  rw [F.flash, G.flash, grade_mix_comm (F.peel x) (G.peel y), H x y, smul_smul,smul_smul]
  congr 1; linear_combination C y x * twist_cube (p x) (p y) r s
lemma Grade.cross_mix (F : Grade p r f) (G : Grade p s g) (H : Access p d C) (h : Term α) : Super.cross p C f (Super.mix p g h)=
    Super.mix p (Super.cross p C f g) h+twist (d.xor r) s • Super.mix p g (Super.cross p C f h) := by
  simp only [Super.cross,mix_sum_first,mix_sum_last,smul_sum, ←sum_add_distrib]; apply sum_congr rfl; intro x hx; apply sum_congr rfl; intro y hy
  by_cases e : C x y=0
  · simp [Super.crossMask,e]
  rw [← H x y e]; simp only [F.flash _,G.peel_mix h,mix_add_last,mix_smul_first,mix_smul_last,smul_add]
  rw [grade_mix_assoc (F.peel x) (G.peel y),← grade_mix_assoc (F.peel x) G, grade_mix_comm (F.peel x) G,
        mix_smul_first,grade_mix_assoc G (F.peel x)]
  cases p x <;> cases p y <;> cases r <;> cases s <;> simp

omit [Fintype α] in
lemma even_mix_comm (F : Grade p false f) (G : Grade p s g) : mix p f g=mix p g f := by simpa using grade_mix_comm F G
lemma even_cross_comm (F : Grade p false f) (G : Grade p s g) (E : Exchange p C) : cross p C f g=cross p C g f := by simpa using F.cross_comm G E
lemma even_bell_mix (F : Grade p false f) (H : Access p d C) (E : Exchange p C) (g : Term α) : bell C (mix p f g)=mix p (bell C f) g+mix p f (bell C g)+cross p C f g := by simpa using F.bell_mix H E g
lemma even_ride_mix {T : Drive α} (F : Grade p false f) (H : Coach p d T) (g : Term α) : ride p T (mix p f g)=mix p (ride p T f) g+mix p f (ride p T g) := by simpa using F.ride_mix H g
omit [Fintype α] in
lemma even_mix (F : Grade p false f) (G : Grade p s g) : Grade p s (mix p f g) := by simpa using F.mix G
lemma even_bell (F : Grade p false f) (H : Access p d C) : Grade p d (bell C f) := by simpa using F.bell H
lemma even_cross (F : Grade p false f) (G : Grade p false g) (H : Access p d C) : Grade p d (cross p C f g) := by simpa using F.cross G H
lemma even_cross_mix (F : Grade p r f) (G : Grade p false g) (H : Access p d C) (h : Term α) : cross p C f (mix p g h)=mix p (cross p C f g) h+mix p g (cross p C f h) := by simpa using F.cross_mix G H h
omit [Fintype α]
lemma access_zero : Access p d (0 : Mask α) := by simp [Access]
lemma Access.sub (F : Access p d B) (G : Access p d C) : Access p d (B-C) := by
  intro x y h; by_cases e : B x y=0
  · apply G; simpa [e] using h
  · exact F x y e
lemma Exchange.sub (F : Exchange p B) (G : Exchange p C) : Exchange p (B-C) := by intro x y; simp only [Pi.sub_apply]; rw [F x y,G x y,mul_sub]
end YM.MSBar.Super
