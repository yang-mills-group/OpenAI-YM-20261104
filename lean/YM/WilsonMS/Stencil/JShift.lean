import YM.WilsonMS.Stencil.JFirst
/-!
# Transform the full Section reading
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.JRad
open Function Filter Set Finset MeasureTheory Real
open MS Plane Koszul Heat Flux Landau Arts Pilot Spin Wire Rock _root_.YM.MS.Shine Outlook
open MvPolynomial Labels Analysis Tensor Maxwell Motif Halo Mach Lifting Theater HBeam Detect
  Detect.Mark Local.BV InnerProductSpace
open Garment Color
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G : Gauge} {m n k i j : ℕ} {z : ℂ} {a b c : Axis}
section pulse
variable {E : Type} [AddCommGroup E] [Module ℂ E]
variable (s : Signed)
local notation "S" => s.ortho

abbrev raised (s : Signed) (n : ℕ) (G : Gauge) : Surf G n n :=
  Surf.orbit (grip s) G
local notation "Y" => (raised s n G)

lemma physical_profile (a b : Axis) :
    (raised s n G).profile (chair n a) (chair n b) = ((S).val b a : ℂ) := by
  let Q := hand s
  let h := Nat.zero_le n
  change (↑((arch h Q).profile _ _) : ℂ) = _
  rw [chair, Spin.ray_taller]
  rw [show ((Q.profile _ _) : ℂ) = _ from hand_s s a b]
  by_cases he : s.perm a = b <;> cases hx : s.flip a <;>
    simp [Signed.ortho, Signed.matrix_at, *, Koszul.cross]

lemma profile_out (u : Apart 0 n) (b : Axis) :
    (raised s n G).profile (aside (Nat.zero_le n) u) (chair n b) = 0 := by
  let Q := grip (n := n) s
  let h := Nat.zero_le n
  change (((Q.profile _ _) : ℝ) : ℂ) = _
  rw [profile, sends, split_right, flare_r, one_smul]
  simp [spray, nowhere]

lemma sectionK (G : Gauge) (i : Axis) (F : Arts.L n → E) :
    (∑ j : Arts.L n, (raised s n G).profile j (chair n i) • F j) =
      ∑ j : Axis, ((S).val i j : ℂ) • F (chair n j) := by
  rw [cut_sum (Nat.zero_le n)]
  simp only [show ∀ u : Apart 0 n, (raised s n G).profile (aside _ u) (chair n i) = 0 from fun u =>
        profile_out s u i,
    zero_smul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (raised s n G).profile (rises _ j) (chair n i) = _ from physical_profile s j i]

lemma moves_by (x : E4) (b : Axis) : ∑ a : Axis, x a * (S).val a b = Ortho.move S⁻¹ x b := by
  rw [Ortho.move, M4.at_coord]
  exact Finset.sum_congr rfl fun i _ => mul_comm ..

lemma passport (z : ℂ) (x : E4) (F : Mield G n) :
    (raised s n G).air (direction G n z x F) =
      direction G n z (Ortho.move S⁻¹ x) ((raised s n G).air F) := by
  unfold direction
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  simp_rw [map_sum, LinearMap.smul_apply, map_smul, Surf.grip, sectionK, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Complex.ofReal_mul, ← Complex.ofReal_sum, moves_by]

lemma carries_ray (x : E4) (a b : Axis) (i : ℕ) :
    (raised s n G).air (rayF z x a b i) =
      ∑ j : Axis,
        ((S).val a j : ℂ) • ∑ k : Axis, ((S).val b k : ℂ) • rayF z (Ortho.move S⁻¹ x) j k i := by
  let T (p : Axis) q := cur z (chair n p) (chair n q) (G := G)
  induction i with
  | zero => simp_rw [rayF, pow_zero, Module.End.one_apply, Surf.earth, sectionK]
  | succ i ih =>
    simp only [rayF, pow_succ', Module.End.mul_apply]
    unfold rayF at ih
    simp only [passport, ih, map_sum, map_smul]

lemma carries_node (x : E4) (a : Axis) (z : ℂ) (i : ℕ) :
    (raised s n G).air (node z a i x) =
      ∑ j : Axis, ((S).val a j : ℂ) • node z j i (Ortho.move S⁻¹ x) := by
  let F := fun (p : Axis) b => rayF (G := G) (n := n) z (Ortho.move S⁻¹ x) p b i
  unfold node
  rw [LinearMapRealm, map_sum]
  simp_rw [LinearMapRealm (raised s n G).air, carries_ray]
  suffices hp :
    ∑ b : Axis, x b • ∑ j : Axis, ((S).val b j : ℂ) • ∑ k : Axis, ((S).val a k : ℂ) • F j k =
      ∑ k : Axis, ((S).val a k : ℂ) • ∑ j : Axis, (Ortho.move S⁻¹ x) j • F j k
    from by
    change volume i • _ = _
    rw [hp, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm ..
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  nth_rw 2 [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← moves_by, Finset.sum_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_smul]
  let v := F j k
  let c : ℂ := (S).val a k
  let w : ℂ := (S).val b j
  let u : ℂ := x b
  change u • w • c • v = c • u • w • v
  rw [smul_comm w c, smul_comm u c]
variable {M : Module.Dual ℝ (Labels.Taylor G i)}

lemma angle (x : E4) (a : Axis) (c : G.ColorIndex) (i : ℕ) (z : ℂ) (n : ℕ) :
    shiftR s G n (factor G i (reading G i x a c) z n) =
      factor G i ((reading G i x a c).comp (Labels.Taylor.turn S)) z n := by
  let Bη := Labels.Taylor G i
  have ht :
    (reading G i x a c).comp (Labels.Taylor.turn S) =
      ∑ j : Axis, (S).val a j • reading G i (Ortho.move S⁻¹ x) j c := by
    ext v
    change Labels.Taylor.value (Labels.Taylor.turn _ v) a x c = _
    rw [Labels.Taylor.turn_value, LinearMap.sum_apply (M := Bη) (σ₁₂ := RingHom.id ℝ)]
    simp [reading]
  rw [corresponding, ht, map_sum]
  have hP := carries_node s (n := n) (G := G) x a z i
  rw [show shiftR s G n (node z a i x c) = _ from congr_fun hP c]
  simp only [Finset.sum_apply, Pi.smul_apply, map_smul, corresponding]
  rfl

lemma factors (f : Module.Dual ℝ (Labels.Taylor G i)) :
    (fun z => rotateMob s G (factor G i f z)) = factor G i (f.comp (Labels.Taylor.turn S)) := by
  let U := Labels.Taylor.turn (G := G) (j := i) S
  refine
    Submodule.span_induction (p := fun f _ =>
      (fun z => rotateMob s G (factor G i f z)) = factor G i (f.comp U)) ?_ ?_ ?_ ?_
      (enough G i ▸ Submodule.mem_top)
  · rintro f ⟨x, a, c, rfl⟩
    exact funext fun z => funext fun n => angle s x a c i z n
  · ext
    simp
  · intro x y _ _ hp hh
    funext z
    rw [map_add, Pi.add_apply, map_add, congr_fun hp z, congr_fun hh z, LinearMap.add_comp, map_add]
    rfl
  intro x y h hx
  funext z
  rw [show (x • y).comp U = x • (y.comp U) from rfl, map_smul, map_smul, Pi.smul_apply,
    LinearMapRealm, congr_fun hx]
  rfl
end pulse
section color

lemma apple_sum {J : Type} {F : J → Mield G n} (P : Finset J) (hp : ∀ i ∈ P, Apple (F i)) :
    Apple (∑ i ∈ P, F i) := by
  classical
    induction P using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    intro i j
    simp
  | insert b s hi ih =>
    rw [Finset.sum_insert hi]
    exact Apple.add (hp b (by simp)) (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))

lemma standard (z : ℂ) (a : Axis) (i : ℕ) (x : E4) : Apple (node (G := G) (n := n) z a i x) := by
  unfold node
  apply Apple.smul (c := (volume i : ℂ))
  apply apple_sum
  intro j _
  rw [ray_sum]
  apply Apple.smul (c := (x j : ℂ))
  exact
    apple_sum _ fun k _ =>
      Apple.smul (Pole.ingot j a (List.ofFn k) |>.1) (c := (((∏ j, x (k j)) : ℝ) : ℂ))

lemma blend (u : G.El) (x : E4) (a : Axis) (c : G.ColorIndex) (i : ℕ) (z : ℂ) (n : ℕ) :
    repeatC u (factor G i (reading G i x a c) z n) =
      factor G i ((reading G i x a c).comp (Labels.Taylor.paint u)) z n := by
  have ht :
    (reading G i x a c).comp (Labels.Taylor.paint u) =
      ∑ j : G.ColorIndex, weight u j c • reading G i x a j := by
    ext v
    rw [LinearMap.sum_apply (M := Labels.Taylor G i) (σ₁₂ := RingHom.id ℝ)]
    change ((G.adjoint u (Labels.Taylor.value v a x)) c) = _
    let d := Labels.Taylor.value v a x
    have he : ∑ c : G.ColorIndex, d c • eb G c = d := color_sum d
    change ((G.adjoint u d) c) = _
    nth_rw 1 [← he]
    simp
    apply Finset.sum_congr rfl
    intro j _
    exact Eq.trans ((by simp [weight]) : d j * _ = d j * weight u j c) (mul_comm ..)
  rw [corresponding, (standard _ a i x) u, ht, map_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, map_smul, corresponding]
  rfl

lemma stamps (f : Module.Dual ℝ (Labels.Taylor G i)) (u : G.El) (z : ℂ) (n : ℕ) :
    repeatC u (factor G i f z n) = factor G i (f.comp (Labels.Taylor.paint u)) z n := by
  let U := Labels.Taylor.paint (G := G) (j := i) u
  refine
    Submodule.span_induction (p := fun f _ =>
      repeatC u (factor G i f z n) = factor G i (f.comp U) z n) ?_ ?_ ?_ ?_
      (enough G i ▸ Submodule.mem_top)
  · rintro f ⟨x, a, c, rfl⟩
    exact blend u x a c i z n
  · simp
  · intro x y _ _ hp hh
    rw [map_add, Pi.add_apply, Pi.add_apply, map_add, hp, hh, LinearMap.add_comp, map_add]
    rfl
  intro x y h hx
  rw [show (x • y).comp U = x • (y.comp U) from rfl, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply,
    LinearMapRealm, hx]
  rfl
end color
end YM.WilsonMS.JRad
