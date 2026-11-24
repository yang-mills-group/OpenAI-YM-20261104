import YM.Integration.WilsonMaxwellThermometerSeven
import YM.Integration.WilsonMaxwellThermometerChiralReading

/-! Linearity in both tested lower sections, and exact odd-word cancellation,
on the original separated continuum diagnostic. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerHeard
open Set Function MeasureTheory Maxwell Maxwell.Free XSpace XSpace.Rose XSpace.Normalize
open WilsonMaxwellThermometerProfile WilsonMaxwellThermometerSeven WilsonMaxwellThermometerChiralReading
open scoped BigOperators
variable {G : Gauge} {V : Normalize.Store G}

theorem of_profile (K : Pick V) (u p q : WickPol G)
    (h : ∀ x∈conf 3, linked x p q u=0) : read K p q u=0 := by
  change (Rose.test K).applyTo (fun x => linked x p q u)=0
  unfold Test.applyTo
  apply integral_eq_zero_of_ae; filter_upwards with x
  change (Rose.test K) x * linked x p q u=0
  by_cases hx : x ∈ tsupport (Rose.test K)
  · rw [h x ((Rose.test K).tsupport_subset hx),mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]

private theorem smooth (p q u : WickPol G) : ContinuousOn (fun x : Points 3 => linked x p q u)
    (conf 3) := by
  intro x hx
  have hu (u p q : WickPol G) : ContinuousAt (fun y : Points 3 => upper y p q u) x := by
    unfold upper; simp only [MultilinearMap.toLinearMap_apply]
    exact (Wick.moment_smooth _ hx).continuousAt
  change ContinuousWithinAt (fun y : Points 3 => upper y p q u - upper y 1 q 1 * upper y p 1 u -
    upper y p 1 1 * upper y 1 q u - upper y p q 1 * upper y 1 1 u +
    (2 * upper y p 1 1 * upper y 1 q 1) * upper y 1 1 u) _ _
  fun_prop (disch := apply ContinuousAt.continuousWithinAt; apply hu)

theorem add_left (K : Pick V) (u p p' q : WickPol G) :
    read K (p+p') q u = read K p q u + read K p' q u := by
  change (Rose.test K).applyTo _ = (Rose.test K).applyTo _ + (Rose.test K).applyTo _
  unfold Test.applyTo; simp_rw [left_add, mul_add]
  exact integral_add ((Rose.test K).smearing (smooth p q u)) ((Rose.test K).smearing (smooth p' q u))

theorem add_right (K : Pick V) (u p q q' : WickPol G) :
    read K p (q+q') u = read K p q u + read K p q' u := by
  change (Rose.test K).applyTo _ = (Rose.test K).applyTo _ + (Rose.test K).applyTo _
  unfold Test.applyTo; simp_rw [right_add, mul_add]
  exact integral_add ((Rose.test K).smearing (smooth p q u)) ((Rose.test K).smearing (smooth p q' u))

theorem smul_left (K : Pick V) (u p q : WickPol G) (c : ℂ) :
    read K (c•p) q u = c * read K p q u := by
  change (Rose.test K).applyTo _ = c*(Rose.test K).applyTo _
  unfold Test.applyTo; simp_rw [left_smul, mul_left_comm _ c]; exact integral_const_mul ..

theorem smul_right (K : Pick V) (u p q : WickPol G) (c : ℂ) :
    read K p (c•q) u = c * read K p q u := by
  change (Rose.test K).applyTo _ = c*(Rose.test K).applyTo _
  unfold Test.applyTo; simp_rw [right_smul, mul_left_comm _ c]; exact integral_const_mul ..

private theorem mirror_upper {x : Points 3} (hx : x∈conf 3) (u p q : WickPol G) :
    upper x (Taylor.mirror _ p) (Taylor.mirror _ q)
      (Taylor.mirror _ u) = upper x p q u := by
  rw [upper_triangle,upper_triangle,tri_eval,tri_eval]
  have hh : tripod (x 0) (x 1) (x 2)=x := by ext1 i; fin_cases i <;> rfl
  rw [hh]
  convert Normalize.free_symmetry (triCols u p q) hx using 2
  funext i; fin_cases i <;> rfl

theorem odd (K : Pick V) (c d : Bool) (u : WickPol G) (hu : Pure 3 u) :
    read K (polar G c) (polar G d) u=0 := by
  have he (s : Bool) : Taylor.mirror _ (polar G s)=polar G s := by
    simp [polar,team,bit,Taylor.mirror_sym]
  have ho : Taylor.mirror _ u = -u := by simpa only [show ((-1:ℂ)^3)= -1 by norm_num, neg_one_smul] using Taylor.parity_sign u hu
  apply of_profile
  intro x hx
  have h (p q : WickPol G) (hp : Taylor.mirror _ p=p)
      (hq : Taylor.mirror _ q=q) : upper x p q u = 0 := by
    have H:=mirror_upper hx u p q; rw [hp,hq,ho,map_neg] at H
    linear_combination -H/2
  have h1 : Taylor.mirror (Slot G) 1 = 1 := map_one _
  simp [linked, h _ _ (he c) (he d), h _ _ (he c) h1, h _ _ h1 (he d), h _ _ h1 h1]

end YM.Integration.WilsonMaxwellThermometerHeard
