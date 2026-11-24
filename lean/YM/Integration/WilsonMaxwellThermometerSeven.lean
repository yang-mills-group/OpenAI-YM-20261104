import YM.Integration.WilsonMaxwellThermometerProfile
import YM.Next.MAXWELL.Triangle

/-! The exact polarized connected reading annihilates a unit at any position.
For square words the three one-point faces of the normal-ordered free law vanish. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSeven
open Set Function MeasureTheory Maxwell Maxwell.Free Maxwell.Wick XSpace XSpace.Rose
open WilsonMaxwellThermometerFaces WilsonMaxwellThermometerProfile
open scoped BigOperators
variable {G : Gauge}

theorem upper_triangle (x : Points 3) (u p q : WickPol G) :
    upper x p q u = triangle G (x 0) (x 1) (x 2) u p q := by
  rw [upper, MultilinearMap.toLinearMap_apply, tri_eval]
  have hh : tripod (x 0) (x 1) (x 2) = x := by ext1 i; fin_cases i <;> rfl
  rw [hh]; apply congrArg (moment G x); funext i; fin_cases i <;> simp [XSpace.Graph3.trip,triCols]; rfl

private theorem blank (x : Points 3) : upper x 1 1 (1:WickPol G) = 1 := by
  rw [upper_triangle, tri_eval]
  rw [show triCols (1:WickPol G) 1 1 = (fun _ => 1) by funext i; fin_cases i <;> rfl]
  exact constants _

theorem left_add (x : Points 3) (u p p' q : WickPol G) :
    linked x (p+p') q u = linked x p q u + linked x p' q u := by
  simp [linked, upper_triangle, LinearMap.add_apply, smul_eq_mul]; ring

theorem left_smul (x : Points 3) (u p q : WickPol G) (c : ℂ) :
    linked x (c•p) q u = c * linked x p q u := by
  simp [linked, upper_triangle, LinearMap.smul_apply, smul_eq_mul]; ring

theorem right_add (x : Points 3) (u p q q' : WickPol G) :
    linked x p (q+q') u = linked x p q u + linked x p q' u := by
  simp [linked, upper_triangle, smul_eq_mul]; ring

theorem right_smul (x : Points 3) (u p q : WickPol G) (c : ℂ) :
    linked x p (c•q) u = c * linked x p q u := by
  simp [linked, upper_triangle, smul_eq_mul]; ring

theorem units (x : Points 3) (u p : WickPol G) :
    linked x 1 p u = 0 ∧ linked x p 1 u = 0 ∧ linked x u p 1 = 0 := by
  refine ⟨?_,?_,?_⟩ <;> simp [linked, blank, smul_eq_mul] <;> ring

private theorem one_contraction {n : ℕ} (x : Points n) (h : x∈conf n)
    (f g : Factor G) (i : Fin n) :
    moment G x (update (fun _ => 1) i (letter f * letter g)) = 0 := by
  let P := update (fun _ : Fin n => (1: WickPol G)) i (letter g)
  rw [show update (fun _ => 1) i (letter f * letter g) = update P i (letter f * P i) by
    unfold P; rw [update_self,update_idem]]
  change moment G x (update P i (symbol f.1 f.2 * P i))=0
  rw [moment_one f.2 P i h]; apply Finset.sum_eq_zero; intro j hj
  have hv : P j=1 := update_of_ne (Finset.mem_erase.mp hj).1 ..
  rw [hv,Derivation.map_one_eq_zero]
  exact MultilinearMap.map_coord_zero _ (i:=j) (update_self ..)

private theorem upper_square (x : Points 3) (h : x∈conf 3) (a b : Factor G) :
    upper x 1 1 (letter a*letter b) = 0 ∧ upper x (letter a*letter b) 1 1 = 0 ∧
      upper x 1 (letter a*letter b) 1 = 0 := by
  simp only [upper_triangle, tri_eval]
  have hx : tripod (x 0) (x 1) (x 2)=x := by ext1 i; fin_cases i <;> rfl
  rw [hx]
  constructor
  · convert one_contraction x h a b 0 using 2; funext i; fin_cases i <;> simp [triCols]; rfl
  constructor
  · convert one_contraction x h a b 1 using 2; funext i; fin_cases i <;> simp [triCols]; rfl
  · convert one_contraction x h a b 2 using 2; funext i; fin_cases i <;> simp [triCols]; rfl

theorem quadratic {j l : ℕ} (x : Points 3) (h : x∈conf 3) (p : Flavor j) (q : Flavor l) :
    upper x 1 1 (team G p q) = 0 ∧ upper x (team G p q) 1 1 = 0 ∧
      upper x 1 (team G p q) 1 = 0 := by
  let F {d : ℕ} (f : Flavor d) (i : G.ColorIndex) : Factor G := ⟨d,flavor d i f⟩
  have H (i : G.ColorIndex) := upper_square x h (F p i) (F q i)
  unfold team
  simp only [upper_triangle, map_sum, LinearMap.sum_apply] at H ⊢
  exact ⟨Finset.sum_eq_zero fun i _ => (H i).1, Finset.sum_eq_zero fun i _ => (H i).2.1,
    Finset.sum_eq_zero fun i _ => (H i).2.2⟩

end YM.Integration.WilsonMaxwellThermometerSeven
