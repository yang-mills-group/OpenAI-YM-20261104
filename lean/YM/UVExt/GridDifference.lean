import YM.UVExt.Interpolation
import YM.Extraction.Equicontinuity

/-!
# Finite families of normalized positional differences
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Grid
open Set Filter Function Extraction Lattice
open scoped BigOperators Topology Classical
variable {n : ℕ}

def jump (p : Index n) : Args n := Pi.single p.1 (Lattice.step p.2)
@[simp] lemma jump_eq (p : Index n) : jump p p.1 p.2 = 1 := by simp [jump]
lemma jump_other {p q : Index n} (h : q≠p) : jump p q.1 q.2 = 0 := by
  by_cases hi : q.1 = p.1
  · have h' : q.2 ≠ p.2 := fun hh=>h (Prod.ext hi hh)
    simp [jump,hi,h']
  simp [jump,hi]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def differences (t : ℝ) (f : Args n→E) (p : Index n) (x : Args n) : E := t⁻¹ • (f (x+jump p)-f x)
def mixed (t : ℝ) : List (Index n) → (Args n→E) → Args n→E
| [], f => f
| p::u, f => differences t (mixed t u f) p

-- Needed for differentiated source arrays in products at multiple placements
lemma differences_comm (t : ℝ) (p q : Index n) (f : Args n→E) : differences t (differences t f p) q = differences t (differences t f q) p := by
  funext x
  unfold differences
  rw [show x+jump q+jump p=x+jump p+jump q by rw [add_right_comm]]
  congr 1; rw [← smul_sub,← smul_sub]; congr 1; abel_nf

private def pathLength (x y : Args n) := ∑ i : Index n, (x i.1 i.2-y i.1 i.2).natAbs
lemma tag_square (u v : Args n) (t : ℝ) :
    dist (tag t u) (tag t v)^2 = ∑ i : Index n, (t*(u i.1 i.2-v i.1 i.2 : ℤ))^2 := by
  rw [dist_eq_norm,← Points.flatten.norm_map, EuclideanSpace.real_norm_sq_eq]; simp_rw [map_sub]
  exact Finset.sum_congr rfl fun i _ => by
    change (_ * (_:ℝ)-t*_)^2=_; rw [Int.cast_sub,mul_sub]
lemma component_le {t : ℝ} (ht : 0≤t) (x y : Args n) (i : Index n) :
    t*((x i.1 i.2-y i.1 i.2).natAbs:ℝ) ≤ dist (tag t x) (tag t y) := by
  apply (sq_le_sq₀ (by positivity) dist_nonneg).1
  rw [tag_square, ← Int.cast_natCast, Int.natCast_natAbs,Int.cast_abs,mul_pow,sq_abs,← mul_pow]
  exact Finset.single_le_sum (f:=(fun i:Index n=> ((t*(x i.1 i.2-y i.1 i.2 : ℤ))^2:ℝ))) (s:=Finset.univ) (fun _ _=>sq_nonneg _) (Finset.mem_univ i)
lemma step_cost (t : ℝ) (ht : 0<t) (f : Args n→E) (p : Index n) (u : Args n) {A} (hp : ‖differences t f p u‖ ≤ A) :
    dist (f (u+jump p)) (f u) ≤ t*A := by
  unfold differences at hp; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le)] at hp
  rw [dist_eq_norm]; exact (inv_mul_le_iff₀ ht).1 hp

private def Pocket (x y z : Args n) := ∀ p : Index n,
    (z p.1 p.2 - y p.1 p.2).natAbs ≤ (x p.1 p.2 - y p.1 p.2).natAbs
private lemma pick_neighbor (x y : Args n) (h : pathLength x y ≠ 0) : ∃ (x' : Args n) (p : Index n),
    (x'=x+jump p ∨ x=x'+jump p) ∧ pathLength x' y + 1 = pathLength x y ∧ Pocket x y x' := by
  have hx : ∃ p : Index n, x p.1 p.2 ≠ y p.1 p.2 := by
    by_contra! hf; apply h; simp [pathLength,hf]
  obtain ⟨p,hp⟩ := hx
  set x':Args n:=if x p.1 p.2 < y p.1 p.2 then x + jump p else x - jump p with H
  have hi : (x' p.1 p.2 - y p.1 p.2).natAbs + 1 = (x p.1 p.2 - y p.1 p.2).natAbs := by
    split_ifs at H <;> simp [H] <;> omega
  have ho (q : Index n) (hq : q ≠ p) : x' q.1 q.2 = x q.1 q.2 := by split_ifs at H <;> simp [H,jump_other hq]
  refine ⟨x',p,?_,?_,?_⟩
  · split at H <;> simp [H]
  · unfold pathLength; conv_rhs => rw [← Finset.sum_erase_add _ _ (Finset.mem_univ p)]
    conv_lhs => rw [← Finset.sum_erase_add _ _ (Finset.mem_univ p)]
    rw [add_assoc,hi]; apply congr_arg fun z:ℕ=> z + _
    exact Finset.sum_congr rfl fun i h=>by rw [ho i (Finset.ne_of_mem_erase h)]
  intro i; by_cases he:i=p
  · rw [he]; omega
  rw [ho i he]
private lemma pocket_dist {t : ℝ} (ht : 0≤t) {x y z : Args n} (hp : Pocket x y z) :
    dist (tag t z) (tag t y) ≤ dist (tag t x) (tag t y) := by
  apply (sq_le_sq₀ dist_nonneg dist_nonneg).mp
  rw [tag_square,tag_square]; exact Finset.sum_le_sum (fun i _ => by
    apply sq_le_sq.mpr
    simp only [abs_mul, abs_of_nonneg ht, ← Int.cast_abs]
    exact mul_le_mul_of_nonneg_left (by simp_rw [← Int.natCast_natAbs]; exact_mod_cast hp i) ht)
private lemma pocket_bound {t A : ℝ} (ht : 0<t) (x y : Args n) (f : Args n→E)
    (hp : ∀ z : Args n, Pocket x y z → ∀ p, ‖differences t f p z‖ ≤ A) :
    dist (f x) (f y) ≤ pathLength x y*(t*A) := by
  by_cases h : pathLength x y=0
  · have he : x=y := by
      funext i a; apply sub_eq_zero.mp (Int.natAbs_eq_zero.mp ?_)
      exact ((Finset.sum_eq_zero_iff_of_nonneg (fun _ _=>Nat.zero_le _)).mp h) (by exact (i,a) : Index n) (Finset.mem_univ (i,a))
    simp [he,pathLength]
  obtain ⟨z,p,hz,hD,H⟩ := pick_neighbor x y h
  have hy := pocket_bound ht z y f (fun v h=>hp v (fun i => (h i).trans (H i)))
  refine (dist_triangle _ (f z) _).trans (add_le_add (b:=t*A) ?_ hy |>.trans_eq ?_)
  · rcases hz with rfl|rfl
    · rw [dist_comm]; exact step_cost t ht _ _ _ (hp x (fun _=>le_refl _) p)
    exact step_cost t ht _ _ _ (hp _ H p)
  · rw [← hD,Nat.cast_add,Nat.cast_one]; ring
termination_by pathLength x y
decreasing_by omega

theorem close_lattice {t A s : ℝ} (ht : 0<t) (hA : 0≤A) (K : Set (Points n))
     (x y : Args n) (f : Args n→E) (hy : tag t y ∈ K) (hr : dist (tag t x) (tag t y)≤s)
     (hp : ∀ z, tag t z ∈ Metric.cthickening s K → ∀ p, ‖differences t f p z‖ ≤ A) :
    dist (f x) (f y) ≤ A*(4*n)*(dist (tag t x) (tag t y)) := by
  let D:= dist (tag t x) (tag t y)
  calc
    _ ≤ pathLength x y * (t*A) := pocket_bound ht _ _ _ (fun u h=>hp u
      (Metric.mem_cthickening_of_dist_le (tag t u) (tag t y) s K hy ((pocket_dist ht.le h).trans hr)))
    _ ≤ _ := by
      unfold pathLength; push_cast
      simp only [Finset.sum_mul]
      have h : ∑ _ : Index n, A*D = (4*n)*A*D := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]; ring
      calc
        _ ≤ ∑ i:Index n, A*D := Finset.sum_le_sum (fun i _=>by simpa [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_left (component_le ht.le x y i) hA)
        _ = _ := by rw [h,mul_comm A]
end YM.UVExt.Grid
