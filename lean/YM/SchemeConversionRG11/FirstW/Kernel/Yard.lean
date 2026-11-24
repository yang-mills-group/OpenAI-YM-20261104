import YM.Pert.Align.Schedule
import YM.Lattice.Support
/-! Physical vs native rulers, ties included. For FirstW (nonzero spatial separations). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter Pert Lattice Topology
open scoped BigOperators
variable {n : Side} {k : ℕ}
def yard (x : Cover) : ℕ := Finset.univ.sup fun i => (x i).natAbs
def stepY (x : Cover) : ℝ := 1 + yard x
def cy (x : Site n) : ℝ := stepY (Lattice.lift x)
lemma cy_eq (x : Site n) : cy x = 1 + (pdist x : ℝ) := rfl
lemma unit_stepY (x : Cover) : 1 ≤ stepY x := by unfold stepY; simp
lemma unit_cy (x : Site n) : 1 ≤ cy x := unit_stepY _
@[simp] lemma stepY_neg (x : Cover) : stepY (-x) = stepY x := by simp [stepY,yard]
@[simp] lemma cy_neg (x : Site n) : cy (-x)=cy x := by simp only [cy_eq,pdist_neg]
@[simp] lemma cy_zero : cy (0 : Site n)=1 := by simp [cy_eq,pdist,lift]
lemma yard_upper (x : Cover) (i : Axis) : (x i).natAbs ≤ yard x := Finset.le_sup (s:=Finset.univ) (f:=fun i=>(x i).natAbs) (Finset.mem_univ _)
lemma yard_picked (x : Cover) : ∃ i : Axis, yard x = (x i).natAbs := by
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image (β:=Axis) Finset.univ (fun i=>(x i).natAbs) Finset.univ_nonempty
  exact ⟨i,le_antisymm (Finset.sup_le hi) (yard_upper _ _)⟩
lemma yard_add (x y : Cover) : yard (x+y) ≤ yard x + yard y := Finset.sup_le (fun i _ => le_trans (Int.natAbs_add_le ..) (Nat.add_le_add (yard_upper x i) (yard_upper y i)))
lemma sum_stepY (x y : Cover) : stepY (x+y) ≤ stepY x + stepY y := by
  have h : ((yard (x+y):ℕ):ℝ) ≤ (yard x:ℝ)+(yard y:ℝ) := by exact_mod_cast yard_add x y
  unfold stepY; linarith
lemma sum_cy (x y : Site n) : cy (x+y) ≤ cy x + cy y := by
  have h : ((pdist (x+y):ℕ):ℝ) ≤ (pdist x:ℝ)+(pdist y:ℝ) := by exact_mod_cast pdist_triangle x y
  simp only [cy_eq]; linarith
lemma reverse_cy (x y : Site n) : cy x ≤ cy y + cy (x-y) := by simpa using sum_cy y (x-y)
lemma done_cy (x : Site n) : cy x ≤ 2*n.val := by
  have h : pdist x ≤ n.val := by
    refine Finset.sup_le (fun i _ => ?_)
    have ht := lift_centers x i; omega
  have hh : (pdist x:ℝ) ≤ n.val := by exact_mod_cast h
  have hn : 1≤(n.val:ℝ) := by exact_mod_cast n.pos
  rw [cy_eq]; linarith
lemma yard_box_iff {x : Cover} : yard x≤k ↔ ∀ i : Axis, (x i).natAbs≤k := ⟨fun h i=>(yard_upper _ i).trans h,fun h=>Finset.sup_le (fun i _=>h i)⟩
def boxN (k : ℕ) : Finset Cover := Finset.Icc (fun _=>-(k:ℤ)) (fun _=>k)
lemma mem_boxN {x : Cover} : x∈boxN k ↔ yard x ≤ k := by
  rw [boxN,Finset.mem_Icc,yard_box_iff]; constructor
  · intro h i
    have hl : -(k:ℤ) ≤ x i := h.1 i
    have hh : x i ≤ (k:ℤ) := h.2 i
    omega
  intro h; exact ⟨fun i=>show -(k:ℤ) ≤ x i from by specialize h i; omega,fun i=>show x i ≤ (k:ℤ) from by specialize h i; omega⟩
lemma yard_toE (x : Cover) : (yard x:ℝ) ≤ ‖Full.incVec 1 x‖ := by
  obtain ⟨i,e⟩ := yard_picked x; have h := Band.coordinate_le (Full.incVec 1 x) i
  simpa only [e, Full.incVec_apply,one_mul, ←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast] using h
lemma yard_fromE (x : Cover) : ‖Full.incVec 1 x‖ ≤ 2 * (yard x:ℝ) := by
  obtain ⟨i,h⟩ := Band.max_coord (Full.incVec 1 x)
  have hh : ((x i).natAbs:ℝ) ≤ (yard x:ℝ) := by exact_mod_cast yard_upper x i
  rw [Full.incVec_apply,one_mul,←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast] at h
  exact h.trans (by linarith)
lemma mover (s : ℝ) (x : Cover) : Full.incVec s x = s • Full.incVec 1 x := by ext; simp
lemma mover_norm {s : ℝ} (x : Cover) (hs : 0≤s) : ‖Full.incVec s x‖ = s * ‖Full.incVec 1 x‖ := by nth_rw 1 [mover s]; rw [norm_smul,Real.norm_of_nonneg hs]
lemma low_at (x : Site n) {s : ℝ} (hs : 0≤s) : s * (cy x-1) ≤ ‖Full.incVec s (lift x)‖ := by rw [cy,stepY,mover_norm _ hs]; gcongr; simpa using yard_toE (lift x)
lemma high_at (x : Site n) {s : ℝ} (hs : 0≤s) : ‖Full.incVec s (lift x)‖ ≤ 2 * (s * (cy x-1)) := by rw [cy,stepY,mover_norm _ hs]; simp only [add_sub_cancel_left]; exact (mul_le_mul_of_nonneg_left (yard_fromE _) hs).trans (le_of_eq (by ring))
lemma inc_add (v w : Cover) (s : ℝ) : Full.incVec s (v+w) = Full.incVec s v + Full.incVec s w := by ext; simp [Full.incVec_apply,mul_add]
lemma inc_step (i : Axis) (s : ℝ) : Full.incVec s (step i) = s • basis i := by ext j; simp [Full.incVec,basis]
open Align
lemma entire (T : Itinerary) (u : Cover) : ∀ᶠ i : ℕ in atTop,Lattice.lift (wrap (T.period i) u) = u := (simple_bounds T (u:=fun _=>u) (inc_const T u)).mono fun _ h => lift_eq_iff.mpr ⟨rfl,fun k=>by have hv:=h k; have :=neg_le_abs (u k); have :=le_abs_self (u k); omega⟩
lemma past (T : Itinerary) (u : Cover) : ∀ᶠ i : ℕ in atTop,∀ x:Site (T.period i),cy (x+wrap (T.period i) u) ≤ (1+stepY u)*cy x ∧ cy x≤ (1+stepY u)*cy (x+wrap (T.period i) u) := by
  filter_upwards [entire T u] with i hi x
  set v := wrap _ u
  have ev : cy v=stepY u := congrArg stepY hi
  have hp : 0≤stepY u := zero_le_one.trans (unit_stepY _)
  exact ⟨(sum_cy x v).trans (by rw [ev]; nlinarith only [unit_cy x,hp]),(reverse_cy x (x+v)).trans (by rw [show x-(x+v)= -v by abel,cy_neg,ev]; nlinarith only [unit_cy (x+v),hp])⟩
end YM.RG11.FirstW
