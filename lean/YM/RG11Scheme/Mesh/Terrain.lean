import YM.Pert.Align.Schedule

/-! Native-unit terrain; polynomial ranges in top lattice coordinates. All ℤ powers below use h>0. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Mesh
open Lattice Function Filter Set Pert
open scoped Topology BigOperators Classical
abbrev elev (x : Cover) : ℕ := Finset.univ.sup fun i=> (x i).natAbs
def wide (x : Cover) : ℝ := ↑(elev x) + 1
def row (x : Cover) := Full.incVec 1 x
@[simp] lemma row_axis (x : Cover) (i:Axis) : row x i=x i := one_mul _
@[simp] lemma row_zero : row 0=0 := PiLp.ext fun i=> by simp
@[simp] lemma row_add (x y : Cover) : row (x+y)=row x+row y := by ext i;rw [row_axis]; simp
@[simp] lemma row_neg (x : Cover) : row (-x)=-row x := by ext i; simp
@[simp] lemma row_sub (x y : Cover) : row (x-y)=row x-row y := by rw [sub_eq_add_neg, row_add,row_neg, sub_eq_add_neg]
lemma inc_row (x : Cover) (h) : Full.incVec h x=h • row x := PiLp.ext fun i=> by change h*_=h*row x i; rw [row_axis]
@[simp] lemma row_step (i:Axis) : row (step i)=basis i := by ext j; simp [basis_eq,eq_comm]
lemma cardinal_big (i : Axis) (x:Cover) : (x i).natAbs ≤ elev x := Finset.le_sup (s:=Finset.univ) (f:=fun i=> (x i).natAbs) (Finset.mem_univ i)
lemma big (i : Axis) (x:Cover) : |(x i:ℝ)| ≤ wide x := by
   have he : |x i| ≤ (elev x:ℤ) := by rw [←Int.natCast_natAbs]; exact_mod_cast (cardinal_big i x)
   unfold wide
   have hl : |(x i:ℝ)| ≤ ↑(elev x) := by exact_mod_cast he
   linarith
lemma wide_one (x:Cover) : 1≤wide x := by unfold wide; simp
lemma wide_pos (x:Cover) : 0<wide x := lt_of_lt_of_le zero_lt_one (wide_one _)
lemma elev_min (x:Cover) : (↑(elev x):ℝ) ≤ ‖row x‖ := by
   obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup _ (Finset.univ_nonempty (α:=Axis)) (fun i=> (x i).natAbs)
   have he := PiLp.norm_apply_le (row x) i
   rw [Real.norm_eq_abs,row_axis] at he
   change elev x=_ at hi
   rw [hi, ← Int.cast_natCast (R:=ℝ), Int.natCast_natAbs,Int.cast_abs]; exact he
lemma axis_elev (x:Cover) : ‖row x‖ ≤ 2*(↑(elev x):ℝ) := by
   have hx (i:Axis) : ‖row x i‖ ≤ (↑(elev x):ℝ) := by
      rw [Real.norm_eq_abs,row_axis]; exact_mod_cast (show |x i| ≤ (elev x:ℤ) from Int.natCast_natAbs _ ▸ by exact_mod_cast (cardinal_big i x))
   have hm : ‖row x‖^2≤∑ _ : Axis, (↑(elev x):ℝ)^2 := by rw [PiLp.norm_sq_eq_of_L2]; exact Finset.sum_le_sum (fun i _=> pow_le_pow_left₀ (norm_nonneg _) (hx i) _)
   have hh : ‖row x‖^2 ≤ 4*(↑(elev x):ℝ)^2 := by simpa only [Finset.sum_const,Finset.card_univ, show Fintype.card Axis=4 from rfl, nsmul_eq_mul, Nat.cast_ofNat] using hm
   nlinarith [Nat.cast_nonneg (α:=ℝ) (elev x), norm_nonneg (row x)] -- check def rank
lemma peak {n : Side} (x : Site n) : 2 * elev (lift x) ≤ n.val := by
   obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup _ (Finset.univ_nonempty (α:=Axis)) (fun i=> (lift x i).natAbs)
   change elev _=_ at hi; rw [hi]; have hh := lift_centers x i; omega
lemma peak_row {n : Side} (x : Site n) : ‖row (lift x)‖ ≤ (n.val:ℝ) := (axis_elev _).trans (by exact_mod_cast peak x)
@[simp] lemma elev_zero : elev 0=0 := by simp [elev]
@[simp] lemma elev_neg (x:Cover) : elev (-x)=elev x := by simp [elev]
@[simp] lemma wide_zero : wide 0=1 := by simp [wide]
@[simp] lemma wide_neg (x:Cover) : wide (-x)=wide x := by simp [wide]
lemma elev_triangle (x y:Cover) : elev (x+y)≤ elev x+elev y := Finset.sup_le (fun i _=> (Int.natAbs_add_le ..).trans (add_le_add (cardinal_big i x) (cardinal_big i y)))
lemma wide_plus (x y:Cover) : wide (x+y) ≤ wide x + wide y := by
   have he : (↑(elev (x+y)):ℝ) ≤ ↑(elev x) + ↑(elev y) := by exact_mod_cast elev_triangle x y
   unfold wide; linarith
lemma wide_triangle (x y:Cover) : wide x ≤ wide (x-y) + wide y := by convert (wide_plus (x-y) y) using 1; simp
lemma wide_budget (x y:Cover) : wide x ≤ wide (x-y) * (1+wide y) := (wide_triangle x y).trans (by nlinarith [wide_one (x-y),wide_one y])
lemma placement (i:Cover) (C : Align.Itinerary) : ∀ᶠ j in atTop,lift (wrap (C.period j) i)=i := by
   have he := Align.simple_bounds C (u:=fun _=>i) (Align.inc_const C i)
   exact he.mono (fun j hj=> lift_eq_iff.mpr ⟨rfl,fun k=>by have := hj k; have := le_abs_self (i k); have := neg_le_abs (i k); omega⟩)
end YM.RG11Scheme.Mesh
