import YM.Integration.WilsonPositionProgramTrialTorusInterior

/-! Concentric cutoffs in the genuine lifted max-distance of the finite torus.
Each interior difference costs one inverse annular width in the energy norm. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialTorusBoxes
open Finset Lattice Pert.Orb
open WilsonPositionProgramTrialTorusInterior (stock)
open scoped BigOperators Classical
variable {n : Side}

def ball (a : Site n) (r : ℝ) : Finset (Site n) :=
  univ.filter (fun x => (separation x a : ℝ) ≤ r)

theorem near (a x : Site n) (i : Axis) :
    |(separation (x+step i) a : ℝ)-(separation x a : ℝ)| ≤ 1 := by
  have edge : separation (x+step i) x ≤ 1 := by
    simpa only [separation,add_sub_cancel_left] using (pdist_step i (n:=n))
  have other : separation x (x+step i) ≤ 1 := (separation_comm ..) ▸ edge
  have p := separation_triangle (x+step i) x a
  have q := separation_triangle x (x+step i) a
  have p' : (separation (x+step i) a : ℝ) ≤ (separation x a : ℝ)+1 := by
    exact_mod_cast (by omega : separation (x+step i) a ≤ separation x a + 1)
  have q' : (separation x a : ℝ) ≤ (separation (x+step i) a : ℝ)+1 := by
    exact_mod_cast (by omega : separation x a ≤ separation (x+step i) a + 1)
  rw [abs_le]
  constructor <;> linarith

def clip (t : ℝ) : ℝ := min 1 (max 0 t)

private theorem pace (s t : ℝ) : |clip s-clip t| ≤ |s-t| := by
  unfold clip
  simp only [min_def,max_def]
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [le_abs_self (s-t),neg_abs_le (s-t)]

def coat (a : Site n) (r w : ℝ) (x : Site n) : ℝ :=
  clip ((r+1+w-(separation x a : ℝ))/w)

private theorem inside (a x : Site n) (r : ℝ) {w : ℝ} (wp : 0<w)
    (h : (separation x a : ℝ) ≤ r+1) : coat a r w x = 1 := by
  have q : 1 ≤ (r+1+w-(separation x a : ℝ))/w := (le_div_iff₀ wp).mpr (by linarith)
  unfold coat clip
  exact min_eq_left (q.trans (le_max_right ..))

private theorem outside (a x : Site n) (r : ℝ) {w : ℝ} (wp : 0<w)
    (h : r+1+w ≤ (separation x a : ℝ)) : coat a r w x = 0 := by
  have q : (r+1+w-(separation x a : ℝ))/w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) wp.le
  simp [coat,clip,max_eq_left q]

theorem original (u : Site n → ℝ) (a : Site n) (r : ℝ) {w : ℝ} (wp : 0<w)
    (locality : ∀ x, x ∈ ball a (r+w+2) → lap u x = 0) (i : Axis) :
    stock (ball a r) (ahead i u) ≤ 4*(1/w)^2*stock (ball a (r+w+2)) u := by
  apply WilsonPositionProgramTrialTorusInterior.original (coat a r w) u
  · intro x live
    apply locality x
    simp only [ball,mem_filter,mem_univ,true_and]
    by_contra! far
    exact live (outside a x r wp (by linarith))
  · intro j x
    apply (pace _ _).trans
    change |(r+1+w-(separation (x+step j) a : ℝ))/w-(r+1+w-(separation x a : ℝ))/w| ≤ 1/w
    rw [←sub_div, show r+1+w-(separation (x+step j) a : ℝ)-(r+1+w-(separation x a : ℝ)) =
      -((separation (x+step j) a : ℝ)-(separation x a : ℝ)) by ring, abs_div,abs_neg,abs_of_pos wp]
    exact (div_le_div_iff_of_pos_right wp).mpr (near a x j)
  · intro j x live
    have touched : (separation x a : ℝ) < r+1+w ∨ (separation (x+step j) a : ℝ) < r+1+w := by
      by_contra! far
      exact live (sub_eq_zero.mpr ((outside a _ r wp far.2).trans (outside a x r wp far.1).symm))
    have h := abs_le.mp (near a x j)
    simp only [ball,mem_filter,mem_univ,true_and]
    rcases touched with h'|h' <;> constructor <;> linarith
  · intro j x hx
    have h := (mem_filter.mp hx).2
    have stepFee := (abs_le.mp (near a x j)).2
    exact ⟨inside a x r wp (by linarith),inside a _ r wp (by linarith)⟩

end YM.Integration.WilsonPositionProgramTrialTorusBoxes
