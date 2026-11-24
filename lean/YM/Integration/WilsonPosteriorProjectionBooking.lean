import YM.Integration.WilsonPosteriorProjectionFlat

/-! Period-free order and sample choices for the actual thermal collar.
The coupling is the reciprocal square root of the genuine fine beta. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionBooking
open Finset Set Lattice Wilson RG Precision Tree Exterior Push.Uniform LocalLTE.Weft
open WilsonPosteriorProjectionPolarization WilsonPosteriorProjectionWire WilsonPosteriorProjectionWireRoom
open scoped BigOperators Classical
variable {G : Gauge} {c : Side}

def capacity (E d r h : ℕ) := E+d+h+5*r+1
def rank (E d r h : ℕ) : J (capacity E d r h) := ⟨r,by dsimp [capacity]; omega⟩

theorem orders (E d r h : ℕ) :
    E ≤ 2*capacity E d r h ∧
    2*(2*capacity E d r h+1)+2*d+h+4*r ≤ 4*(2*capacity E d r h+1) := by
  unfold capacity
  omega

def demand (r : ℕ) := ∑ u ∈ (rule r).support, slots u

theorem demand_nonneg (r : ℕ) : 0 ≤ demand r :=
  sum_nonneg fun u _ => sum_nonneg fun j _ => abs_nonneg (u j)

theorem sampled {r : ℕ} (v : Fin r → Letter G c) (g R : ℝ) (D M : ℕ) (hg : 0<g)
    (g1 : g≤1) (hD : 1≤D) (room : demand r ≤ R/g) (u : Fin r → ℝ) (hu : u∈(rule r).support)
    (i : J M) : ‖g • ((g^4*probe M i) • studio v u)‖ ≤ D*R := by
  have paid := (le_div_iff₀ hg).mp room
  have R0 : 0 ≤ R := (mul_nonneg (demand_nonneg r) hg.le).trans paid
  have cell : |g^4*probe M i| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (pow_nonneg hg.le _) (probes M i).1.le)]
    exact (mul_le_of_le_one_right (pow_nonneg hg.le _) (probes M i).2).trans (pow_le_one₀ hg.le g1)
  have used : slots u ≤ demand r := single_le_sum
    (f:=fun u : Fin r → ℝ => slots u) (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) hu
  have su : 0 ≤ slots u := sum_nonneg fun j _ => abs_nonneg _
  calc
    _ ≤ |g| * |g^4*probe M i| * slots u := WilsonPosteriorProjectionWireRoom.room v u g _
    _ ≤ g*slots u := by
      rw [abs_of_pos hg]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hg.le cell) su
    _ ≤ demand r*g := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right used hg.le
    _ ≤ R := paid
    _ ≤ _ := le_mul_of_one_le_left R0 (by exact_mod_cast hD)

theorem cooling (y β L : ℝ) (y1 : 2≤y) (lower : y/2≤β) :
    let g := (Real.sqrt β)⁻¹
    0<g ∧ g≤1 ∧ y*g^2≤4 ∧ |β*L| * g^2 ≤ |L| := by
  intro g
  have y0 : 0≤y := by linarith
  have β1 : 1≤β := by linarith
  have β0 : 0<β := zero_lt_one.trans_le β1
  have gt : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr β0)
  have id : β*g^2=1 := by
    unfold g
    rw [inv_pow,Real.sq_sqrt β0.le,mul_inv_cancel₀ β0.ne']
  refine ⟨gt,?_,?_,?_⟩
  · exact (inv_le_one₀ (Real.sqrt_pos.mpr β0)).mpr (by simpa using Real.sqrt_le_sqrt β1)
  · have he := mul_le_mul_of_nonneg_right (by linarith : y≤2*β) (sq_nonneg g)
    nlinarith only [id,he]
  · rw [abs_mul,abs_of_pos β0]
    calc
      _ = (β*g^2)*|L| := by ring
      _ ≤ _ := by rw [id,one_mul]

theorem point_order (g η : ℝ) (p h r : ℕ) (hg : 0<g) (g1 : g≤1)
    (loss : η≤1) (book : h+4*r≤p) :
    g^((p:ℝ)+1-η) ≤ g^(h+4*r) := by
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_ge hg g1
  have order : ((h+4*r:ℕ):ℝ)≤p := by exact_mod_cast book
  linarith

end YM.Integration.WilsonPosteriorProjectionBooking

