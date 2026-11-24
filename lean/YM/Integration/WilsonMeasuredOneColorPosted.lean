import YM.Integration.WilsonMeasuredOneColorRadius
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredOneColorPosted
open Lattice RG Wilson Filter QuadraticLocal.Advent PhysicalNext PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped BigOperators Topology
variable {G:Gauge} (R:Run G)
def first (simple:G.Simple) := (eventually_atTop.mp (WilsonMeasuredOneColorRadius.original R simple)).choose
theorem both (simple:G.Simple) {j N per:ℕ} (cut:j+1≤N) (late:first R simple≤j+1)
    {a n o h C:ℝ} (ap:0<a) (np:0<n) (op:0<o) (hp:0<h)
    (upper:a⁻¹≤2*R.alloy.B.a.clock.hatBeta ((j+1)+1)*n)
    (price:o^6≤R.alloy.B.a.clock.hatBeta ((j+1)+1)) (C2:C≤2)
    (step:h ≤ max 1 (max (budgetR R j*budgetR R (j+1)) C)) :
    let t:=(regulatorRun R.family N per (j+1))^12/n
    0<t ∧ t≤a/(o^6*h) ∧ t≤a :=by
  have β : 0 < (R.family.path.rep N per (j+1)).beta :=
    (half_pos (zero_lt_one.trans (R.alloy.B.a.fits.delayed _))).trans_le
      (R.makes.wilson.represents N per (j+1) cut).band.1
  refine ⟨div_pos (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr β)) _) np,?_,?_⟩
  · exact (eventually_atTop.mp (WilsonMeasuredOneColorRadius.original R simple)).choose_spec
      (j+1) late N per cut rfl ap np op hp upper price C2 step
  · have lo:1≤R.family.path.levels.clock.hatBeta ((j+1)+1):=(R.family.path.levels.fits.delayed _).le
    simpa only [one_pow,mul_one,div_one] using
      (eventually_atTop.mp (WilsonMeasuredOneColorRadius.original R simple)).choose_spec
        (j+1) late N per cut rfl (C:=0) ap np (show 0<(1:ℝ) from zero_lt_one)
        zero_lt_one upper (by simpa only [one_pow] using lo) (by norm_num) (le_max_left ..)
theorem weights (simple:G.Simple) {j N per:ℕ} (cut:j+1≤N) (late:first R simple≤j+1)
    {a f n o h C:ℝ} (ap:0<a) (fp:0<f) (np:0<n) (hp:0<h) (wallet:f=a/(o^6*h))
    (upper:a⁻¹≤2*R.alloy.B.a.clock.hatBeta ((j+1)+1)*n)
    (price:o^6≤R.alloy.B.a.clock.hatBeta ((j+1)+1)) (C2:C≤2)
    (step:h ≤ max 1 (max (budgetR R j*budgetR R (j+1)) C)) :
    let t:=(regulatorRun R.family N per (j+1))^12/n
    0<t ∧ t≤f ∧ t≤a :=by
  have nz:o≠0:=by
    intro eq
    rw [eq,zero_pow (by decide:6≠0),zero_mul,div_zero] at wallet
    exact fp.ne' wallet
  have sixth:|o|^6=o^6:=by
    rw [←abs_pow,abs_of_nonneg (Even.pow_nonneg (by decide : Even 6) o)]
  obtain ⟨pos,low,top⟩:=both R simple cut late ap np (abs_pos.mpr nz) hp upper
    (sixth.trans_le price) C2 step
  exact ⟨pos,by simpa only [sixth,←wallet] using low,top⟩

end YM.Integration.WilsonMeasuredOneColorPosted
end
