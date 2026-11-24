import YangMills.WilsonProof.NativeSupport.JointSkyScale

/-! Numerical admission of all primitive births and the full native hat
heap using one purchased reserve. The nonlinear debit is quadratic in
the old root bound and linear in the newly planted amplitude. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet

def oldRadius (k u h:ℝ) := (k*max u h)⁻¹
def bornRadius (k h:ℝ) := (k*h)⁻¹
def mountedFare (quiet old birth:ℝ) := 2*(old+birth)+2*(Real.exp (quiet+old+birth)-1)
def fullFare (a:ℝ) := a+Real.exp a*a

theorem radius_price {k u h:ℝ} (size:1 ≤ k) (pos:0 < h) (small:h ≤ 1)
    (room:k*max u h ≤ 1) :
    1 ≤ oldRadius k u h ∧ 1 ≤ bornRadius k h ∧ oldRadius k u h*u ≤ 1/k ∧
    bornRadius k h*h=1/k ∧ 2/min (bornRadius k h) (oldRadius k u h^2) ≤ 2*k^2*(u^2+h) := by
  have kp:0 < k := zero_lt_one.trans_le size
  let z:=max u h
  have zp:0 < z :=pos.trans_le (le_max_right ..)
  have kd:k*h ≤ 1 := (mul_le_mul_of_nonneg_left (le_max_right u h) kp.le).trans room
  change 1 ≤ (k*z)⁻¹ ∧ 1 ≤ (k*h)⁻¹ ∧ (k*z)⁻¹*u ≤ 1/k ∧ (k*h)⁻¹*h=1/k ∧ _
  refine ⟨(one_le_inv₀ (mul_pos kp zp)).mpr room,(one_le_inv₀ (mul_pos kp pos)).mpr kd,?_,?_,?_⟩
  · calc
      (k*z)⁻¹*u ≤ (k*z)⁻¹*z := mul_le_mul_of_nonneg_left (le_max_left ..) (inv_pos.mpr (mul_pos kp zp)).le
      _ = 1/k := by field_simp
  · field_simp
  · have zsq:z^2 ≤ u^2+h := by
      rcases le_total u h with uh|hu
      · rw [show z=h from max_eq_right uh]
        nlinarith only [sq_nonneg u,mul_nonneg pos.le (sub_nonneg.mpr small)]
      · rw [show z=u from max_eq_left hu];linarith only [pos]
    have a0 : 2/(oldRadius k u h)^2 ≤ 2*k^2*(u^2+h) := by
      change 2/((k*z)⁻¹)^2 ≤ _
      rw [inv_pow,div_inv_eq_mul,mul_pow,←mul_assoc]
      exact mul_le_mul_of_nonneg_left zsq (by positivity)
    have d0 : 2/bornRadius k h ≤ 2*k^2*(u^2+h) := by
      rw [bornRadius,div_inv_eq_mul]
      calc
        _ ≤ 2*(k^2*h) := by gcongr; nlinarith only [mul_nonneg kp.le (sub_nonneg.mpr size)]
        _ ≤ 2*k^2*(u^2+h) := by rw [←mul_assoc]; gcongr; nlinarith only [sq_nonneg u]
    rcases le_total (bornRadius k h) ((oldRadius k u h)^2) with le|le
    · simpa only [min_eq_left le] using d0
    · simpa only [min_eq_right le] using a0

theorem heap_cash {k μ s z box x quiet old birth:ℝ} (kp:0 < k) (mu:1 ≤ μ) (s0:0 ≤ s) (z0:0 ≤ z)
    (bx:1 ≤ box) (heat:1 ≤ x) (q0:0 ≤ quiet) (o0:0 ≤ old) (b0:0 ≤ birth)
    (fund:64*μ*box*x^2*(1+μ*s*(1+z)) ≤ k)
    (calibrated:quiet ≤ 1/k) (inherited:old ≤ μ*s/k) (fresh:birth ≤ μ*s*z/k) :
    box*(quiet+old+birth) ≤ 3 ∧ fullFare (mountedFare quiet old birth) ≤ (1/x^2)/μ := by
  let cost:=(1+μ*s*(1+z))/k
  let total:=quiet+old+birth
  let mounted:=mountedFare quiet old birth
  have mp:0 < μ:=zero_lt_one.trans_le mu
  have bp:0 < box:=zero_lt_one.trans_le bx
  have xp:0 < x:=zero_lt_one.trans_le heat
  have cost0:0 ≤ cost := by dsimp [cost];positivity
  have total0:0 ≤ total := by dsimp [total];positivity
  have billed:total ≤ cost := by
    calc
      total ≤ 1/k+μ*s/k+μ*s*z/k := add_le_add (add_le_add calibrated inherited) fresh
      _ = cost := by dsimp only [cost];ring
  have invoice : 64*μ*box*x^2*cost ≤ 1 := by
    rw [show 64*μ*box*x^2*cost=(64*μ*box*x^2*(1+μ*s*(1+z)))/k by dsimp only [cost];ring]
    exact (div_le_iff₀ kp).mpr (by simpa only [one_mul] using fund)
  have bulk:1 ≤ μ*box*x^2 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le mu bx) (one_le_pow₀ heat)
  have cap : 64*cost ≤ 1 := by
    apply le_trans _ invoice
    rw [show 64*μ*box*x^2*cost=(64*cost)*(μ*box*x^2) by ring]
    exact le_mul_of_one_le_right (by positivity) bulk
  have few:total ≤ 1 := by linarith only [billed,cap,cost0]
  have dv: Real.exp total-1 ≤ 2*total := by
    apply (le_abs_self _).trans
    simpa only [abs_of_nonneg total0] using (Real.abs_exp_sub_one_le (x:=total) (by rwa [abs_of_nonneg total0]))
  have money:0 ≤ mounted := by
    change 0 ≤ 2*(old+birth)+2*(Real.exp total-1)
    exact add_nonneg (by positivity) (mul_nonneg zero_le_two (sub_nonneg.mpr (Real.one_le_exp total0)))
  have light:mounted ≤ 6*cost := by
    change 2*(old+birth)+2*(Real.exp total-1) ≤ _
    have part:old+birth ≤ total := by dsimp [total];linarith only [q0]
    linarith only [dv,part,billed]
  have change_:Real.exp mounted ≤ 3 := (Real.exp_le_exp.mpr (by linarith only [light,cap,cost0])).trans Real.exp_one_lt_three.le
  have bill : fullFare mounted ≤ 64*cost := by
    unfold fullFare
    linarith only [mul_le_mul_of_nonneg_right change_ money,light,cost0]
  constructor
  · change box*total ≤ 3
    have another:1 ≤ 64*μ*x^2 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) mu) (one_le_pow₀ heat)
    calc
      _ ≤ box*cost := mul_le_mul_of_nonneg_left billed bp.le
      _ ≤ (box*cost)*(64*μ*x^2) := le_mul_of_one_le_right (mul_nonneg bp.le cost0) another
      _ = 64*μ*box*x^2*cost := by ring
      _ ≤ 3 := invoice.trans (by norm_num)
  · change fullFare mounted ≤ (1/x^2)/μ
    apply (le_div_iff₀ mp).mpr
    apply (le_div_iff₀ (sq_pos_of_pos xp)).mpr
    calc
      fullFare mounted*μ*x^2 ≤ 64*cost*μ*x^2 := by gcongr
      _ ≤ (64*cost*μ*x^2)*box := le_mul_of_one_le_right (by positivity) bx
      _ = 64*μ*box*x^2*cost := by ring
      _ ≤ _ := invoice

end YM.Integration.InletSusceptibility.Packet
