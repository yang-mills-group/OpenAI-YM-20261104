import YangMills.WilsonProof.NativeSupport.PacketMoment

/-! The finite word polynomial pays the moment generating function under the
original normalized, real, tagged path measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Finset MeasureTheory Lattice RG Wilson RGComparison.Core16
open WilsonUniformUnmarkedInletConnectedCovariance
open scoped Classical BigOperators
variable {G : Gauge} {n c : Side}

private theorem exp_factor {x : ℝ} (hx : |x| ≤ 1/4) :
    Real.exp x ≤ (1+x)*Real.exp (2*x^2) := by
  have pos : 0<1-x := by linarith [(abs_le.mp hx).2]
  have sq : x^2 ≤ (1/4 : ℝ)^2 := sq_le_sq.mpr (by simpa using hx)
  have prod := mul_nonneg (sq_nonneg x) (show 0 ≤ 1-2*x^2 by linarith)
  have cross := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [←Real.exp_add,neg_add_cancel,Real.exp_zero] at cross
  apply (mul_le_mul_iff_of_pos_right pos).mp
  calc
    Real.exp x*(1-x) ≤ 1 := by linarith [cross]
    _ ≤ (1-x^2)*(1+2*x^2) := by nlinarith
    _ ≤ (1-x^2)*Real.exp (2*x^2) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (2*x^2)]) (by linarith)
    _ = (1+x)*Real.exp (2*x^2)*(1-x) := by ring

private theorem compare (d : Descent n c) (ok : d.OK G) (β : ℕ→ℝ) (Z : Config G c)
    {f h : Config G n→ℝ} (cont : Continuous f) (other : Continuous h)
    (a : ℝ) (le : ∀ U,f U ≤ a*h U) : mass d β f Z ≤ a*mass d β h Z := by
  simp only [mass,mul_sum]
  refine sum_le_sum fun t _=>?_
  rw [←integral_const_mul]
  apply integral_mono (d.path_integrable ok β t f cont Z) ((d.path_integrable ok β t h other Z).const_mul _)
  intro x
  simp only [Descent.integrand]
  rw [mul_left_comm a]
  exact mul_le_mul_of_nonneg_left (le _) (mul_nonneg (d.probability_nonneg ..) (Real.exp_pos _).le)

private theorem product_mgf {H : Type*} [Fintype H] (W : H→ℝ) (unit : ∀ j,|W j| ≤ 1)
    {s : ℝ} (hs : |s| ≤ 1/4) :
    Real.exp (s*∑ j,W j) ≤ Real.exp ((Fintype.card H : ℝ)*(2*s^2))*∏ j,(1+s*W j) := by
  have bound j : |s*W j| ≤ |s| := by
    rw [abs_mul]; exact (mul_le_mul_of_nonneg_left (unit j) (abs_nonneg s)).trans_eq (mul_one _)
  rw [mul_sum,Real.exp_sum]
  calc
    ∏ j,Real.exp (s*W j) ≤ ∏ j,(Real.exp (2*s^2)*(1+s*W j)) := by
      refine prod_le_prod (fun _ _=>(Real.exp_pos _).le) fun j _=>?_
      rw [mul_comm (Real.exp _)]
      exact (exp_factor ((bound j).trans hs)).trans (mul_le_mul_of_nonneg_left
        (Real.exp_monotone (by linarith [sq_le_sq.mpr (bound j)]))
        (by linarith [(abs_le.mp ((bound j).trans hs)).1]))
    _ = _ := by rw [prod_mul_distrib]; simp [Real.exp_nat_mul]

theorem log_mgf {H : Type*} [Fintype H] (d : Descent n c) (ok : d.OK G)
    (β : ℕ→ℝ) (Z : Config G c) (W : H→ Config G n→ℝ) (cont : ∀ j,Continuous (W j))
    (unit : ∀ j U, |W j U| ≤ 1) {s w fee : ℝ} (hw : |w| ≤ 1) (hs : |s| ≤ 1/4)
    (price : mass d β (fun U=>∏ j,(1+s*W j U)) Z / mass d β 1 Z ≤
      Real.exp fee*(1+s*w)^Fintype.card H) :
    Real.log (mass d β (fun U=>Real.exp (s*∑ j,W j U)) Z) - Real.log (mass d β 1 Z)
      ≤ fee + (Fintype.card H : ℝ)*(2*s^2+s*w) := by
  let K : ℝ := Fintype.card H
  let f (U : Config G n) := ∑ j,W j U
  have hf : Continuous f := continuous_finsetSum _ fun j _=>cont j
  let F (U : Config G n) := Real.exp (s*f U)
  have hF : Continuous F := (continuous_const.mul hf).rexp
  have pos := positive d ok β Z
  have lo : 0 < mass d β F Z := by
    have small (U : Config G n) : |f U| ≤ K := calc
      _ ≤ ∑ j,|W j U| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : H,(1:ℝ) := sum_le_sum fun j _=>unit j U
      _ = _ := by simp [K]
    have lower : mass d β 1 Z ≤ Real.exp (|s| *K)*mass d β F Z := by
      apply compare d ok β Z continuous_const hF
      intro U
      change 1 ≤ Real.exp _*Real.exp _
      rw [←Real.exp_add,←Real.exp_zero]
      apply Real.exp_monotone
      have h := (neg_abs_le (s*f U))
      rw [abs_mul] at h
      linarith [mul_le_mul_of_nonneg_left (small U) (abs_nonneg s)]
    exact pos_of_mul_pos_right (pos.trans_le lower) (Real.exp_pos _).le
  let P (U : Config G n) := ∏ j,(1+s*W j U)
  have hP : Continuous P := continuous_finsetProd _ fun j _=>continuous_const.add (continuous_const.mul (cont j))
  have est := compare d ok β Z hF hP (Real.exp (K*(2*s^2)))
    (fun U=>product_mgf (fun j=>W j U) (fun j=>unit j U) hs)
  have sw : |s*w| ≤ 1/4 := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_left hw (abs_nonneg s)).trans_eq (mul_one _)).trans hs
  have pp : (1+s*w)^Fintype.card H ≤ Real.exp (K*(s*w)) := by
    rw [show K=(Fintype.card H : ℝ) from rfl,Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith [(abs_le.mp sw).1]) (by linarith [Real.add_one_le_exp (s*w)]) _
  have costs : mass d β F Z ≤ Real.exp (fee+K*(2*s^2+s*w))*mass d β 1 Z := by
    have upper := (div_le_iff₀ pos).mp price
    calc
      _ ≤ Real.exp (K*(2*s^2))*mass d β P Z := est
      _ ≤ Real.exp (K*(2*s^2))*(Real.exp fee*(1+s*w)^Fintype.card H*mass d β 1 Z) :=
        mul_le_mul_of_nonneg_left upper (Real.exp_pos _).le
      _ ≤ Real.exp (K*(2*s^2))*(Real.exp fee*Real.exp (K*(s*w))*mass d β 1 Z) := by gcongr
      _ = _ := by rw [show fee+K*(2*s^2+s*w)=K*(2*s^2)+(fee+K*(s*w)) by ring,Real.exp_add,Real.exp_add fee]; ring
  have log := Real.log_le_log lo costs
  rw [Real.log_mul (Real.exp_pos _).ne' pos.ne',Real.log_exp] at log
  linarith

end YM.Integration.InletSusceptibility.Packet
