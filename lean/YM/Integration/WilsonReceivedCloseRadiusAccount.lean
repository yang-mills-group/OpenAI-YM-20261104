import YM.Integration.WilsonReceivedClosePhysicalBirths
import YM.Integration.WilsonReceivedCloseSlate

/-! Restoring each original source radius before an ordinary close reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseRadiusAccount
open Finset Lattice Marker
open scoped BigOperators

/-- The actual fitted radius loss at the first joint admission is bounded by the adjoining page. -/
theorem reserve {h Ω U e κ g upper bill : ℝ} (p : ℕ)
    (old : 4 ≤ Ω) (kept : Ω ≤ U) (kp : 0 < κ) (unit : κ ≤ 1)
    (gp : 0 < g) (cold : 3*g ≤ 1) (up : 0 ≤ upper) (temp : upper ≤ 3*g)
    (head : 8*Ω*e ≤ κ*(3*g)^p) (account : bill ≤ 8*Ω*e+κ*upper^p)
    (paid : h ≤ max (max 1 bill) (Ω^5+1)) : h ≤ U^6 := by
  have once : κ*(3*g)^p ≤ 1 := mul_le_one₀ unit (pow_nonneg (by positivity) _) (pow_le_one₀ (by positivity) cold)
  have invoice : bill ≤ 2 := calc
    _ ≤ κ*(3*g)^p+κ*(3*g)^p := account.trans (add_le_add head
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ up temp _) kp.le))
    _ ≤ 1+1 := add_le_add once once
    _ = 2 := by norm_num
  have one : 1 ≤ U := by linarith only [old,kept]
  have two : 2 ≤ U := by linarith only [old,kept]
  apply paid.trans
  apply max_le
  · apply max_le (one_le_pow₀ one)
    exact invoice.trans (two.trans (by simpa only [pow_one] using (pow_le_pow_right₀ one (by decide:1≤6))))
  · calc
      _ ≤ U^5+U^5 := add_le_add (pow_le_pow_left₀ (by linarith only [old]) kept _) (one_le_pow₀ one)
      _ = U^5*2 := by ring
      _ ≤ U^5*U := mul_le_mul_of_nonneg_left two (pow_nonneg (zero_le_one.trans one) _)
      _ = _ := by ring

variable {V : Type} [DecidableEq V] {R : Census V}

def registered (old fresh: Finset V) (u f w : V→ℝ) (v : V) : ℝ :=
  if v∈old then u v else if v∈fresh then f v else w v

/-- A fixed number of labels can spend their published inverse powers once at their births. The
product of all adjoining page costs is independently paid using the reporter calendar. -/
theorem published (old fresh : Finset V) (u f w : V→ℝ)
    (wu : ∀v,0<u v) (wf : ∀v,0<f v) (ww : ∀v,0<w v)
    {stage U F g κ η : ℝ} (hf : 0 ≤ F) (st : 1 ≤ stage)
    (gp : 0<g) (cold : 3*g ≤ 1) (nu nf a p : ℕ)
    (oldPaid : ∀ v∈old, u v ≤ stage^2*(U*(g⁻¹)^(2*nu))*w v)
    (freshPaid : ∀ v∈fresh, f v ≤ stage*(F*(g⁻¹)^(2*nf))*w v)
    (roof : stage^(2*a) ≤ g^(-η)) (power : 2*(max nu nf)*a ≤ p) :
    ∃ c : ℝ, 0 ≤ c ∧
      (∀ s : R.Mode, s.val.card ≤ a → Poly.toll (registered old fresh u f w) s ≤ c*Poly.toll w s) ∧
      c*(g^(-η)*(5*κ*(3*g)^p)) =
        5*κ*(3:ℝ)^p*(max 1 (max U F))^a*(g^(-η)*g^(-η))*g^(p-2*(max nu nf)*a) := by
  let D := max nu nf
  let A := max 1 (max U F)
  let y := g⁻¹
  have y₁ : 1 ≤ y := by
    change 1 ≤ g⁻¹
    rw [←one_div,le_div_iff₀ gp,one_mul]
    linarith only [cold,gp]
  have yp := zero_lt_one.trans_le y₁
  have A₁ : 1 ≤ A := le_max_left _ _
  let cost := stage^2*(A*y^(2*D))
  have cn : 1 ≤ cost := one_le_mul_of_one_le_of_one_le (one_le_pow₀ st)
    (one_le_mul_of_one_le_of_one_le A₁ (one_le_pow₀ y₁))
  have growth (v:V) : registered old fresh u f w v ≤ cost*w v := by
    unfold registered
    by_cases h:v∈old
    · rw [if_pos h]
      apply (oldPaid v h).trans
      apply mul_le_mul_of_nonneg_right _ (ww v).le
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact mul_le_mul ((le_max_left _ _).trans (le_max_right _ _))
        (pow_le_pow_right₀ y₁ (Nat.mul_le_mul_left 2 (le_max_left _ _))) (pow_nonneg yp.le _) (zero_le_one.trans A₁)
    · rw [if_neg h]
      by_cases h':v∈fresh
      · rw [if_pos h']
        apply (freshPaid v h').trans
        apply mul_le_mul_of_nonneg_right _ (ww v).le
        exact mul_le_mul (by simpa only [pow_one] using pow_le_pow_right₀ st (by decide:1≤2))
          (mul_le_mul ((le_max_right _ _).trans (le_max_right _ _))
            (pow_le_pow_right₀ y₁ (Nat.mul_le_mul_left 2 (le_max_right _ _))) (pow_nonneg yp.le _) (zero_le_one.trans A₁))
          (mul_nonneg hf (pow_nonneg yp.le _)) (sq_nonneg _)
      · rw [if_neg h']; exact le_mul_of_one_le_left (ww v).le cn
  let allot := g^(-η)*A^a*y^(2*D*a)
  have salary : cost^a ≤ allot := by
    calc
      cost^a = stage^(2*a)*A^a*y^(2*D*a) := by dsimp only [cost]; rw [mul_pow,mul_pow,←pow_mul,←pow_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right roof (pow_nonneg
        (zero_le_one.trans A₁) _)) (pow_nonneg yp.le _)
  have spend : 2*D*a ≤ p := power
  have restore : y^(2*D*a)*g^p = g^(p-2*D*a) := by
    have decomp : g^p = g^(2*D*a)*g^(p-2*D*a) := by rw [←pow_add]; congr 1; omega
    change (g⁻¹)^_*_ = _
    rw [decomp,inv_pow,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ gp.ne'),one_mul]
  refine ⟨allot,(pow_nonneg (zero_le_one.trans cn) _).trans salary,?_,?_⟩
  · intro s cardS
    unfold Poly.toll
    calc
      _ ≤ ∏v∈s.val,cost*w v := Finset.prod_le_prod (fun i _=>by
        unfold registered
        split_ifs
        · exact (wu i).le
        · exact (wf i).le
        · exact (ww i).le) (fun i _=>growth i)
      _ = cost^s.val.card*(∏ v∈s.val,w v) := by rw [Finset.prod_mul_distrib]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right ((pow_le_pow_right₀ cn cardS).trans salary)
        (Finset.prod_nonneg (fun v _=>(ww v).le))
  · calc
      _ = 5*κ*(3:ℝ)^p*A^a*(g^(-η)*g^(-η))*(y^(2*D*a)*g^p) := by dsimp only [allot]; rw [mul_pow]; ring
      _ = _ := by rw [restore]

end YM.Integration.WilsonReceivedCloseRadiusAccount
