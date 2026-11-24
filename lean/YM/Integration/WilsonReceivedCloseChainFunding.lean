import YM.Integration.WilsonReceivedCloseReentry

/-! Sum the fresh errors and restore each subset's own radii along one enrolled close interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseChainFunding
open Filter Finset Lattice Wilson RG RG16 QuadraticLocal.Advent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped BigOperators Classical Topology

variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "B" => budgetR R
local notation "H" => R.alloy.B.a.clock.hatBeta

include simple in
/-- The upper sender can precede the measured interval by a date. -/
theorem upper (degree : ℕ) (Q : ℝ) :
    ∀ᶠ b : ℕ in atTop, ∀ m ≤ b, PaceR.Close R degree Q m b → ∀ N per, b ≤ N →
      ∀ j, m ≤ j → j ≤ N → 0 < regulatorRun R.family N per j ∧
        regulatorRun R.family N per j ≤ 3*regulatorRun R.family N per b := by
  have grows : Tendsto H atTop atTop :=
    tendsto_const_nhds.add_atTop (R.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [PaceR.covers_hat R simple degree Q,grows.eventually_ge_atTop (8:ℝ)]
    with b window warm m mb close N per top j mj jN
  have half := window m m le_rfl mb close
  have rising := WilsonStartup.Timing.hat_mono R.alloy.B.a (Gauge.slopeConstant_pos simple).le mj
  have lower := (R.makes.wilson.represents N per j jN).band.1
  obtain ⟨lb,ub⟩ := (R.makes.wilson.represents N per b top).band
  let x := R.family.path.β N per j
  let y := R.family.path.β N per b
  change H j/2 ≤ x at lower
  change H b/2 ≤ y at lb
  change y ≤ 2*H b at ub
  have x₀ : 0 < x := by linarith only [lower,half,rising,warm]
  have y₀ : 0 < y := by linarith only [lb,warm]
  have a := Real.sqrt_pos.mpr x₀
  have c := Real.sqrt_pos.mpr y₀
  have bound : Real.sqrt y ≤ 3*Real.sqrt x := by
    nlinarith only [a,c,Real.sq_sqrt x₀.le,Real.sq_sqrt y₀.le,
      sq_nonneg (3*Real.sqrt x+Real.sqrt y),sq_nonneg (Real.sqrt x),
      (by linarith only [lower,half,rising,ub] : y ≤ 8*x)]
  refine ⟨inv_pos.mpr a,?_⟩
  change (Real.sqrt x)⁻¹ ≤ 3*(Real.sqrt y)⁻¹
  rw [←one_div,←div_eq_mul_inv,le_div_iff₀ c,div_mul_eq_mul_div,one_mul,div_le_iff₀ a]
  exact bound

private theorem count {i b : ℕ} (ib : i ≤ b) (books : ∀ j ∈ Ico i b, 2 ≤ B j) :
    ((b-i+1:ℕ):ℝ) ≤ PaceR.roof R i b := by
  induction ib using Nat.decreasingInduction with
  | self => simp [PaceR.roof]
  | of_succ j lt ih =>
    have rest := ih (fun k hk => books k (mem_Ico.mpr ⟨(Nat.le_succ j).trans (mem_Ico.mp hk).1,(mem_Ico.mp hk).2⟩))
    have paid := mul_le_mul_of_nonneg_right (books j (mem_Ico.mpr ⟨le_rfl,lt⟩))
      (zero_le_one.trans (PaceR.roof_ge (R:=R) (i:=j+1) (b:=b)))
    rw [PaceR.roof_step R lt,show b-j+1 = (b-(j+1)+1)+1 by omega,Nat.cast_add,Nat.cast_one]
    linarith only [rest,paid,PaceR.roof_ge (R:=R) (i:=j+1) (b:=b)]

include simple in
theorem original (degree a q : ℕ) {Q η ε : ℝ} (cap : 0 ≤ Q) (loss : 0 < η) (ep : 0 ≤ ε) :
    ∀ᶠ b : ℕ in atTop, ∀ m ≤ b, PaceR.Close R degree Q m b → ∀ N per, b ≤ N →
      ∀ i, m ≤ i → i ≤ b → ∀ (w : ℕ → ℝ) (arity : ℕ → ℕ) (e : ℝ), 0 ≤ e →
      (∀ j ∈ Ico i b, 2 ≤ B j ∧ 0 ≤ w j ∧ w j ≤ (B j)^2*(B (j+1))^7 ∧ arity j ≤ a) →
      (∏ j ∈ Ico i b, (w j)^(arity j))*
        (e+∑ j ∈ Ico i b, ε*(regulatorRun R.family N per (min N (j+2)))^q) ≤
      (regulatorRun R.family N per b)^(-η)*(e+ε*(3*regulatorRun R.family N per b)^q) := by
  filter_upwards [WilsonReceivedCloseReentry.envelope R simple degree a cap loss,upper R simple degree Q]
    with b fiscal band m mb close N per top i mi ib w arity e e₀ books
  let income := ε*(3*regulatorRun R.family N per b)^q
  have income₀ : 0 ≤ income := mul_nonneg ep (pow_nonneg (mul_nonneg (by norm_num)
    ((band m mb close N per top b mb top).1.le)) _)
  have remain : e+∑ j ∈ Ico i b, ε*(regulatorRun R.family N per (min N (j+2)))^q ≤
      (PaceR.roof R i b)*(e+income) := by
    have each (j:ℕ) (hj:j ∈ Ico i b) := band m mb close N per top (min N (j+2))
      (by have h := (mem_Ico.mp hj).1; omega) (min_le_left ..)
    have all := sum_le_sum (s:=Ico i b) (fun j hj => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (each j hj).1.le (each j hj).2 q) ep)
    rw [sum_const,Nat.card_Ico,nsmul_eq_mul] at all
    have nr : (0:ℝ) ≤ (b-i:ℕ) := Nat.cast_nonneg _
    calc
      _ ≤ e+((b-i:ℕ):ℝ)*income := add_le_add_right all e
      _ ≤ ((b-i+1:ℕ):ℝ)*(e+income) := by
        rw [Nat.cast_add,Nat.cast_one]
        nlinarith only [income₀,mul_nonneg nr e₀]
      _ ≤ _ := mul_le_mul_of_nonneg_right (count R ib (fun j h => (books j h).1)) (add_nonneg e₀ income₀)
  have subset := prod_le_prod (s:=Ico i b) (fun j h => pow_nonneg (books j h).2.1 _) (fun j h => by
    obtain ⟨_,nn,price,load⟩ := books j h
    rw [pow_mul,pow_mul,←mul_pow]
    exact (pow_le_pow_left₀ nn price _).trans (pow_le_pow_right₀
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (budget_pos R)) (one_le_pow₀ (budget_pos R))) load) :
    ∀ j ∈ Ico i b, (w j)^(arity j) ≤ (B j)^(2*a)*(B (j+1))^(7*a))
  have P₀ := prod_nonneg (s:=Ico i b) (fun j _ => mul_nonneg (pow_nonneg (zero_le_one.trans (budget_pos (i:=j) R)) (2*a))
    (pow_nonneg (zero_le_one.trans (budget_pos (i:=j+1) R)) (7*a)))
  calc
    _ ≤ (∏ j ∈ Ico i b, (B j)^(2*a)*(B (j+1))^(7*a))*((PaceR.roof R i b)*(e+income)) :=
      mul_le_mul subset remain (add_nonneg e₀ (sum_nonneg (fun j hj => mul_nonneg ep (pow_nonneg
        ((band m mb close N per top (min N (j+2)) (by have h := (mem_Ico.mp hj).1; omega) (min_le_left ..)).1.le) _)))) P₀
    _ = _ := (mul_assoc ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (fiscal m mb close N per top i mi ib) (add_nonneg e₀ income₀)

end YM.Integration.WilsonReceivedCloseChainFunding
