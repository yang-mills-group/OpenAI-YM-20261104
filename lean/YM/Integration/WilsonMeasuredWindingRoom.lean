import YM.Integration.WilsonMeasuredWindingSum

/-! On the original measured calendar an enrolled polynomial incoming norm
fits the allowance for a single propagated winding error at its reporting age. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredWindingRoom
open Filter Lattice RG PhysicalNext.Repeat.Legato ActualRunAdmissionScales ActualRunAdmissionClock
open WilsonMeasuredWindingSum
open scoped Topology BigOperators
variable {G : Gauge}

theorem original (R : Run G) (simple : G.Simple) (readout : RG05Preconstruction.ReadoutPurchase R.b)
    (degree d load : ℕ) (C K : ℝ) :
    let L := R.family.path.levels
    let p := degree + (d+1)*load
    ∀ᶠ i in atTop, ∀ τ A : ℝ, 0 ≤ τ → τ ≤ room L K i → 0 ≤ A →
      A ≤ C*(L.clock.hatBeta i)^d →
      τ*(admittedCost L i)^degree*A^load ≤ room L (K+p) i := by
  intro L p
  have mesh := ActualRunQLocalAdmission.actual_preMesh R readout
  filter_upwards [cost_subpower R.family simple R.makes mesh 1 zero_lt_one,
    actual_inverse_lower R.family simple R.makes mesh,
    (WardBin.bell L simple).eventually_ge_atTop (max 1 C)] with i cost band high
  let H := L.clock.hatBeta i
  have hh : 1 ≤ H := (le_max_left ..).trans high
  have hpos : 0 < H := zero_lt_one.trans_le hh
  have HC : C ≤ H := (le_max_right ..).trans high
  let g := Pert.Asymptotics.regulatorRun R.family (i+1) 0 (i+1)
  have hg : H⁻¹ ≤ g := band (i+1) 0 (Nat.lt_succ_self i)
  have cg : admittedCost L i ≤ g⁻¹ := by
    simpa only [Real.rpow_neg_one] using cost (i+1) 0 (Nat.lt_succ_self i)
  have hc : admittedCost L i ≤ H := cg.trans (by simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hpos) hg)
  have hact : 0 ≤ admittedCost L i := zero_le_one.trans (admittedCost_one L i)
  have sx : 0 ≤ L.S.scale i := by
    change 0 ≤ Real.log ((L.S.a i)⁻¹)
    apply Real.log_nonneg
    have h : (1:ℝ) ≤ ((L.S.denominator i).val:ℝ) := by exact_mod_cast (L.S.denominator i).pos
    simpa [Schedule.a] using h
  have lp : 0 ≤ Real.log (2+H) := Real.log_nonneg (by linarith)
  have hroom : H^p ≤ room L (p:ℝ) i := by
    calc H^p ≤ (2+H)^p := pow_le_pow_left₀ hpos.le (by linarith) _
         _ = Real.exp ((p:ℝ)*Real.log (2+H)) := by
           rw [Real.exp_nat_mul,Real.exp_log (by linarith : 0<2+H)]
         _ ≤ _ := Real.exp_le_exp.mpr (by
           dsimp [room,H]
           exact mul_le_mul_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α:=ℝ) p]) lp)
  intro τ A ht hτ hz hA
  have ap : A ≤ H^(d+1) := hA.trans (by
    rw [pow_succ,mul_comm (H^d) H]
    exact mul_le_mul_of_nonneg_right HC (pow_nonneg hpos.le _))
  calc τ*(admittedCost L i)^degree*A^load ≤ room L K i*H^degree*(H^(d+1))^load :=
         mul_le_mul (mul_le_mul hτ (pow_le_pow_left₀ hact hc _) (pow_nonneg hact _) (Real.exp_pos _).le)
           (pow_le_pow_left₀ hz ap _) (pow_nonneg hz _)
           (mul_nonneg (Real.exp_pos _).le (pow_nonneg hpos.le _))
       _ = room L K i*H^p := by dsimp only [p]; rw [←pow_mul,pow_add]; ring
       _ ≤ room L K i*room L (p:ℝ) i := mul_le_mul_of_nonneg_left hroom (Real.exp_pos _).le
       _ = _ := by unfold room; rw [←Real.exp_add]; congr 1; ring

end YM.Integration.WilsonMeasuredWindingRoom
end

