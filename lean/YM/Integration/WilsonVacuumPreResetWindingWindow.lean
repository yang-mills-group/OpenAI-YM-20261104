import YM.Integration.WilsonVacuumPreResetAngularDifference

/-! Reserve a portion of the exponentially small incoming finite-volume error
for the torus width before testing the original finite update. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetWindingWindow
open Function Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Winding WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {α:Type*} {n:Side} {r:ℕ}

/-- The real physical periodic diameter is at most four side lengths, uniformly
in the number of angular arguments. -/
theorem diameter (x:Fin r→(Site n × α)):soar (tor n) x ≤ 4*n.val:=by
  apply league_le
  intro i j
  let z:Site n:=(x j).1-(x i).1
  change (∑a:Axis,(Lattice.lift z a).natAbs) ≤ 4*n.val
  calc
    _ ≤ ∑_a:Axis,n.val:=Finset.sum_le_sum fun a _=>by
      rw [Lattice.lift,ZMod.valMinAbs_natAbs_eq_min]
      exact (min_le_left ..).trans (ZMod.val_lt ..).le
    _=4*n.val:=by simp [Axis]

private theorem small (s A:ℝ) (width:0 ≤ s)(price:0 ≤ A)(P:Ten ℝ (Site n × α) r)
    (step:stroll P)(per:∀x,|pruce P x| ≤ A*Real.exp (-s*(4*n.val))):
    Sight P 0 s A:=by
  refine ⟨⟨price,fun x=>?_⟩,⟨price,fun x=>?_⟩,⟨price,fun x _=>?_⟩,step⟩
  · rw [Real.norm_eq_abs]
    apply (per x).trans
    apply mul_le_mul_of_nonneg_left _ price
    apply Real.exp_le_exp.mpr
    have size:((soar (tor n) x:ℕ):ℝ) ≤ 4*n.val:=by exact_mod_cast diameter x
    linarith [mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr width) (sub_nonneg.mpr size)]
  · simp only [Pi.zero_apply,norm_zero]
    exact mul_nonneg price (Real.exp_pos _).le
  · simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs]
    apply (per _).trans
    apply mul_le_mul_of_nonneg_left _ price
    apply Real.exp_le_exp.mpr
    have size:(n.val:ℝ) ≤ 4*n.val:=by have h:(0:ℝ) ≤ n.val:=Nat.cast_nonneg _;linarith
    linarith [mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr width) (sub_nonneg.mpr size)]

/-- For every observation node in the unit interval the same native winding
calculation can receive the amplified signed fine input on this torus. -/
theorem submitted (s A C t η:ℝ) (width:0 ≤ s)(price:0 ≤ A)(unit:0<η)(clock:|t| ≤ 1)
    (P Q:Ten ℝ (Site n × α) r)(U:Ten ℝ (Cloth α) r)(step:stroll P)(base:Sight Q U s C)
    (per:∀x,|pruce (P-Q) x| ≤ A*η*Real.exp (-s*(4*n.val))):
    Sight (Q+(t/η)•(P-Q)) U s (C+A):=by
  have march:stroll ((t/η)•(P-Q)):=fun z x=>by
    simp only [Pi.smul_apply,Pi.sub_apply,step z x,base.strollT z x]
  have head:Sight ((t/η)•(P-Q)) 0 s A:=small s A width price _ march fun x=>by
    rw [pruce_mu,Pi.smul_apply,smul_eq_mul,abs_mul,abs_div,abs_of_pos unit]
    calc
      _ ≤ (|t|/η)*(A*η*Real.exp (-s*(4*n.val))):=
        mul_le_mul_of_nonneg_left (per x) (div_nonneg (abs_nonneg _) unit.le)
      _=|t| *(A*Real.exp (-s*(4*n.val))):=by field_simp
      _ ≤ A*Real.exp (-s*(4*n.val)):=mul_le_of_le_one_left
        (mul_nonneg price (Real.exp_pos _).le) clock
  simpa only [add_zero] using base.add head

end YM.Integration.WilsonVacuumPreResetWindingWindow
end
