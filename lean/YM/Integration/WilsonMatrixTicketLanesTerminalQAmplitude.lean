import YM.Integration.WilsonMatrixTicketLanesTerminalQGrades

/-! Compact gross income for the genuine normalized first Wilson block at every period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesTerminalQAmplitude
open Function MeasureTheory Filter Finset Lattice RG Wilson RGComparison.Core16 RGComparison.Core16.Spool
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I] (J:I→Lamp G)

theorem compact : ∃C:ℝ,0≤C ∧ ∀(b:Side)(o:I→Site b)(U:Config G b),‖tally J o U‖≤C:=by
  choose A hA using fun i=>(isCompact_range (J i).regular.norm).bddAbove
  refine ⟨∏i,|A i|,prod_nonneg fun _ _=>abs_nonneg _,fun b o U=>?_⟩
  rw [tally,norm_prod]
  exact prod_le_prod (fun _ _=>norm_nonneg _) fun i _=>
    ((hA i (Set.mem_range.mpr ⟨expandAt (o i) U,rfl⟩)).trans (le_abs_self _))

theorem normalized {C:ℝ}(cp:0≤C)
    (price:∀(b:Side)(o:I→Site b)(U:Config G b),‖tally J o U‖≤C)
    {c f:Side}(S:StepData c f)(u:Directions G c)(o:I→Site f){g:ℝ}(gp:0<g)(law:S.IsKernel (g⁻¹^2) G):
    ‖reads J S u o g‖≤g⁻¹^(power J)*C:=by
  let β:=g⁻¹^2
  let V:=Parcel.Oven.slice u g
  let w (U:Config G f):=S.density β U V * bare β U
  have wp (U):0≤w U:=mul_nonneg (law.positive U V) (bare_pos β U).le
  have wi:Integrable w (prior G f):=StepData.push_slice law V (bare β) (bare_integrable β)
  let Z:=∫U,w U ∂prior G f
  have zp:0≤Z:=integral_nonneg wp
  have denom:spinVac (G:=G) S u g=Z:=rfl
  have raw:‖survey J S u o g‖≤Z*C:=by
    calc
      _≤∫U,‖S.density β U V • (bare β U • column J o U)‖ ∂prior G f:=norm_integral_le_integral_norm _
      _≤∫U,w U*C ∂prior G f:=integral_mono_of_nonneg (ae_of_all _ fun _=>norm_nonneg _) (wi.mul_const C)
        (ae_of_all _ fun U=>by
          change ‖S.density β U V • (bare β U • column J o U)‖ ≤ w U*C
          have combined:S.density β U V • (bare β U • column J o U)=w U • column J o U:=smul_smul .. 
          rw [combined,norm_smul,Real.norm_eq_abs,abs_of_nonneg (wp U)]
          exact mul_le_mul_of_nonneg_left (price f o U) (wp U))
      _=Z*C:=integral_mul_const ..
  have inv:‖(spinVac (G:=G) S u g)⁻¹ • survey J S u o g‖≤C:=by
    rw [denom,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr zp)]
    by_cases zero:Z=0
    · simpa only [zero,inv_zero,zero_mul] using cp
    · exact (mul_le_mul_of_nonneg_left raw (inv_nonneg.mpr zp)).trans_eq (by rw [←mul_assoc,inv_mul_cancel₀ zero,one_mul])
  unfold reads
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (inv_pos.mpr gp).le _)]
  exact mul_le_mul_of_nonneg_left inv (pow_nonneg (inv_pos.mpr gp).le _)

end YM.Integration.WilsonMatrixTicketLanesTerminalQAmplitude
