import YM.Integration.WilsonSeparatedPrefixMovingHomeEars

/-! Contracting the original source and its filed singleton with the same
complex dose at its actual homes. Each occupied charge is cleared once. -/
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixUnitWeight
open Function Set Finset MeasureTheory Lattice RG Wilson Source
open PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open WilsonSeparatedPrefixCohortUnscale (product salary)
open WilsonSeparatedPrefixMovingHomeEars (returned)
open private scale from YM.Integration.WilsonThermometerOccupiedLinear
open private scaled from YM.Integration.WilsonSeparatedPrefixCohortUnscale
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type*}{N p f b:ℕ}
local notation "C" => R.family
local notation "X" t:max => Config G ((C).side t p)
local notation "P" => (C).path.rep N p f

private theorem scalar {K j:ℕ}(step:j≤K)(D:X K→ℂ)
    (paid:Integrable (fun U=>((C).path.rep N p K).eval U • D U) (prior G _))
    (z:ℂ)(W:X j):
    actualTransport (C) (N:=N) (fun U=>z*D U) step W=z*actualTransport (C) (N:=N) D step W:=by
  let H:=fun U:X K=>((C).path.rep N p K).eval U • D U
  have exact:(fun U=>((C).path.rep N p K).eval U • (z*D U))=z • H:=by
    funext U;exact smul_comm _ z (D U)
  unfold actualTransport
  rw [exact,scale R z H paid step]
  exact smul_comm _ z _

theorem original (live:f≤N)(age:b≤f)(s:Finset I)(χ:I→ℝ)(pos:∀i,0<χ i)(θ:I→ℂ)
    (unit:∀i,‖θ i‖≤1)(A:I→X N→ℂ)(B:I→X f→ℂ)(fund:∀i,funded (A i))(W:X b)
    {ε:ℝ}(ep:0≤ε)
    (original:returned (R:=R) live age (product s A) (product s (fun i U=>(χ i:ℂ)*B i U)) W
      ((∏i∈s,χ i)*ε)):
    returned (R:=R) live age (product s (fun i U=>(θ i/(χ i:ℂ))*A i U))
      (product s (fun i U=>θ i*B i U)) W ε:=by
  let z:=∏i∈s,θ i/(χ i:ℂ)
  let old:=product s (fun i U=>(χ i:ℂ)*B i U)
  let all:=product s A
  let null:=fun U=>actualTransport (C) (N:=N) all live U-old U
  have upper:product s (fun i U=>(θ i/(χ i:ℂ))*A i U)=fun U=>z*all U:=by
    funext U;simp only [product,z,all,prod_mul_distrib]
  have lower:product s (fun i U=>θ i*B i U)=fun U=>z*old U:=by
    funext U
    simp only [product,z,old,←prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    field_simp [(Complex.ofReal_ne_zero.mpr (pos i).ne')]
  obtain ⟨priorOld,price⟩:=original
  have wholesome:=salary s A fund
  have good:Integrable (fun U=>(P).eval U • null U) (prior G _):=by
    obtain ⟨limit,bnd⟩:=wholesome.2
    have full:=actualTransport_weighted_integrable (C) R.makes (N:=N) (p:=p) (le_refl N) wholesome.1.aestronglyMeasurable bnd live
    convert full.sub priorOld using 1
    funext U
    simp only [null,old,all,smul_sub,Complex.real_smul,Pi.sub_apply]
  rw [upper,lower]
  refine ⟨?_,?_⟩
  · convert priorOld.smul z using 1
    funext U;simp only [Pi.smul_apply,smul_eq_mul,old];ring
  · have combine:(fun U=>actualTransport (C) (N:=N) (fun W=>z*all W) live U-z*old U)=fun U=>z*null U:=by
      funext U
      rw [scaled R (le_rfl:N≤N) live all wholesome z U,mul_sub]
    simp only [combine,scalar R age null good z W,norm_mul]
    apply (mul_le_mul_of_nonneg_left price (norm_nonneg z)).trans
    have cancel:‖z‖*(∏i∈s,χ i)=∏i∈s,‖θ i‖:=by
      rw [show ‖z‖=∏i∈s,‖θ i/(χ i:ℂ)‖ from norm_prod ..,←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (pos i).le,div_mul_cancel₀ _ (pos i).ne']
    rw [←mul_assoc,cancel]
    exact (mul_le_mul_of_nonneg_right (Finset.prod_le_one (fun i _=>norm_nonneg _) (fun i _=>unit i)) ep).trans_eq (one_mul _)

end YM.Integration.WilsonSeparatedPrefixUnitWeight
end
