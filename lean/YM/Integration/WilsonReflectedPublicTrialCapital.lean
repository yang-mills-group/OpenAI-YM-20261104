import YM.Integration.WilsonReflectedPublicOpticalSwaps
/-! The raw engineering cost of a genuine fixed-cutoff guarded coordinate
in the reflected physical joint trial. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicTrialCapital
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Next.Rank MergeProof Push.Local
open WilsonOriginalMicroscopicGuardedPage WilsonOriginalMicroscopicGuardedReporters WilsonReflectedFundedHearing WilsonReflectedFullPanel
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)
local notation "C₀" => R.family
local notation "mesh" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

theorem travel {j K:ℕ}(age:j≤K):stretch R (1/32) j K≤2*(mesh j/mesh K):=by
  have pos:=div_pos ((C₀).S.a_pos j) ((C₀).S.a_pos K)
  have le:1 ≤ mesh j/mesh K :=(one_le_div ((C₀).S.a_pos K)).mpr ((C₀).S.strictAnti.antitone age)
  unfold WilsonOriginalMicroscopicGuardedReporters.stretch
  rw [←WilsonReflectedRelativeDate.ratio]
  nth_rw 2 [←Real.exp_log pos]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  apply Real.exp_le_exp.mpr
  have l:=Real.log_nonneg le
  linarith only [l]

private theorem accounting {H az ak wrap fee C:ℝ} (d t:ℕ)(hp:1≤H)
    (a:0<az)(b:0<ak)(v:0≤fee)(_w:0≤wrap)(cp:0≤C)
    (trip:az/ak≤H^t)(wallet:wrap≤C*H^2):
    (ak^d)⁻¹*(2*(az/ak)*(wrap*(az^d*fee)))≤2*C*H^(t*(d+1)+2)*fee:=by
  have ratio:=div_nonneg a.le b.le
  calc
    _ = 2*wrap*((az/ak)^(d+1))*fee := by rw [pow_succ,div_pow];ring
    _ ≤ 2*(C*H^2)*((H^t)^(d+1))*fee := by
      apply mul_le_mul_of_nonneg_right _ v
      exact mul_le_mul (mul_le_mul_of_nonneg_left wallet (by norm_num)) (pow_le_pow_left₀ ratio trip _)
        (pow_nonneg ratio _) (mul_nonneg (by norm_num) (mul_nonneg cp (pow_nonneg (zero_le_one.trans hp) _)))
    _ = _ := by rw [←pow_mul,pow_add];ring

theorem priced {d N p j f K t q:ℕ}(head:j≤K)(_h:j≤f)(top:K≤N)
    {M:(C₀).label d≃ₗ[ℂ](C₀).label d}{Y:(C₀).label d}{C fee:ℝ}
    (cp:0≤C)(v:0≤fee)(hp:1≤β f)
    (trip:mesh j/mesh K≤(β f)^t)(wrap:0≤1+wrapCost R d j)(cash:1+wrapCost R d j≤C*(β f)^2)
    (paid:receipt R d j K N p q head top (1/32) M Y (mesh j^d*fee))
    (s:Motion){dose:ℂ}(small:‖dose‖≤1):
    let w:=M.symm (WilsonOriginalMicroscopicGuardedPage.full R d N p j Y)
    let v₀:=Motion.patch ((C₀).labels.level d) s w
    let z:=dose*(((mesh K:ℂ)^d)⁻¹)
    ‖z‖*((C₀).labels.level d).coeffSize v₀ ≤
      (orbitCost ((C₀).labels.level d)*(2*C))*(β f)^(t*(d+1)+2)*fee:=by
  intro w v₀ z
  let Ω:=orbitCost ((C₀).labels.level d)
  have op:0≤Ω:=zero_le_one.trans (orbitCost_one_le _)
  have wb:=paid.2.1
  change ((C₀).labels.level d).coeffSize w≤_ at wb
  have aw:((C₀).labels.level d).coeffSize v₀≤
      Ω*(2*(mesh j/mesh K)*((1+wrapCost R d j)*(mesh j^d*fee))):=
    (patch_cost _ s w).trans (mul_le_mul_of_nonneg_left
      (wb.trans (mul_le_mul_of_nonneg_right (travel R head) (mul_nonneg wrap (mul_nonneg
        (pow_nonneg ((C₀).S.a_pos j).le _) v)))) op)
  have cost:‖z‖≤(mesh K^d)⁻¹:=by
    rw [show z=dose*(((mesh K:ℂ)^d)⁻¹) from rfl,norm_mul,norm_inv,norm_pow,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((C₀).S.a_pos K)]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (pow_nonneg ((C₀).S.a_pos K).le _)) small
  have price:=accounting d t hp ((C₀).S.a_pos j) ((C₀).S.a_pos K) v wrap cp trip cash
  calc
    _ ≤ (mesh K^d)⁻¹*(Ω*(2*(mesh j/mesh K)*((1+wrapCost R d j)*(mesh j^d*fee)))) :=
      mul_le_mul cost aw (Work.G08.size_nonneg ..) (inv_nonneg.mpr (pow_nonneg ((C₀).S.a_pos K).le _))
    _ = Ω*((mesh K^d)⁻¹*(2*(mesh j/mesh K)*((1+wrapCost R d j)*(mesh j^d*fee)))) :=by ring
    _ ≤ Ω*(2*C*(β f)^(t*(d+1)+2)*fee) :=mul_le_mul_of_nonneg_left price op
    _ = _ :=by ring

end YM.Integration.WilsonReflectedPublicTrialCapital
end
