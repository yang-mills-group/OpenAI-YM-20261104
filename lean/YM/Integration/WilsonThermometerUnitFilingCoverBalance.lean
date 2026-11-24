import YM.Integration.WilsonThermometerUnitFilingCoverRegister

/-! A single physical inverse power pays the rooted claim at every retained Taylor degree. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverBalance
open Finset Lattice RG Wilson Marker
open RegulatorIR Taping Budget Budget.Packet Prim Profiles Halo Ledger Ledger.Sky Oracle Uniform
open WilsonThermometerUnitFilingCoverRegister
open WilsonThermometerUnitFilingCoverCurrency (gross part sign)
open scoped Classical BigOperators ENNReal

theorem restored {β C w g cash:ℝ}(ready:0≤β)(gp:0<g)(cp:0≤cash)(heat:β*g^2≤2)
    (d:ℕ)(income:C/w≤(1+cash)/g^d)(G:Gauge)(h u accuracy e:ℕ)(wanted:e≤accuracy):
    WilsonThermometerUnitFilingCoverInvoice.invoice G (e+h) u 1 β C w ≤
      2*gross G h u accuracy*(1+cash)/g^(d+2):=by
  let A:=part G h u e
  have ap:0≤A:=sign h u e
  have paid:A≤gross G h u accuracy:=Finset.single_le_sum (fun j _=>sign h u j)
    (Finset.mem_range.mpr (by omega))
  unfold WilsonThermometerUnitFilingCoverInvoice.invoice
  rw [Real.rpow_one]
  change A*β*C/w≤_
  calc
    _ = A*β*(C/w):=by ring
    _ ≤ A*β*((1+cash)/g^d):=mul_le_mul_of_nonneg_left income (mul_nonneg ap ready)
    _ ≤ _:=by
      apply (le_div_iff₀ (pow_pos gp _)).mpr
      calc
        _ = A*(1+cash)*(β*g^2):=by rw [pow_add];field_simp
        _ ≤ A*(1+cash)*2:=mul_le_mul_of_nonneg_left heat (mul_nonneg ap (by linarith))
        _ ≤ _:=by nlinarith [mul_le_mul_of_nonneg_right paid (show 0≤1+cash by linarith)]

variable {G:Gauge}{W:Type}{steps:W→ℕ}{sides:Page steps→Side}(Z:Circuit steps sides)
  {K:KernelChoices}(scheme:Program K)(branches:∀ P:Patch,P.Branches K G)(units:Page steps→Binding.Scale)
local notation "L" => Z.dialect scheme G branches units
variable (T:Ledger.Sky.Accounts (Z.dialect scheme G branches units))
  {m:Uniform.Meter W}{p b h:ℕ}(P:Ledger.Sky.Primitive (Z.dialect scheme G branches units) m p b)
  (k:Choice steps)(S:W→Submission G)(paid:∀v,(S v).grades ()+1=h)
local notation "report" => WilsonThermometerUnitFilingCoverEra.filed (L) T P k (fun v=>field (S v))
  (fun v=>stamp (S v) (paid v))

theorem original (meter:Uniform.Meter W)(β g cash:W→ℝ)(late:∀v,Real.exp 1≤β v)
    (width:∀v,Real.exp ((S v).σ⁻¹^2)≤β v)
    (gp:∀v,0<g v)(cp:∀v,0≤cash v)(heat:∀v,β v*(g v)^2≤2)
    (d:ℕ)(income:∀v,(S v).cost/((S v).rad ())≤(1+cash v)/(g v)^d)
    (accuracy e r u:ℕ)(wanted:e≤accuracy):
    Claim meter (fun v=>(L).coverQ (fun _=>0) u (k.choose v))
      (fun v=>ENNReal.ofReal (2*gross G h u accuracy*(1+cash v)/(g v)^(d+2)))
      (fun v=>(report).main (Page.opening k.after.spans v) e r):=by
  obtain ⟨f,fo,enough⟩:=WilsonThermometerUnitFilingCoverRegister.original
    Z scheme branches units T P k S paid meter β late width one_pos e r u
  refine ⟨f,fo,fun v=>(enough v).trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _)⟩
  exact restored ((Real.exp_pos 1).le.trans (late v)) (gp v) (cp v) (heat v) d (income v) G h u accuracy e wanted

end YM.Integration.WilsonThermometerUnitFilingCoverBalance
