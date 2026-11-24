import YM.Integration.WilsonThermometerNumericalStation
import YM.Integration.WilsonOriginalCoverJetColors

/-! The measured inverse-beta coin has zero linear term. Its genuine
back substitution preserves the entire first deposited face, including a
field-dependent zeroth face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalClockSlope
open Function Finset Filter Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Assembly
open Comparison.RG02.Moving AllOrder AllOrder.Floe PowerSeries Laurent QuadraticLocal
open scoped Classical Topology BigOperators

private theorem flat_tariff (p:Caliber) (z:p.measure 1=0) (h:ℕ) :
    HasDerivAt (p.tariff h) 0 0 := by
  have term (i:ℕ) : HasDerivAt (fun t:ℝ=>t^i*p.measure i) 0 0 := by
    cases i with
    | zero=>simp only [pow_zero,one_mul];exact hasDerivAt_const ..
    | succ i=>
      cases i with
      | zero=>simp only [z,mul_zero];exact hasDerivAt_const ..
      | succ i=>simpa [Nat.succ_eq_add_one] using ((hasDerivAt_pow (i+2) (0:ℝ)).mul_const (p.measure (i+2)))
  unfold Caliber.tariff
  convert! HasDerivAt.fun_sum (u:=range (h+1)) (fun i _=>term i) using 1; simp

theorem rating (q:Pace.Coin) (a:ℝ) (income:Pace.Earn q a) (depth:ℕ) :
    HasDerivAt ((Rebirth.caliber q income.1).back depth).rating 0 0 := by
  let p:=Rebirth.caliber q income.1
  have q1:p.measure 1=0:=by
    change q 1+PositionX.Jet.just 1 1=0
    simp [income.2.1,PositionX.Jet.just]
  have dz:=flat_tariff p q1 depth
  have direct:HasDerivAt (p.direct depth).rating 0 0:= by
    change HasDerivAt (fun t:ℝ=>(Real.sqrt (p.tariff depth t))⁻¹) 0 0
    have sq:=dz.sqrt (by simp [p.zero_tariff])
    convert! sq.inv (by simp [p.zero_tariff]) using 1; simp [p.zero_tariff]
  let K:=p.direct depth
  have back:HasDerivAt K.backmap (deriv K.backmap 0) 0 :=
    (K.back_smooth.differentiableAt (by simp)).hasDerivAt
  change HasDerivAt (fun x=>(K.rating (K.backmap x))⁻¹) 0 0
  have at0:HasDerivAt K.rating 0 (K.backmap 0):=K.back_origin.symm ▸ direct
  convert! (at0.comp 0 back).inv (by simp [K.origin]) using 1; simp [K.origin]

variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (U:Display E) (K:UnitCost)
theorem zeroth (p:ℕ) (x:E) : born U K 0 p 0 x=U 0 x := by
  simp only [born,Comparison.RG02.Moving.Path.motion,jet_zero,ages,cover,K.origin,zpow_zero,Complex.ofReal_one,one_mul,
    zero_mul,inv_one,one_smul,Complex.ofReal_zero]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ ne; simp [ne]
  · simp

theorem first (quiet:HasDerivAt K.rating 0 0) (p:ℕ) (live:0<p)
    (smooth:∀i≤p,Differentiable ℝ (U i)) (x:E) :
    born U K 0 p 1 x=U 1 x := by
  have inv:HasDerivAt (fun t=>(K.rating t)⁻¹) 0 0 := by convert! quiet.inv (by simp [K.origin]) using 1 ; simp [K.origin]
  have loc:HasDerivAt (fun t=>(K.rating t)⁻¹ • x) 0 0:=by simpa using inv.smul_const x
  have f0 (i:ℕ) (hi:i≤p) : HasDerivAt (fun t=>U i ((K.rating t)⁻¹ • x)) 0 0:=by
    convert! ((smooth i hi _).hasFDerivAt.comp_hasDerivAt 0 loc) using 1 ; simp
  have clk:HasDerivAt (fun t:ℝ=>((t*K.rating t:ℝ):ℂ)) 1 0:=by
    simpa [K.origin] using ((hasDerivAt_id (0:ℝ)).mul quiet).ofReal_comp
  have term (i:ℕ)(hi:i∈range (p+1)) :
      HasDerivAt (fun t=>(↑(t*K.rating t):ℂ)^i*U i ((K.rating t)⁻¹ • x))
        (if i=1 then U 1 x else 0) 0:=by
    have fi:=f0 i (by simpa [Nat.lt_succ_iff] using mem_range.mp hi)
    cases i with
    | zero=>simpa only [pow_zero,one_mul,zero_ne_one,if_false] using fi
    | succ i=>
      cases i with
      | zero=>convert! clk.mul fi using 1 <;> simp [K.origin] ; rfl
      | succ i=>convert! (clk.pow (i+2)).mul fi using 1 ; simp [K.origin]
  have price:HasDerivAt (fun t=>ages U 0 p t (K.rating t) x) (U 1 x) 0:=by
    simpa [ages,cover,Nat.lt_succ_iff.mpr live] using HasDerivAt.fun_sum term
  change Assembly.jet _ 1 1=U 1 x
  simpa [Assembly.jet,iteratedFDeriv_one_apply,fderiv_apply_one_eq_deriv] using price.deriv

end YM.Integration.WilsonThermometerOriginalClockSlope
