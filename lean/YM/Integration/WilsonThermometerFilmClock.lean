import YM.Integration.WilsonThermometerOriginalClockSlope

/-! The radial feed of the native first chronological coefficient at a possibly moving clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerFilmClock
open Function Finset Filter Comparison.RG02 Comparison.RG02.Adjacent Comparison.RG02.Assembly
open Comparison.RG02.Moving
open scoped Classical Topology BigOperators

variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (U:Display E) (K:UnitCost)
theorem first (p:ℕ) (live:0<p) (smooth:∀ i ≤ p,Differentiable ℝ (U i)) (x:E) :
    born U K 0 p 1 x=U 1 x+(fderiv ℝ (U 0) x) ((-deriv K.rating 0) • x) := by
  have rated:HasDerivAt K.rating (deriv K.rating 0) 0:=(K.smooth.differentiableAt (by simp)).hasDerivAt
  have inv:HasDerivAt (fun t=>(K.rating t)⁻¹) (-deriv K.rating 0) 0:=by
    convert! rated.inv (by simp [K.origin]) using 1 ; simp [K.origin]
  have loc:=inv.smul_const x
  let drift:=(fderiv ℝ (U 0) x) ((-deriv K.rating 0) • x)
  have f0 (i:ℕ) (hi:i≤p) :
      HasDerivAt (fun t=>U i ((K.rating t)⁻¹ • x)) ((fderiv ℝ (U i) x) ((-deriv K.rating 0) • x)) 0:=by
    convert! ((smooth i hi _).hasFDerivAt.comp_hasDerivAt 0 loc) using 1
    simp [K.origin]
  have clk:HasDerivAt (fun t:ℝ=>((t*K.rating t:ℝ):ℂ)) 1 0:=by
    simpa [K.origin] using ((hasDerivAt_id (0:ℝ)).mul rated).ofReal_comp
  have term (i:ℕ)(hi:i∈range (p+1)) :
      HasDerivAt (fun t=>(↑(t*K.rating t):ℂ)^i*U i ((K.rating t)⁻¹ • x))
        ((if i=1 then U 1 x else 0)+(if i=0 then drift else 0)) 0:=by
    have fi:=f0 i (by simpa [Nat.lt_succ_iff] using mem_range.mp hi)
    cases i with
    | zero=>simpa [drift] using fi
    | succ i=>
      cases i with
      | zero=>convert! clk.mul fi using 1 <;> simp [K.origin] ; rfl
      | succ i=>convert! (clk.pow (i+2)).mul fi using 1 ; simp [K.origin]
  have price:HasDerivAt (fun t=>ages U 0 p t (K.rating t) x) (U 1 x+drift) 0:=by
    simpa [ages,cover,Finset.sum_add_distrib,Nat.lt_succ_iff.mpr live] using HasDerivAt.fun_sum term
  change Assembly.jet _ 1 1=U 1 x+drift
  simpa [Assembly.jet,iteratedFDeriv_one_apply,fderiv_apply_one_eq_deriv] using price.deriv

end YM.Integration.WilsonThermometerFilmClock
