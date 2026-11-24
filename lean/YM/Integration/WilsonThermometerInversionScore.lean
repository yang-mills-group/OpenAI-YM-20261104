import YM.Integration.WilsonThermometerInversionFiling

/-! First nonzero interacting inversion coefficient one grade above an
actual placed word's angular pole. The Jacobian and the negative cubic
Wilson variation are kept with the same zero-order socket and Hessian. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerInversionScore
open Function Finset Filter MeasureTheory Lattice Wilson Gauge Precision
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Radial
open PertExtension.Series.Tested PertExtension.Orb PowerSeries
open scoped Classical BigOperators ContDiff Topology
private theorem next (a b : ℕ→ℝ) (w:ℕ) (h:∀i<w,a i=0) :
    conv a b (w+1) = a (w+1)*b 0+a w*b 1 := by
  rw [conv,term,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,sum_range_succ,sum_range_succ]
  simp only [coeff_mk]
  have hz : ∑ i∈range w,a i*b (w+1-i)=0 :=
    sum_eq_zero (fun i hi=>by rw [h i (mem_range.mp hi),zero_mul])
  rw [hz]
  simp [add_comm (a w*b 1)]

variable {G:Gauge} {n:Side} {P:ChartRatio G} (price:LocalRatio P)
    {O:Observable G n} (valid:LocalTest O) {w:ℕ}
    (order:RadialOrder w (O ∘ expLinks G (Cotree n)))
local notation "A" => O ∘ expLinks G (Cotree n)
local notation "J" => jacobian P (U:=Cotree n)
local notation "Q" => accountingWith P O

include order price valid
private theorem accounted (u:Dir G n) : jet (Q) (w+1) u =
    jet (J) 0 u*jet (A) (w+1) u + jet (J) 1 u*jet (A) w u := by
  let j := fun i=>jet (J) i u
  let a := fun i=>jet (A) i u
  have joint := (directions (chart_integrand price valid) u).unique
    ((directions (Chart.Ratio.jacobian_smooth price (U:=Cotree n) |>.of_le le_top) u).prod
      (directions valid.germ u))
  have h := congrFun joint (w+1)
  have zero (i:ℕ)(hi:i<w) : a i=0 := by dsimp [a];rw [jets_vanish valid.germ order hi];rfl
  have e : conv j a=conv a j := congrArg (fun p:PowerSeries ℝ=>term p) (mul_comm (PowerSeries.mk j) (PowerSeries.mk a))
  change jet (Q) (w+1) u=conv j a (w+1) at h
  rw [h,e,next _ _ w zero]
  dsimp [a,j]
  ring

private theorem integrand (u:Dir G n) :
    integrandSeries fiscal (Q) (w+1) u =
      jacobian P (U:=Cotree n) 0*jet (A) (w+1) u +
      (jet (J) 1 u - jacobian P (U:=Cotree n) 0*jet fiscal 3 u)*jet (A) w u := by
  let a := fun i=>jet (Q) i u
  let b := fun i=>expsum (layers fiscal) i i u
  have eq : integrandSeries fiscal (Q) (w+1) u=conv a b (w+1) := by
    simp only [integrandSeries,Zone.mul,conv,term,coeff_mul,coeff_mk]
    rfl
  have zero (i:ℕ)(hi:i<w) : a i=0 := by
    rw [show a i=jet (Q) i u from rfl,entering_jets price valid order i hi.le,if_neg hi.ne]
  rw [eq,next _ _ _ zero]
  have h0:b 0=1:=by norm_num [b,expsum,Zone.TaylorPow,sum_range_succ]
  have h1:b 1= -jet fiscal 3 u:=by
    norm_num only [b,expsum,Radial.layers,sum_range_succ,sum_range_zero,Zone.TaylorPow,
      Zone.mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,if_true,if_false,
      zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero,Nat.factorial,Nat.reduceSub,Nat.reduceAdd,neg_add_cancel]
  rw [h0,h1,show a w=jet (Q) w u from rfl,entering_jets price valid order w le_rfl,
    if_pos rfl,show a (w+1)=jet (Q) (w+1) u from rfl,accounted price valid order]
  simp only [jet_zero]
  ring

theorem slope (ev:Even n.val) : diagonalWith P O (w+1) =
    (∫ u,(jacobian P (U:=Cotree n) 0*jet (A) (w+1) u +
      (jet (J) 1 u-jacobian P (U:=Cotree n) 0*jet fiscal 3 u)*jet (A) w u)*
      kernel fiscal u ∂tangent G (Cotree n)) / rowsWith P (n:=n) 1 0 := by
  apply (eq_div_iff (pivot ev price).ne').mpr
  have p:=congrFun (rows_with_head price ev O) (w+1)
  rw [next _ _ w (diag_down price valid order ev),rowsWith_odd _ (by decide : Odd 1),
    mul_zero,add_zero] at p
  rw [p]
  unfold rowsWith Radial.moment normTerm
  simp_rw [integrand price valid order]

end YM.Integration.WilsonThermometerInversionScore
