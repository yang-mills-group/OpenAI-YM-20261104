import YM.Integration.WilsonVacuumPreResetCoin
import YM.Integration.WilsonVacuumPreResetTorusDepositJet

/-! Every term in the homogeneous angular support of an original Wilson row
receives the same signed kinetic multiplier. The finite grade convolution
is exactly the one used by the deposited group-field program. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetHomogeneousRows
open Lattice Wilson RG Gauge Pressure Precision Tree Stationary
open Function Finset PowerSeries AllOrder.Floe AllOrder.Floe.Step
open AllOrder AllOrder.Ker AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Ink.Money
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open PertExtension.Series
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetTorusGrade
open scoped BigOperators Classical

variable {G:Gauge}{n:Side}

private theorem balance (p:Cost)(unit:constantCoeff p=1){i a e r:ℕ}(same:a+e=i+r):
    (pace p)^i*((pace p)⁻¹)^a=(pace p)^e*((pace p)⁻¹)^r:=by
  let A:=pace p
  let B:=A⁻¹
  have inv (j:ℕ):B^j*A^j=1:=by
    rw [←mul_pow,PowerSeries.inv_mul_cancel A ((pace_cc unit).trans_ne one_ne_zero),one_pow]
  have ne:A≠0:=by intro h; have z:=pace_cc unit; change constantCoeff A=1 at z; rw [h,map_zero] at z; norm_num at z
  apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero a ne) (pow_ne_zero r ne))
  calc
    (A^i*B^a)*(A^a*A^r)=(B^a*A^a)*(A^i*A^r):=by ring
    _=A^(i+r):=by rw [inv,one_mul,pow_add]
    _=A^(e+a):=by rw [←same,Nat.add_comm a e]
    _=(B^r*A^r)*(A^e*A^a):=by rw [inv,one_mul,pow_add]
    _=(A^e*B^r)*(A^a*A^r):=by ring

theorem weighted (p:Cost)(unit:constantCoeff p=1)(P:PChart G n)(e r:ℕ)
    (support:∀ i a:ℕ,a+e≠i+r→P i a=0)(t:ℕ)(z:rule (Coarse G) n):
    evaluated (mix (pace p) P) t z =
      ∑ i∈range (t+1),Pace.ladder (((r:ℝ)-e)/2) (Tested.term (p-1)) (t-i)*
        evaluated P i z:=by
  let A:=pace p
  let W:=A^e*(A⁻¹)^r
  let c (i:ℕ):=coeff (t-i) W
  have finite (i:ℕ):FiniteGen (P i):=⟨i+r+1,fun a h=>support i a (by omega)⟩
  have priced:mix A P t=∑ i∈range (t+1),c i•P i:=by
    funext a
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i mem
    change coeff (t-i) (A^i*(A⁻¹)^a) • P i a = c i • P i a
    by_cases same:a+e=i+r
    · rw [balance p unit same]
    · rw [support i a same,smul_zero,smul_zero]
  have bounded (i:ℕ):FiniteGen (c i•P i):=
    ⟨i+r+1,fun a h=>by change c i•P i a=0;rw [support i a (by omega),smul_zero]⟩
  simp only [WilsonVacuumPreResetTorusGrade.evaluated,Blue.flash,coeff_mk]
  rw [priced,visible_sum (fun i _=>bounded i),map_sum]
  apply sum_congr rfl
  intro i hi
  rw [visible_μ (finite i),MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C,
    WilsonVacuumPreResetCoin.original p unit]

/-- A deposited prism has degree and angular support separated by its own
fixed Laurent lag at every coupling coefficient. -/
theorem deposited (p:Cost)(unit:constantCoeff p=1)(v:PrismA G)(t:ℕ)(z:rule (Coarse G) n):
    evaluated (mix (pace p) (Mosaic.surf v n)) t z=
      ∑ i∈range (t+1),coeff (t-i) (p*(pace p)^(v.grade-v.rise))*
        Haiku.Coat.trade v.grade v.cells i n z:=by
  have support (i a:ℕ)(h:a+v.grade≠i+(v.rise+2)):Mosaic.surf v n i a=0:=by
    unfold Mosaic.surf
    split
    · exact shine_dark (by omega)
    · rfl
  rw [weighted p unit _ v.grade (v.rise+2) support]
  simp_rw [WilsonVacuumPreResetCoin.deposited p unit v.rankA,
    WilsonVacuumPreResetTorusDepositJet.original]

end YM.Integration.WilsonVacuumPreResetHomogeneousRows
