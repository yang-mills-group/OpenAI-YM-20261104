import YM.Integration.WilsonVacuumPreResetDepositedLetters
import YM.Integration.OriginalFiniteWickReadout

/-! Conversion between the finite squarefree coupling register of the
original RG02 step and the real power series used by the periodic Wick step. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteRegister
open Function Finset Marker Multi Comparison.RG02 Order Cumulants PowerSeries
open WilsonCoeffUV.Blue
open scoped Classical BigOperators

variable {V:Type}[DecidableEq V][Fintype V](R:Census V)(r:ℕ)

def register:PowerSeries ℝ→+*Grade R r:=
  (Order.series R r).comp (PowerSeries.map ((Poly.bead R).comp Complex.ofRealHom))

theorem read (P:PowerSeries ℝ)(t:R.Mode)(u:Index r):
    (register R r P).part (Join.pair t u)=
      (u.val.card.factorial:ℂ)*(if t=R.quiet then ((coeff u.val.card P:ℝ):ℂ) else 0):=by
  rw [register,RingHom.comp_apply,Order.polarization,coeff_map,RingHom.comp_apply,Assembly.beads]
  rfl

private theorem scalar (a:ℝ):register R r (PowerSeries.C a)=(a:ℂ)•(1:Grade R r):=by
  have bead:Poly.bead R (a:ℂ)=(a:ℂ)•(1:Poly R):=by simpa using Poly.product_bead (1:Poly R) (a:ℂ)
  rw [register,RingHom.comp_apply,PowerSeries.map_C,RingHom.comp_apply,Order.series_C]
  change (Join.injectLeft R (indices r)) (Poly.bead R (a:ℂ)) = _
  rw [bead,map_smul,map_one]

theorem exponential (P:PowerSeries ℝ)(h:constantCoeff P=0):
    register R r (raiseE P)=Poly.pass (register R r P):=by
  let M:=Fintype.card (V⊕Fin r)
  let table:=∑j∈range (M+1),PowerSeries.C (coeff j (PowerSeries.exp ℝ))*P^j
  have terms (i:ℕ)(hi:i<M+1):coeff i (raiseE P)=coeff i table:=by
    rw [raises h]
    exact edit_coeff PowerSeries.C h (PowerSeries.exp ℝ) hi
  have common:register R r (raiseE P)=register R r table:=by
    apply Join.both_parts
    intro t u
    rw [read,read,terms u.val.card (by
      have hu:=Order.order_limit r u
      have hM:r≤M:=by simp [M]
      omega)]
  rw [common]
  unfold table Poly.pass
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul,map_pow,scalar,PowerSeries.coeff_exp]
  simp [one_div]

theorem heard (P:PowerSeries ℝ)(h:constantCoeff P=1)(x:Grade R r)
    (book:denominator x=register R r P):
    logVac x=register R r (logOf P):=by
  have zero:constantCoeff (logOf P)=0:=constantCoeff_logOf h
  have start:(register R r (logOf P)).part (Board R r).quiet=0:=by
    rw [←Join.pair_quiet,read]
    change ((0:ℕ).factorial:ℂ)*(if R.quiet=R.quiet then ((coeff 0 (logOf P):ℝ):ℂ) else 0)=0
    simp [coeff_zero_eq_constantCoeff_apply,zero]
  unfold logVac
  rw [book,←raising_log h,exponential R r _ zero,Cumulants.connected_pass start,raising_log h]

end YM.Integration.WilsonVacuumPreResetFiniteRegister
