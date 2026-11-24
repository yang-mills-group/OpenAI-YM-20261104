import YM.Integration.WilsonIndependentCollarOrbitalPeg
import YM.Integration.WilsonOriginalCensusFinitePortrait

/-! Read one native `Blue.paint` rank of the actual filed angular tensor at
the retained Wilson link. This uses the existing normalized tensor entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarAngularPeg
open Finset Lattice RG Stationary FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonOriginalRawQReversion (coordinates)
open WilsonReceivedDepositedOrbitalFixedMoments (reading)
open WilsonIndependentCollarOrbitalPeg (outer)
open scoped Classical BigOperators

def multiplier {G:Gauge}{s:Side}{r:ℕ}(Y:Stationary.Link G s)(z:Fin r→Site s×Hooks G) : ℂ :=
  Complex.ofReal (∏a,coordinates G s Y (z a))

theorem unit_cap {G:Gauge}{s:Side}{r:ℕ}(Y:Stationary.Link G s)(paid:‖Y‖≤1)(z:Fin r→Site s×Hooks G) :
    ‖multiplier Y z‖ ≤ 1 := by
  rw [multiplier,Complex.norm_real,norm_prod]
  exact Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun a _=> (norm_le_pi_norm Y (z a)).trans paid)

theorem physical {G:Gauge}{s:Side}{r:ℕ}{I:Type}[DecidableEq I](J:Finset I)
    (T:(Fin r→Site s×Hooks G)→Pen (fun _:I=>1) J)(Y:Stationary.Link G s) :
    (∑z,outer J (T z)*multiplier Y z)=Complex.ofReal
       (MvPolynomial.eval (coordinates G s Y) (paint r (fun z=>touch reading J (T z)))) := by
  simp only [Blue.toll,Complex.ofReal_sum,Complex.ofReal_mul,multiplier]
  rfl

theorem rank_zero {G:Gauge}{s:Side}(Y:Stationary.Link G s)(z:Fin 0→Site s×Hooks G) :
    multiplier Y z=1 := by simp [multiplier]

end YM.Integration.WilsonIndependentCollarAngularPeg
end
