import YM.Integration.WilsonIndependentCollarOrbitalBasisPayment

/-! The flat canonical source actually used by the K-stencil has unit norm
at every own test horizon, including horizon zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarCanonicalProbe
open Finset Lattice QuadraticLocal QuadraticLocal.Earn Marker Multi WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider
open WilsonReceivedCanonicalSocketSeed (present sheet contact)
open WilsonIndependentCollarOrbitalPeg (ink page_cap)
open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonOriginalMixedBlockRows (room)
open scoped Classical BigOperators ContDiff

theorem cap {V:Type}(D:V→ℕ)(v:V) : ‖present D v‖=1 := by
  apply le_antisymm (page_cap (D v))
  have h:=registry (page (D v) (sheet (D v))) (contact (D v)) zeroC
  change ‖iteratedFDeriv ℝ 0 (fun _:E=>(1:ℝ)) (zeroC:E) (dot ∘ (Fin.elim0:Fin 0→Axis))‖ ≤ _ at h
  rw [iteratedFDeriv_zero_apply,norm_one] at h
  exact h

theorem original {I:Type}[Fintype I][DecidableEq I]{side:Side}{n:ℕ}{P:Passport side (Fin n)}
    (B:I→Binder P (Stock.census (Fin n)))(D:Fin n→ℕ)(x:Affinity.Wallet (room (Fin n)))
    (target:(Stock.census (Fin n)).Mode):
    (∑s:Finset I,‖wages B x target s‖ * ∏z∈s,‖ink (present D) (B z).mode.val‖) ≤
      (2:ℝ)^(Fintype.card I)*∏v∈target.val,‖(x v).val‖ := by
  have h:=WilsonIndependentCollarOrbitalDose.original B x (present D) target
  apply h.trans_eq
  congr 1
  exact prod_congr rfl fun v _=>by rw [cap D v,mul_one]

end YM.Integration.WilsonIndependentCollarCanonicalProbe
end
