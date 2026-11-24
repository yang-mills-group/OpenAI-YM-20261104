import YM.Integration.WilsonNeutralTwoPrintPathPolynomial

/-! Two independent physical pupils on one true finite board. Their observations are kept separate through evaluation at the original source centre, held-field centre and signed scalar, then charged as one finite winding difference. -/
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathHeldRead
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open AllOrder AllOrder.Floe Exterior Comparison.RG02 Comparison.RG02.Adjacent Multi
open FVA1Physical FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead
open WilsonNeutralTwoPrintPeg WilsonCoeffUV WilsonCoeffUV.Blue FormalBulk08
open scoped Classical BigOperators

open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel
variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{C:Census V}
  {I X:Bool→Type}{P:Bool→Passport n V}
  (M:(a:Bool)→I a→Row (P a) C G (X a))(x:(a:Bool)→X a)(grades:Bool→V→ℕ)(s:Hot C)
  (layout:Bool→Layout G)(tape:Bool→Finset Age)
  {w:Bool→V→ℝ}{σ cost:Bool→ℝ}{order seats shelf:Bool→ℕ}
  (stock:∀a,Scene.Armada (M a) (w a) (grades a) (σ a) (cost a) (order a) (seats a) (shelf a))
  (positive:∀a,0<σ a)(proper:∀a,Legal (tape a) (layout a))(v:s.val.val)
open WilsonNeutralTwoPrintPathSlit (Bond)
open WilsonNeutralTwoPrintPathJet (diagonal)
variable {Z I₀:Type}[NormedAddCommGroup Z][NormedSpace ℝ Z][CompleteSpace Z]
  {J:Finset I₀}{y:I₀ → Cover}
variable (cap:ℕ)(source held:Bond G n≃Bond G n)(amount:ℂ)(test:Z →L[ℝ] ℝ)
variable (finite:(r:ℕ) → Ten Z (Bond G n) r)(cover:(r:ℕ) → Ten Z (Cloth (Loc G 1)) r)

include stock positive proper v in
theorem original (e:ℕ)(pin:J.Nonempty)(room:4*crestCard y J<n.val)(α W:ℕ→ℝ)
    (σpaid:∀r,r≤cap → 0<α r)(wound:∀r,r≤cap → MarkU y J (finite r) (cover r) (α r) (W r))
    (upper:∀B,(peek dvd_rfl (M false) (grades false) (layout false) (tape false) (x false) e B).part s.val=
      amount*(diagonal cap (fun r z=>test (finite r (source ∘z))) (B ∘held):ℝ))
    (lower:∀B,(peek dvd_rfl (M true) (grades true) (layout true) (tape true) (x true) e B).part s.val=
      amount*(diagonal cap (fun r z=>test (plume (cover r) n (source ∘z))) (B ∘held):ℝ)):
    (cap.factorial:ℝ)*WilsonEmittedAngularJointFare.mass
      (WilsonNeutralTwoPrintAccount.entry M x grades s layout tape e) cap ≤
        (cap.factorial:ℝ)*(‖amount‖*‖test‖)*∑r∈range (cap+1),
        WilsonNeutralTwoPrintPathRankFare.tariff (Loc G 1) r (α r) (W r)*catchW (α r/512) n:=by
  apply WilsonNeutralTwoPrintPathSlit.original M x grades s layout tape stock positive proper v
    cap (held.symm.trans source) amount test finite cover e pin room α W σpaid wound
  intro p B
  rw [upper,lower]
  exact WilsonNeutralTwoPrintPathPolynomial.compared test amount source held finite (fun r=>plume (cover r) n) cap p B

end YM.Integration.WilsonNeutralTwoPrintPathHeldRead
end
