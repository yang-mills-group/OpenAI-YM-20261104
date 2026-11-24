import YM.Integration.WilsonNeutralTwoPrintPathSlit
import YM.Integration.WilsonNeutralTwoPrintPathPlaced

/-! A complete separately rendered angular polynomial, rebased from the elected compact support to the held field. Signs and the numerical complex source dose are taken before extracting individual mixed angular entries. -/
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathPolynomial
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open AllOrder AllOrder.Floe Exterior Comparison.RG02 Comparison.RG02.Adjacent Multi
open FVA1Physical FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead
open WilsonNeutralTwoPrintPeg WilsonCoeffUV WilsonCoeffUV.Blue FormalBulk08
open scoped Classical BigOperators

open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel
open WilsonNeutralTwoPrintPathJet WilsonNeutralTwoPrintPathSlit
open WilsonOriginalPrimerReceipts
variable {I:Type}[Fintype I]

theorem rendered (T:Ranked I)(cap:ℕ)(B:I→ℝ):
    MvPolynomial.eval B (packed T cap)=∑r∈range (cap+1),∑z:Fin r→I,T r z*∏j,B (z j):=by
  simp [packed,render,word]

theorem placed (T:Ranked I)(cap:ℕ)(B:I→ℝ)(shift:I≃I):
    diagonal cap T (B ∘shift)=MvPolynomial.eval B (packed (fun r z=>T r (shift.symm ∘ z)) cap):=by
  rw [rendered]
  unfold diagonal
  apply sum_congr rfl
  intro r _
  change MvPolynomial.eval (B ∘ shift) (∑z:Fin r→I,T r z • ∏j,MvPolynomial.X (z j))=_
  simp only [MvPolynomial.smul_eq_C_mul,map_sum,map_mul,MvPolynomial.eval_C,map_prod,MvPolynomial.eval_X]
  have eqn:=Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl (Fin r)) shift)
    (fun z=>T r (shift.symm ∘ z)*∏j,B (z j))
  apply Eq.trans _ eqn
  apply sum_congr rfl
  intro z _
  change T r z*∏j,B (shift (z j))=T r (fun j=>shift.symm (shift (z j)))*∏j,B (shift (z j))
  simp

theorem phase_weight (p:Bool)(a:ℂ)(x:ℝ):phase p (a*(x:ℂ))=phase p a*x:=by
  cases p <;> simp [phase,Complex.mul_re,Complex.mul_im]

variable {Z:Type}[NormedAddCommGroup Z][NormedSpace ℝ Z](test:Z→L[ℝ]ℝ)
theorem compared (a:ℂ)(τ η:I≃I)(high low:∀r:ℕ,(Fin r→I)→Z)(cap:ℕ)(p:Bool)(B:I→ℝ):
    phase p (a*(diagonal cap (fun r z=>test (high r (τ ∘ z))) (B∘η):ℝ))-
    phase p (a*(diagonal cap (fun r z=>test (low r (τ ∘ z))) (B∘η):ℝ))=
      MvPolynomial.eval B (packed
        (fun r z=>phase p (a*(test (high r (τ ∘ η.symm ∘ z)-low r (τ ∘ η.symm ∘ z)):ℝ))) cap):=by
  rw [phase_weight,phase_weight,placed,placed,rendered,rendered,rendered,←mul_sub,←sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro r _
  rw [←sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro z _
  rw [phase_weight,map_sub]
  ring

end YM.Integration.WilsonNeutralTwoPrintPathPolynomial
end
