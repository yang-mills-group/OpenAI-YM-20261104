import YM.Integration.WilsonNeutralTwoPrintPathMass
import YM.Integration.WilsonNeutralTwoPrintPathRankFare

/-! Total angular winding bill of the two deposited real pupils on their true finite board. The formal field, complexDosed test, scalar complexDose and actual coordinate translation are the same in the signed observation and in its invoiced mixed rows. -/
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathSlit
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
abbrev Bond (H:Gauge)(m:Side):=Site m × Loc H 1


variable {Z I₀:Type}[NormedAddCommGroup Z][NormedSpace ℝ Z][CompleteSpace Z]
  {J:Finset I₀}{y:I₀ → Cover}
variable (cap:ℕ)(addresses:(Bond G n) ≃ (Bond G n))(complexDose:ℂ)(paidLabel:Z →L[ℝ] ℝ)
variable (finite:(r:ℕ) → Ten Z (Bond G n) r)(lifted:(r:ℕ) → Ten Z (Cloth (Loc G 1)) r)

def rows (r:ℕ)(z:Fin r → (Bond G n)):ℂ:=
  complexDose*((paidLabel (finite r (addresses ∘ z)-plume (lifted r) n (addresses ∘ z)):ℝ):ℂ)

theorem allowance {α W:ℝ}(pin:J.Nonempty)(room:4*crestCard y J<n.val)(hα:0<α)(r:ℕ)
    (paid:MarkU y J (finite r) (lifted r) α W):
    ∑z,‖rows addresses complexDose paidLabel finite lifted r z‖≤
      (‖complexDose‖*‖paidLabel‖)*(WilsonNeutralTwoPrintPathRankFare.tariff (Loc G 1) r α W*catchW (α/512) n):=by
  calc
    _ ≤∑z:Fin r → (Bond G n),(‖complexDose‖*‖paidLabel‖)*‖finite r (addresses ∘ z)-plume (lifted r) n (addresses ∘ z)‖:=by
      apply sum_le_sum
      intro z _
      rw [rows,norm_mul,Complex.norm_real,mul_assoc]
      exact mul_le_mul_of_nonneg_left (paidLabel.le_opNorm _) (norm_nonneg _)
    _ ≤ _:=by
      rw [←mul_sum]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      have reorder:=Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl (Fin r)) addresses)
        (fun z=>‖finite r z-plume (lifted r) n z‖)
      change (∑z,‖finite r (addresses ∘ z)-plume (lifted r) n (addresses ∘ z)‖)=_ at reorder
      rw [reorder]
      exact WilsonNeutralTwoPrintPathRankFare.original pin room hα paid

include stock positive proper v in
theorem original (e:ℕ)(pin:J.Nonempty)(room:4*crestCard y J<n.val)(α W:ℕ→ℝ)
    (hα:∀r,r≤cap → 0<α r)(winding:∀r,r≤cap → MarkU y J (finite r) (lifted r) (α r) (W r))
    (read:∀p B,phase p ((peek dvd_rfl (M false) (grades false) (layout false) (tape false) (x false) e B).part s.val)-phase p ((peek dvd_rfl (M true) (grades true) (layout true) (tape true) (x true) e B).part s.val)=MvPolynomial.eval B
       (packed (fun r z=>phase p (rows addresses complexDose paidLabel finite lifted r z)) cap)):
    (cap.factorial:ℝ)*WilsonEmittedAngularJointFare.mass
        (WilsonNeutralTwoPrintAccount.entry M x grades s layout tape e) cap ≤
      (cap.factorial:ℝ)*(‖complexDose‖*‖paidLabel‖)*∑r∈range (cap+1),
        WilsonNeutralTwoPrintPathRankFare.tariff (Loc G 1) r (α r) (W r)*catchW (α r/512) n:=by
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply (WilsonNeutralTwoPrintPathMass.original M x grades s layout tape stock positive proper v
     e cap _ read).trans
  rw [mul_sum]
  apply sum_le_sum
  intro r hr
  have rc:r≤cap:=by simpa only [mem_range,Nat.lt_succ_iff] using hr
  exact allowance addresses complexDose paidLabel finite lifted pin room (hα r rc) r (winding r rc)

end YM.Integration.WilsonNeutralTwoPrintPathSlit
end
