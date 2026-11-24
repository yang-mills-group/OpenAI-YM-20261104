import YM.Integration.WilsonCapturedPrimaryWindingColoredPeg
import YM.Integration.WilsonCapturedPrimaryWindingStockRead
import YM.Integration.WilsonMeasuredWindingCensusReturn

/-! The actual occupied Wilson word is tested once. Both real channels of
each enrolled counterterm enter before the finite engineering coefficient. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingColoredCatalogue
open Function Finset Tensor Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.RG02.Adjacent Comparison.Density
open RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.FVAAlt2 RegulatorIR.Diagram
open WilsonEmittedWordJointFare WilsonEmittedCutGrouping WilsonEmittedFiledCatalogue
open WilsonIndependentCapturedAngularWinding WilsonEmittedFiledThermalGerm
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {A V : Type} [Fintype A] [DecidableEq V]
variable {I X : A→Type} {Γ : Census V} {P : A→Passport n V}
variable (M : (a:A)→I a→Row (P a) Γ G (X a)) (w:A→V→ℝ) (grades:A→V→ℕ)
variable (x:(a:A)→X a) (c:A→ℝ) (ℓ:A→ℕ)
variable (B:BudgetPoint) {σ b α K θ:A→ℝ} {p pieces depth:A→ℕ} {g:ℝ}
variable (old:∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope:∀a,Invoice.Supports B (K a) (α a) g (σ a) (θ a))
variable (s:Multi.Hot Γ) (layout:A→Layout G) (tapes:A→Finset Age)
variable {L:Type} [DecidableEq L] {C:Census L}
local notation "full" => (fun z:Chart G n=>words M x c ℓ (fun a=>picked (M a) s.val) z.1 (increment 1 z.2))
local notation "board" => WilsonEmittedFiledMixedWindow.joint G n


open WilsonEmittedFiledDeckFare WilsonEmittedAngularJointFare
local notation "radial" d:max a:max => WilsonCapturedPrimaryWindingStockRead.printed M grades x ℓ s layout tapes d a
local notation "keys₀" => WilsonEmittedRootedJetWage.Slot G n
local notation "peg" => WilsonEmittedRootedJetWage.peg G n
local notation "I₀" => SiteSlot G n

include old scope in
theorem seen (d:ℕ) (a:Stationary.Link G n):
    Assembly.jet full d (1,Stationary.edgeColor a)=∑v,c v • (radial d a) v:=by
  rw [WilsonEmittedFiledGerm.heard M w grades x c ℓ B old scope s layout tapes]
  apply sum_congr rfl
  intro v _
  apply congrArg (fun z:ℂ=>c v • z)
  dsimp only [WilsonEmittedFiledGerm.price,WilsonCapturedPrimaryWindingStockRead.printed]
  split
  · rw [WilsonMeasuredOriginalPeriodWord.literal]
    change (Air.discharge _ _ (Stationary.arm G n 1 (Stationary.edgeColor.symm (Stationary.edgeColor a)))).part s.val=_
    rw [ContinuousLinearEquiv.symm_apply_apply]
  · rfl

include old scope in
theorem original (u:L)(left right:UnitCost)(V₁ V₂:Bool→Bulk.Colors C G n)
    (bank₁ bank₂:Bool→Orders (I₀)) {cap pole J:ℕ}(room:J≤cap+pole+1)
    (issue₁:∀k,Booth.Arm.Single left (V₁ k) (bank₁ k) u cap pole)
    (issue₂:∀k,Booth.Arm.Single right (V₂ k) (bank₂ k) u cap pole)
    (print:∀d<J,∀a:Stationary.Link G n,(∑v,c v • (radial d a) v)=
      if pole≤d then
        (row left (V₁ false) u (d-pole) a-row right (V₂ false) u (d-pole) a)+
        (row left (V₁ true) u (d-pole) a-row right (V₂ true) u (d-pole) a)*Complex.I else 0)
    {fee:ℝ}(positive:0≤fee)
    (sale:∀k e,e+pole<J → ((e+pole).factorial:ℝ)*mass
      (fun r x=>(((bank₁ k) e r x-(bank₂ k) e r x:ℝ):ℂ)) (e+pole)≤fee/2):
    ∀d<J,∑i:Fin d → (keys₀),‖iteratedFDeriv ℝ d full 0 (peg∘i)‖≤fee:=by
  let analytic:=WilsonEmittedFiledGerm.smooth M w grades x c ℓ B old scope s layout tapes
  intro d hd
  by_cases enough:pole≤d
  · let e:=d-pole
    have total:e+pole=d:=by dsimp [e];omega
    have live:e+pole<J:=total.symm ▸ hd
    have named:=WilsonCapturedPrimaryWindingColoredPeg.two full u left right V₁ V₂ bank₁ bank₂
      (show e≤cap by omega) issue₁ issue₂ (analytic.of_le le_top) (by
        intro a
        rw [seen M w grades x c ℓ B old scope s layout tapes,print _ live a,if_pos (Nat.le_add_left pole e),Nat.add_sub_cancel])
    rw [←total]
    apply named.trans
    dsimp only
    rw [mul_add]
    linarith [sale false e live,sale true e live]
  · have zero:=WilsonCapturedPrimaryWindingColoredPeg.census full d (analytic.of_le le_top)
      (fun _ _=>0) (by
        intro a
        rw [seen M w grades x c ℓ B old scope s layout tapes,print d hd a,if_neg enough]
        simp [held])
    simpa only [mass,norm_zero,sum_const_zero,mul_zero] using zero.trans (by simpa [mass] using positive)

end YM.Integration.WilsonCapturedPrimaryWindingColoredCatalogue

