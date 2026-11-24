import YM.Integration.WilsonCapturedPrimaryWindingPeek

/-! The exact original occupied census retains every input colour and its own
mark power. Each printed coefficient is read at its actual physical period. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingStockRead
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open QuadraticLocal.Earn.Scene AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density
open FVA1Physical.TwoReset AnalyticBridge.SectorAffine.Offset
open RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.FVAAlt2 RegulatorIR.Diagram
open Comparison.RG02.Adjacent
open WilsonIndependentCapturedAngularWinding WilsonEmittedFiledThermalGerm
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {A V:Type} [Fintype A] [DecidableEq V] {Γ:Census V}
variable {I X:A→Type} {P:A→Passport n V} (M:(a:A)→I a→Row (P a) Γ G (X a))
variable (grades:A→V→ℕ) (x:(a:A)→X a) (lag:A→ℕ) (s:Multi.Hot Γ)
variable (L:A→Layout G) (tape:A→Finset Age)

def printed (i:ℕ) (B:Stationary.Link G n) (a:A) : ℂ :=
  let pole:=Launch.index Γ (grades a) s.val+1
  if lag a+pole ≤ i then (peek dvd_rfl (M a) (grades a) (L a) (tape a) (x a) (i-lag a-pole) B).part s.val
  else 0

theorem original {Lab:Type} [DecidableEq Lab] {stock:Census Lab} (V₁ V₂:Bulk.Colors stock G n)
    (c₁ c₂:UnitCost) (u:Lab) {toll i:ℕ} (well₁:Bulk.Well V₁) (well₂:Bulk.Well V₂)
    (t₁:V₁.power (Booth.Arm.pub u)=toll) (t₂:V₂.power (Booth.Arm.pub u)=toll)
    (c:A→ℝ) (visible:∀B:Stationary.Link G n,
      (∑a,c a • printed M grades x lag s L tape i B a)=
        if toll ≤ i then WilsonEmittedFiledDeckFare.row c₁ V₁ u (i-toll) B-
          WilsonEmittedFiledDeckFare.row c₂ V₂ u (i-toll) B else 0) (v:Directions G n) :
    (∑a,c a • WilsonEmittedFiledGerm.price M grades x lag s L tape i v a)=
      Assembly.jet (field c₁ V₁ u-field c₂ V₂ u) i (1,Stationary.edgeColor.symm v) := by
  let B:=WilsonCubicOriginalTorus.coordinates G n v
  have same a: WilsonEmittedFiledGerm.price M grades x lag s L tape i v a =
      printed M grades x lag s L tape i B a := by
    dsimp only [WilsonEmittedFiledGerm.price,printed]
    split
    · rw [WilsonMeasuredOriginalPeriodWord.literal (M a) (grades a) (L a) (tape a) (x a) _ B]
    · rfl
  simp_rw [same]
  rw [visible B]
  have sv:=WilsonEmittedFiledMixedWindow.grading c₁ V₁ u well₁
  have sz:=WilsonEmittedFiledMixedWindow.grading c₂ V₂ u well₂
  rw [t₁] at sv
  rw [t₂] at sz
  by_cases reached:toll ≤ i
  · rw [if_pos reached]
    have hi:toll+(i-toll)=i:=by omega
    have left:=WilsonEmittedFiledThermalGerm.ray c₁ V₁ u well₁ (i-toll) B
    have right:=WilsonEmittedFiledThermalGerm.ray c₂ V₂ u well₂ (i-toll) B
    rw [t₁,hi] at left
    rw [t₂,hi] at right
    change _=Tensor.diagonal (Tensor.coeff (field c₁ V₁ u-field c₂ V₂ u) i 0) (1,B)
    simp only [Tensor.diagonal,Tensor.coeff,iteratedFDeriv_sub_apply (sv.smooth.of_le le_top)
      (sz.smooth.of_le le_top),smul_sub,_root_.sub_apply]
    exact (congrArg₂ Sub.sub left right).symm
  · rw [if_neg reached]
    simp [Assembly.jet,(sv.sub sz).vanish i (Nat.lt_of_not_ge reached)]

end YM.Integration.WilsonCapturedPrimaryWindingStockRead
