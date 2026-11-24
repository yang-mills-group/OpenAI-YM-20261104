import YM.Integration.WilsonOlderFreshReversionGross
import YM.Integration.WilsonOlderSignedOneMarkMasks

/-! The full unmasked kinetic balance is an admissible charged scalar on the old Wilson vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshReversionStore
open Function Finset Lattice RG Wilson Marker Ac Push.Local QuadraticLocal Source Labels
open Planned.GuardedAtom Extra.Trajectories WilsonCenteredFiledAtoms Comparison.RG02.Cumulants
open WilsonCenteredLampCapture WilsonCenteredMountedCapture WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Countable ι]
  {P : Rep G n} {o : V→Site n} {c : Census V} {d : ℕ} {F : Frame G d}

def price (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (Z : Support n) (rad : ℕ)
    (μ η κ radius small full : ℝ) :=
  let fee := stage p rad ({()}:Finset Unit)*(Real.exp ((p.supportExponent+2)*coverNumber p.B Z)*(radius⁻¹*small))
  cartage p Y S μ η κ fee 0 + WilsonOlderSignedOneMarkMasks.fare p Z η radius full κ

theorem original (L : Lamps X ι G P.p o c) (x : X) (s : c.Mode) (v : V) (member : v∈s.val)
    (w : V→ℝ) (hw : ∀ i,0<w i) {small full : ℝ}
    (wage : L.Paid w P.p.B (P.p.supportExponent+2) small)
    (gross : Gross L w P.p.B (P.p.supportExponent+2) full)
    (y : Site n) (Z : Support n) (root : y∈Z) (seat : o v∈Z) (rad : ℕ) (near : separation (o v) y≤rad)
    (K : Guard.Keeper P.p P.activities) {σ C Λ δ η κ μ : ℝ} (law : P.Lawful σ C Λ δ η)
    (div : 0<κ) (room : hitWidth P.p*η≤1) (hη : 0≤η) (S : SectionData F) (Y : Hol G)
    (read : Readable Y S P.p n μ) :
    Store P S Y y κ (price P.p S Y Z rad μ η κ (Poly.toll w s) small full)
      (fun U=>(P.eval U:ℂ)*(bare L x U).part s) := by
  have no : ForceCost P.p P.activities (0 : ℕ → Config G n → ℂ) (κ*0) := by
    rw [mul_zero]
    exact ⟨fun _=>0,Extra.Histories.budget0 _ _,by simp⟩
  have blank : ForceFormat P.p P.activities y 0 :=
    ⟨by simp,by simp,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
  have reg:=single L x s v member w hw wage y Z root seat rad near 1 K law div room hη S Y read 0 blank no
  have hot:=WilsonOlderSignedOneMarkMasks.original L s v member w hw gross x Z y root seat K div hη room
    law.labels.boundK law.labels.forced S Y
  obtain ⟨A,format,bill,present⟩:=sub law reg hot
  refine ⟨A,format,?_,fun U=>?_⟩
  · simpa only [price,norm_one,one_mul] using bill
  rw [present]
  simp only [Pi.sub_apply,map_zero,tsum_zero,mul_zero,add_zero,one_mul]
  ring

end YM.Integration.WilsonOlderFreshReversionStore
