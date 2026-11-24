import YM.Integration.WilsonOriginalCountableMarkedSheet
import YM.Integration.WilsonMixedFreshMergerCrown

/-! The source, its occupied hard stock, and its original source addresses are returned together. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCollaredMarkedSheet
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.Corrected QuadraticLocal
open QuadraticLocal.Affinity Hard Kiosk Canopy Ovens
open WilsonRootedKioskOccupiedSlip
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V I:Type}[DecidableEq V] [Fintype V] [Countable I]
  {o:V→Site n}{R:Census V}{w:V→ℝ} {films:V→Type}
  [∀v,AddCommGroup (films v)] [∀v,Module ℝ (films v)]
  (actors:∀v,Set (films v)) (pieces:∀v,Submodule ℝ (films v)) (lands:V→Support n)

theorem original (P:Rep G n) (L:Lamps (Wallet actors) I G P.p o R) {hard bill shrink:ℝ}
    (file:Taut lands actors pieces L)
    (receipt:Hard.Install P.activities P.p hard (Willow.haloSlack P.p.B))
    (hw:∀v,0<w v) (one:1 ≤ shrink) (earned:Gross L w P.p.B (P.p.supportExponent+1) bill)
    (enough:shrink⁻¹*bill ≤ Willow.haloSlack P.p.B) :
    ∃ H:Hard (Wallet actors) P.p P.activities.forced P.activities.K o R,
      Crown lands actors pieces H ∧ H.Paid (fun v=>w v/shrink) P.p.B P.p.supportExponent hard ∧
      ∀t U,(⟨L,H⟩:Gallery (Wallet actors) I o P R).density t U=(↑(P.eval U):ℂ) • Poly.pass (bare L t U) := by
  obtain ⟨old,fee,⟨merger⟩,rent⟩:=receipt.room
  let H:=Hard.rent (α:=Wallet actors) (o:=o) (R:=R) rent
  have quiet:Crown lands actors pieces H:=by
    constructor
    intro i U
    refine Stencil.const (Poly.bead R (↑(old.K i U):ℂ)) ?_
    intro s hs
    exact (Poly.part_send ..).trans (if_neg hs)
  refine ⟨Kiosk.Second.canopy H (sheet L.shade) merger,?_,
    WilsonOriginalCountableMarkedSheet.at_merger P L merger rent hw one earned enough⟩
  exact Crown.second H merger (sheet L.shade) quiet
    (WilsonMixedFreshMergerCrown.enrolled actors pieces lands L file)

end YM.Integration.WilsonOriginalCollaredMarkedSheet
