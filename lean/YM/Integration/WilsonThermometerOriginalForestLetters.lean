import YM.Integration.WilsonThermometerReceivedPupilJets
import YM.Integration.ActualJointJetContact

/-! The measured two-date source's first two entire field jets in the lower forest chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalForestLetters
open Function MeasureTheory Lattice RG Tree Wilson Exterior Precision Marker Multi Comparison.RG02
open Comparison.RG02.Assembly Comparison.RG02.Valence FVA1Physical.Wilson FVA1Physical.TwoReset
open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Earn AllOrder.Floe
open scoped Classical BigOperators ContDiff

variable {G:Gauge} {c f:Side} {V:Type} [DecidableEq V] {R:Census V}

/-- Agreement on the full angular panel persists after the nonlinear chart of the nominated forest. -/
theorem common (X Y:Bulk.Colors R G f) (s:Multi.Hot R) (same:X.power s=Y.power s)
    (gx:GradeAt (X.power s) (Bulk.projected (X.mark s))) (gy:GradeAt (X.power s) (Bulk.projected (Y.mark s)))
    (panel:∀ d ≤ 1,∀y,(Air.discharge X d y).part s.val=(Air.discharge Y d y).part s.val)
    (S:StepData c f) (F:Forest S.ratio) (j:ℕ) (hj:j≤1) (u:Bulk.Joint S F (G:=G)) :
    jet (Bulk.markFn S F X s) (X.power s+j) u=jet (Bulk.markFn S F Y s) (Y.power s+j) u := by
  have pg:=ActualJointJetContact.grade_sub_of_shifted_slices _ _ (X.power s) 1 gx gy (by
    intro d hd y
    simpa only [Air.discharge,Multi.part_lit,←same] using panel d hd y)
  let D (t:ℝ) (U:Config G f):=X.mark s t U-Y.mark s t U
  have joint:=Bulk.joint_receipt S F (z:=D) pg
  rw [←same]
  exact ActualJointJetContact.jet_eq_of_grade_sub _ _ (Bulk.joint_receipt S F gx).smooth
    (Bulk.joint_receipt S F gy).smooth joint (by omega) u

theorem copied {ι α:Type} {n:Side} {J:Passport n V} (mult:n.val∣f.val) (M:ι→Row J R G α)
    (w:V→ℕ) (L:Layout G) (T:Finset Age) (v:α) (p depth:ℕ) (live:0<p) (q:Pace.Coin)
    (a:ℝ) (earned:Pace.Earn q a) (value:ℕ→Stationary.Link G f→Poly R)
    (agree:∀d≤p,∀y,value d y=peek mult M w L T v d y) (quiet:ℝ → Config G f → ℝ)
    (S:StepData c f) (F:Forest S.ratio) (s:Multi.Hot R) (j:ℕ) (hj:j≤1) (u:Bulk.Joint S F (G:=G)) :
    let pupil:=copyColor mult M w (fun i=>(M i).paint v) L T
    let power (b:Multi.Hot R):=Launch.index R w b.val+1
    let K:=(Rebirth.caliber q earned.1).back depth
    let X:=WilsonOriginalCoverJetColors.colors quiet power p (WilsonOriginalCoverJetColors.reset p value K)
    let Y:=WilsonOriginalCoverJetColors.colors quiet power p (fun b d y=>(Air.discharge pupil d y).part b.val)
    jet (Bulk.markFn S F X s) (power s+j) u=jet (Bulk.markFn S F Y s) (power s+j) u := by
  let pupil:=copyColor mult M w (fun i=>(M i).paint v) L T
  let power (b:Multi.Hot R):=Launch.index R w b.val+1
  let K:=(Rebirth.caliber q earned.1).back depth
  let old (b:Multi.Hot R) (d:ℕ) (y:fieldDir G f 1):=(Air.discharge pupil d y).part b.val
  let X:=WilsonOriginalCoverJetColors.colors quiet power p (WilsonOriginalCoverJetColors.reset p value K)
  let Y:=WilsonOriginalCoverJetColors.colors quiet power p old
  have boundOld (b:Multi.Hot R) (d:ℕ) (_:d≤p):Level ((power b+d:ℕ):ℤ) (old b d):=
    WilsonThermometerOriginalPupilDegree.coefficient pupil d b
  have boundNew:=WilsonThermometerOriginalPupilDegree.restamped mult M w L T v p K value agree
  apply common X Y s rfl (WilsonOriginalCoverJetColors.grade quiet power p _ boundNew s)
    (WilsonOriginalCoverJetColors.grade quiet power p old boundOld s) _ S F j hj u
  intro d hd y
  have paid:=WilsonThermometerOriginalPupilDegree.rendered mult M w L T v p K value agree quiet s d (hd.trans live) y
  have literal:=WilsonOriginalCoverJetColors.angular quiet power p old boundOld d (hd.trans live) y
  have filed:=WilsonThermometerOriginalDepositedSlope.table mult M w L T v p depth live q a earned value agree s y
  obtain rfl|rfl : d=0 ∨ d=1 := by omega
  · rw [paid.2]; rw [show WilsonOriginalCoverJetColors.reset p value K s 0 y=_ from filed.1,
      agree 0 (Nat.zero_le _)]; simpa [X,Y,old,pupil,peek,Multi.part_lit] using congrArg (fun z:Poly R=>z.part s.val) literal.symm
  · rw [paid.2]; rw [show WilsonOriginalCoverJetColors.reset p value K s 1 y=_ from filed.2,
      agree 1 live]; simpa [X,Y,old,pupil,peek,Multi.part_lit] using congrArg (fun z:Poly R=>z.part s.val) literal.symm

end YM.Integration.WilsonThermometerOriginalForestLetters
