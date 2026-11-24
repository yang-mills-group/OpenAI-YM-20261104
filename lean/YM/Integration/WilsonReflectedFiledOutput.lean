import YM.Integration.WilsonReflectedMicroscopicSites

/-! A complete original replicated cylinder has a single filed counterterm
at the older date. Its physical copy estimate and the filed coefficient
come from the same original cluster, including all earlier primary feeds. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReflectedFiledOutput
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Marker Extra.Multi PhysicalNext.Repeat.Legato MergeProof Accent
open Bid Bandage Cells Stock RG16.Literal Trace.Physical.GermGraph GridApprox
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple) {N p b J u h:ℕ}
include simple
theorem original (ot:Opened R.family h u p) (tiling:Stock.Tabs.opens R.family.path.levels 1 J u)
    (ub : u ≤ b) (bN : b < N) (room:GridApprox.room R.family.path.levels J b (lensScope R.family h))
    (Y : Cut R.family N p) (cont : Continuous Y)
    (inside:Interior ((center R.family.S p (tiling.1.trans (ub.trans bN.le)) 0).chamber 0) Y)
    (basis:∀B:R.family.label h,
      Interior ((center R.family.S p (tiling.1.trans (ub.trans bN.le)) 0).chamber 0) (R.family.O N p B 0))
    (q:store R.family h p b) {dR M E w:ℝ}
    (paid:reads h N p b q dR) (size:(R.family.labels.level h).coeffSize q.x+dR ≤ M) (pos:0 < M)
    (fund:4*(1+(R.family.path.levels.params b).columns)*M ≤ E) (wpos:0 < w)
    (roomW:32*(1+(R.family.path.levels.params b).columns)*w*‖alto R.family.path u h‖*
      (E/gainChart R.family.path b u) ≤ fly R.alloy.B.a h u/2)
    (whole:Fleet R.family N p h b J Y (tiling.1.trans (ub.trans bN.le))
      (march (fun _:Site (R.family.side J p)=>w) (near R.alloy.B.a) u b) q bN.le) :
    ∃ Z:R.family.label h,Funds R.family R.makes p N b h J u E dR w Y tiling.1 ub bN.le ot Z q :=by
  have back:=R.again simple
  have readout:=Fleet.keeps R.family N p h b J R.makes Y cont (tiling.1.trans ub) bN.le _ q paid whole
  obtain ⟨Z,cap,physical,A,x,tracked,price,eq⟩:=MergeProof.root_bequest R.family N b u p h R.makes w
    back.1.scrim back.1.tabs J tiling Y q ot.post (hk:=ub) bN room basis cont inside paid.1 paid.2
    size pos fund wpos roomW whole
  obtain ⟨works,currency⟩:=RG16.Literal.align R.family N p h b u A R.makes ot ub bN.le tracked Y cont Z
    (eq.trans (congr_arg₂ (·+·) readout.symm rfl)) (price u le_rfl ub)
  exact ⟨Z,paid,cap,whole,readout,Next.UVStress.minus inside (basis Z),works,physical,currency⟩
end YM.Integration.WilsonReflectedFiledOutput
