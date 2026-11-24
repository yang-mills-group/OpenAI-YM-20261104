import YM.Integration.WilsonThermometerUnitFilingFeed
import YM.RG16.Unmasked.Merits
import YM.OPE.Strobe.Noon

/-! The normalized Wilson integral of a complete funded source is heard by
its own fixed-date scalar. The two prices are the original physical replica
bound and its measured currency on the same cutoff source. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingHearing
open Function Set MeasureTheory Lattice Wilson RG Source Labels OPE Bid Cells
open MergeProof Ribbons Accent ManyCopies RG16 RG16.Literal Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFeed
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple)

include simple in
private theorem constant_field {N p : ℕ} (live : R.family.ref 0≤N) (v : R.family.label 0) :
    R.family.O N p v 0=v 0 • (1:Cut R.family N p) := by
  let F := R.family.labels.level 0
  obtain ⟨z,eq⟩ := RG12.unit_spans simple R.family 0 (R.family.ref 0) (by decide) v
  rw [eq,(R.family.linearO N p 0 0).map_smul]
  have un := R.family.constant R.makes 0 (p:=p) live 0
  change R.family.O N p (unitVec F R.family.path (R.family.ref 0)) 0=1 at un
  rw [un]
  simp [unitVec,Labels.Frame.e0]

include simple in
/-- Applied to the same capture receipt for the complete signed source, this
identifies its true, unselected finite Wilson expectation at the fixed date.
No inserted face is divided by an auxiliary conditional gas. -/
theorem original {N p b t J : ℕ} (jt : J≤t) (tb : t≤b) (bN : b≤N)
    (ot : Opened R.family 0 t p) (Y : Cut R.family N p) (hf : Continuous Y)
    (B : R.family.label 0) (q : store R.family 0 p b) {E dR w : ℝ}
    (fund : Funds R.family R.makes p N b 0 J t E dR w Y jt tb bN ot B q) :
    ‖R.family.omega N p Y-report R Y t‖ ≤ 2*(stakes R.family J t/w)+E/gainChart R.family.path b t := by
  let T := center R.family.S p (jt.trans (tb.trans bN)) 0
  let X := Y - R.family.O N p B 0
  have pack : ‖R.family.omega N p X‖ ≤ 2*(stakes R.family J t/w) :=
    (OPE.Strobe.atone (Q:=X) T (R.family.beta N p) (seamless R.makes N p) fund.inview).trans fund.packing
  have hX : X=Y-B 0 • (1:Cut R.family N p) := by
    rw [show X=Y-R.family.O N p B 0 by rfl,constant_field R simple (ot.post.trans (tb.trans bN))]
  have mean : R.family.omega N p X = R.family.omega N p Y-B 0 := by
    unfold Family.omega moment
    rw [hX]
    simp only [Pi.one_def,Pi.sub_apply]
    rw [integral_sub]
    · simp [probReal_univ]
    · exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact integrable_const _
  have idB : (R.family.factory 0 N p).terminal.symm B=B :=
    (terminal R simple (ot.post.trans (tb.trans bN)) _).symm.trans
      ((R.family.factory 0 N p).terminal.apply_symm_apply B)
  let f := topReport R.family N p 0 R.makes t ot (tb.trans bN) Y
  have cur := fund.currency
  rw [scalar_cost R simple ot (tb.trans bN),Pi.sub_apply,idB] at cur
  have filed : report R Y t=f 0 := by
    simp only [report,dif_pos (And.intro ot (tb.trans bN)),terminal R simple (ot.post.trans (tb.trans bN))]
    rfl
  rw [mean] at pack
  rw [filed]
  have tri : ‖R.family.omega N p Y - f 0‖ ≤ ‖R.family.omega N p Y-B 0‖+‖f 0-B 0‖ := by
    simpa only [dist_eq_norm,norm_sub_rev (B 0) (f 0)] using dist_triangle (R.family.omega N p Y) (B 0) (f 0)
  exact tri.trans (add_le_add pack cur)

end YM.Integration.WilsonThermometerUnitFilingHearing
