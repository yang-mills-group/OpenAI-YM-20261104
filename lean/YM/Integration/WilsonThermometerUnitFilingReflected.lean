import YM.Integration.WilsonThermometerUnitFilingHearing
import YM.OPE.Cards.Literal

/-! The original replicated settlement pays subtraction of the actual
fixed-date horizon-zero scalar on the same chamber. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingReflected
open Function Set MeasureTheory Lattice Wilson RG Source Labels OPE Bid Cells
open MergeProof Ribbons Accent ManyCopies RG16 RG16.Literal Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFeed OPE.Cards
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
theorem original {N p b u J:ℕ} (ju:J≤u) (ub:u≤b) (bN:b≤N)
    (door:Opened R.family 0 u p) (Y:Cut R.family N p) (B:R.family.label 0)
    (q:store R.family 0 p b) {E dR w:ℝ}
    (fund:Funds R.family R.makes p N b 0 J u E dR w Y ju ub bN door B q) :
    PaidAt R.family.S N p J (R.family.beta N p)
      (2*(stakes R.family J u/w)+E/gainChart R.family.path b u)
      (Y-report R Y u • (1:Cut R.family N p)) := by
  let T:=center R.family.S p (ju.trans (ub.trans bN)) 0
  let X:=Y-R.family.O N p B 0
  let c:=B 0-report R Y u
  have cB:=constant_field R simple (p:=p) (door.post.trans (ub.trans bN)) B
  have refile:Y-report R Y u • (1:Cut R.family N p)=X+c • 1:=by
    funext U;dsimp only [X,c];rw [cB];simp [Pi.sub_apply,Pi.smul_apply]
  have hx:Interior (T.chamber 0) X:=fund.inview
  have hc:Interior (T.chamber 0) (c • (1:Cut R.family N p)):=
    (show Interior (T.chamber 0) (1:Cut R.family N p) from Interior.constant ..).scale _
  have idB : (R.family.factory 0 N p).terminal.symm B=B :=
    (terminal R simple (door.post.trans (ub.trans bN)) _).symm.trans
      ((R.family.factory 0 N p).terminal.apply_symm_apply B)
  have cur:=fund.currency
  rw [scalar_cost R simple door (ub.trans bN),Pi.sub_apply,idB] at cur
  have fc:‖c‖≤E/gainChart R.family.path b u:=by
    dsimp only [c];rw [norm_sub_rev]
    simpa only [report,dif_pos (And.intro door (ub.trans bN)),terminal R simple (door.post.trans (ub.trans bN))] using cur
  rw [refile]
  refine ⟨ju.trans (ub.trans bN),hx.plus hc,((seamless R.makes N p).semi T _ _ hx hc).trans ?_⟩
  apply add_le_add fund.packing
  change T.rootTest (R.family.beta N p) (c • (1:Cut R.family N p)) ≤ E/gainChart R.family.path b u
  rw [Next.UVStress.root_smul T (R.family.beta N p) c (1:Cut R.family N p),Cells.Tiling.root_one,mul_one]
  exact fc

end YM.Integration.WilsonThermometerUnitFilingReflected
