import YM.Integration.WilsonThermometerUnitFilingMeasured
import YM.Integration.WilsonThermometerUnitFilingCoarse

/-! The reflected Wilson expectation and its fixed flat report for the
same literal microscopic source and the actual retained capture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatReflection
open Function Filter MeasureTheory Lattice Wilson RG Source Labels OPE Bid Cells Real Marker
open MergeProof Ribbons Accent ManyCopies RG16 RG16.Literal Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato Pert.Asymptotics WilsonThermometerUnitFilingFeed
open WilsonThermometerUnitFilingCoarse (reading)
open scoped Classical BigOperators
open private replica from YM.Integration.WilsonThermometerUnitFilingMeasured
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "C" => R.family

include simple in
theorem original {N p u b j:ℕ}(ub:u ≤ b)(bN:b<N)(jN:j ≤ N)
    (ou:Opened C 0 u p)(Y:Cut C N p)(hf:Continuous Y)(B:(C).label 0){a e:ℝ}
    (ret:WholeProductCapture.Retained C N b p 0 u R.makes ou ub bN Y B a)
    (inside:Interior ((center (C).S p jN 0).chamber 0) (Y-(C).O N p B 0))
    (root:(center (C).S p jN 0).rootTest ((C).beta N p) (Y-(C).O N p B 0) ≤ e):
    ‖(C).omega N p Y-reading R (N:=N) (credit C N p 0 Y b bN.le) u ub‖ ≤
      e+a/gainChart (C).path b u:=by
  have top:=ub.trans bN.le
  have raw:=replica R simple (ou.post.trans top) jN Y hf B e inside root
  have bound:=WilsonCapturedRetainedProjection.measured R 0 ou ub bN le_rfl ub ou Y B a ret
  rw [scalar_cost R simple ou top,Pi.sub_apply] at bound
  have back:((C).factory 0 N p).terminal.symm B=B:=
    (terminal R simple (ou.post.trans top) _).symm.trans (((C).factory 0 N p).terminal.apply_symm_apply B)
  have price:gainChart (C).path b u * ‖report R Y u-B 0‖ ≤ a:=by
    simp only [report,dif_pos (And.intro ou top),terminal R simple (ou.post.trans top)]
    simpa only [back] using bound
  have cost:‖report R Y u-B 0‖ ≤ a/gainChart (C).path b u:=
    (le_div_iff₀ (Real.exp_pos _)).mpr ((mul_comm ..).trans_le price)
  obtain ⟨_,_,_,_,traj,_⟩:=ret
  rw [WilsonThermometerUnitFilingCoarse.reported R simple bN.le ub Y hf ou (traj u le_rfl ub).2.2.1]
  exact (show ‖(C).omega N p Y-report R Y u‖ ≤ ‖(C).omega N p Y-B 0‖+‖report R Y u-B 0‖ by
    simpa only [dist_eq_norm,norm_sub_rev (B 0) (report R Y u)] using dist_triangle ((C).omega N p Y) (B 0) (report R Y u)).trans
    (add_le_add raw cost)

end YM.Integration.WilsonOriginalTwoFlatReflection
end
