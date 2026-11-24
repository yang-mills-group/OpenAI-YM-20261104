import YM.Integration.WilsonSeparatedOriginalSlabFiledFilm
import YM.Integration.WilsonPositionSeparatedProfileUnitJet
import YM.Integration.WilsonPositionSeparatedProfileFlatReadout

/-! Actual original reading of a filed physical source. The degree-zero page is its normalized signed response at the flat field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabMeasuredProxy
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open ProjectorNext.Equivariance RG16.Literal Trace.Physical.GermGraph Extra.Histories.Relay WilsonLimitConstruction PhysicalNext
open MergeProof.Ribbons.ManyCopies.Cadet.Studio.ZeroDegree
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}(R:Run G){u N per:ℕ}
set_option quotPrecheck false
local notation "C"=>R.family
local notation "A"=>(C).path
local notation "Y"=>(C).path.rep N per u

theorem graded (h:ℕ)(door:Opened C h u per)(live:u≤N)(f:Cut C N per)(paid:Booked C N per h f u live):
    ∃(q:store C h per u)(e:ℝ),reads h N per u q e ∧ credit C N per h f u live=q.density 0 ((C).localSection h) Y ∧
      fitting h N per u R.makes door live (topReport C N per h R.makes u door live f)=
        Trace.Physical.Germ.projection ((C).labels.level h) (C).params (Y).p.threshold 0 q:=by
  obtain ⟨q,e,format,source⟩:=paid
  refine ⟨q,e,format,source,?_⟩
  calc _=readPage C N per h f u live:=(fitting («C»:=R.family) h N per u R.makes door live).apply_symm_apply _
       _=page h per u q:=readPage_eq C N per h f R.makes live door.post q format source
       _=_:=by
         apply congrArg (fun θ:ℝ=>Trace.Physical.Germ.projection ((C).labels.level h) (C).params θ 0 q)
         exact congrArg (fun pars=>pars.threshold) (R.makes.wilson.represents N per u live).vac.symm

theorem unit (door:Opened C 0 u per)(live:u≤N)(f:Cut C N per)(paid:Booked C N per 0 f u live):
    (fitting 0 N per u R.makes door live (topReport C N per 0 R.makes u door live f)) 0=
      credit C N per 0 f u live 1/((Y).eval 1:ℂ):=by
  obtain ⟨q,e,format,source,seen⟩:=graded R 0 door live f paid
  have fit:=WilsonPositionSeparatedProfileUnitJet.projection ((C).labels.level 0) (C).params Y 0 q format.1
  rw [seen,fit,source]
  have empty:RG.flags (Y).p.threshold (1:Config G ((C).side u per))=∅:=(offFlags _ (Y).p.threshold_pos).self_of_nhds
  apply (eq_div_iff (noFlagEval (R:=Y) empty)).mpr
  exact (mul_comm (q.x 0) ((Y).eval 1:ℂ)).trans (WilsonPositionSeparatedProfileFlatField.vacuum ((C).localSection 0) (R.makes.sections 0) Y 0 q format.1).symm

end YM.Integration.WilsonSeparatedOriginalSlabMeasuredProxy
