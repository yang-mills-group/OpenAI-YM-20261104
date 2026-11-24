import YM.Integration.WilsonPhysicalStationMixedWickNamedGram
import YM.Integration.WilsonPhysicalStationMixedWickInverse

/-! A compact genuinely separated neighborhood and a generic original two-site
appointment on which the full reflected free lower bank stays in its positive chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickChamber
open Filter Finset Function Lattice RG Wilson Labels Source Cells Extraction Table Maxwell Maxwell.Free
open XSpace XSpace.Structure1 XSpace.Normalize PhysMS PhysicalNext.Repeat.Legato
open MS MS.Land MS.Menus MS.Theater Local.Physical Extra Extra.FD RG17 Table.Pairing Spec Climb
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt)
open WilsonPositionProgramPublicWickGram (nodes reading vertex)
open WilsonMeasuredPublicEntranceNativeLowerFrame (panel pivot)
open WilsonMeasuredPublicEntranceNativeLowerMoment (free ports)
open scoped BigOperators Classical Topology Matrix.Norms.Operator MeasureTheory
variable {G:Gauge}(R:Run G)(B:Deck G)(e:ℕ)(a:Axis)
local notation "I" => Glyph B e

theorem regular :ContinuousOn (fun y i j=>panel R B e a y i j) (conf 2):=by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  let d:=WilsonOriginalBlissMixedGram.grades e e
  let v:=ports R (pivot R B e a i) (named R B e j)
  exact ((Bel R.family.book).class_smooth (Bel R.family.book) (Maxwell.table_smooth R.family.labels)
    (fun k=>⟨d k,v k⟩)).continuousOn

theorem separated :pointsAt a∈conf 2:=by
  apply FD.couple_ok
  intro eq
  have bad:=congrArg norm ((WilsonPositionProgramPublicWickGram.apart a).symm.trans (sub_eq_zero.mpr eq.symm))
  simp [basis_norm] at bad

theorem original (δ:ℝ)(positive:0<δ):
    ∃K:Set (Points 2),IsCompact K ∧ K⊆conf 2 ∧ ∃ξ∈generic 2,K∈𝓝 ξ ∧
      ∀y∈K,‖(fun i j=>panel R B e a y i j)-reading a (nodes a) (id:I→I)‖≤δ:=by
  let x:=pointsAt a
  have hx:x∈conf 2:=separated a
  have localRead:=((regular R B e a).continuousAt ((conf_open 2).mem_nhds hx)).tendsto
  have inside:∀ᶠy in 𝓝 x,y∈conf 2 ∧ ‖(fun i j=>panel R B e a y i j)-reading a (nodes a) (id:I→I)‖≤δ:=by
    filter_upwards [(conf_open 2).mem_nhds hx,localRead.eventually (Metric.ball_mem_nhds _ positive)] with y safe near
    refine ⟨safe,?_⟩
    change dist (fun i j=>panel R B e a y i j) (fun i j=>panel R B e a x i j)<δ at near
    simpa only [x,dist_eq_norm,WilsonMeasuredPublicEntranceNativeLowerFrame.reflected] using near.le
  obtain ⟨w,wp,box⟩:=Metric.mem_nhds_iff.mp inside
  have dense:Dense (generic 2):=MeasureTheory.Measure.dense_of_ae (μ:=MeasureTheory.volume) (Extraction.almostGeneric 2)
  obtain ⟨ξ,gξ,hξ⟩:=dense.exists_mem_open (Metric.isOpen_ball (x:=x) (ε:=w/2))
    ⟨x,Metric.mem_ball_self (half_pos wp)⟩
  have safety:Metric.closedBall x (w/2)⊆Metric.ball x w:=Metric.closedBall_subset_ball (half_lt_self wp)
  refine ⟨_,isCompact_closedBall x (w/2),fun y h=>(box (safety h)).1,ξ,gξ,?_,fun y h=>(box (safety h)).2⟩
  exact mem_of_superset (Metric.isOpen_ball.mem_nhds hξ) Metric.ball_subset_closedBall

end YM.Integration.WilsonPhysicalStationMixedWickChamber
end
