import YM.Integration.WilsonPhysicalChiralNonfreeCurvatureTest

/-! The physical reference of the signed station is the precise issued
Maxwell polynomial on every constant-shell tensor, including the unit. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalChiralNonfreeCartanAnchor
open Finset RG Labels Wilson Source Lattice Next.Rank Next.Rank.Price Next.Rank.Atlas
open Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot
open WilsonPositionThermometerGradedSource Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame
open Maxwell XSpace XSpace.Normalize Maxwell.Free ProjectorNext.Calibration
open WilsonPhysicalChiralNonfreeCurvatureTest Tensor Analysis
open scoped Classical BigOperators Topology
variable {G:Gauge}

theorem named (C:Family G)(s:Rose.Badge)(i:Fin 3):
    reduceEq (((C.labels.level (grade i)).coords.symm (ladder C (grade i) (source C s i))).val)=
    (if i∈s then base G i else leaf G (grade i)).val:=by
  have h:=Further.CorrectedLift.ladder_reads (C:=C) (source C s i)
  calc
    _ = (Maxwell.Free.fields C.labels (grade i) ((Cells.standard C).project (grade i)
         (ladder C (grade i) (source C s i)))).val:=rfl
    _ = (Maxwell.Free.fields C.labels (grade i) (source C s i)).val:=by rw [h]
    _ = _:=by rw [WilsonPositionThermometerGradedSource.source,LinearEquiv.apply_symm_apply]

theorem shell (P:Labels.Taylor G 0):∃X:Maxwell.Shell G 0,Maxwell.gaugeJet X=P:=by
  let U:=Maxwell.potential P
  have legal:U.val∈Maxwell.onShell G.Color 0:=by
    refine ⟨U.property,?_⟩
    intro b x
    apply sum_eq_zero
    intro j _
    have eqn:diagonal (U.val j b)=fun _ : E4=>U.val j b (fun _=>0):=by
      funext a; exact congrArg (U.val j b) (Subsingleton.elim ..)
    rw [eqn]
    simp [Maxwell.grad,D]
  exact ⟨⟨U.val,legal⟩,Maxwell.potential.symm_apply_apply P⟩

theorem tower (P:Labels.Taylor G 0):∃X:Maxwell.TaylorTower G,
    (fun j=>Maxwell.gaugeJet (X j))=PositionX.Tri.chunk P:=by
  obtain ⟨x,h⟩:=shell P
  refine ⟨Pi.single 0 x,?_⟩
  funext j
  rcases eq_or_ne j 0 with rfl|hj
  · simpa only [PositionX.Tri.chunk,Pi.single_eq_same] using h
  · rw [Pi.single_eq_of_ne hj,PositionX.Tri.chunk,Pi.single_eq_of_ne hj,map_zero]

theorem physical (C:Family G)(s:Rose.Badge)(i:Fin 3)(P:Labels.Taylor G 0):
    ∃X:Maxwell.TaylorTower G,(fun j=>Maxwell.gaugeJet (X j))=PositionX.Tri.chunk P ∧
    Labels.read (PositionX.Tri.chunk P) (((C.labels.level (grade i)).coords.symm
      (ladder C (grade i) (source C s i))).val) =
      Maxwell.probe X (if i∈s then base G i else leaf G (grade i)).val:=by
  obtain ⟨X,h⟩:=tower P
  refine ⟨X,h,?_⟩
  rw [←h,←Maxwell.jet_value,named C s i]

end YM.Integration.WilsonPhysicalChiralNonfreeCartanAnchor
