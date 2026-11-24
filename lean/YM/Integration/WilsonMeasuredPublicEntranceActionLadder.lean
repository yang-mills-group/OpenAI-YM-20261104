import YM.Integration.WilsonMeasuredPublicEntranceActionInvariant
import YM.TraceExtension.Atlas.Horns
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Basis

/-! The signed Wilson action has its original six-plane raw coordinates on the
chosen native ladder. Its vacuum coefficient is recovered from the true mean. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceActionLadder
open Function Filter Set Extraction Climb Next.UVStress Table Work.A01 Maxwell UVNext.FreeStress Spin
open Spec Trace Trace.Over Trace.Terrace Trace.Pilot TraceExtension MergeProof.East Next.Rank
open Further.CorrectedLift Push.CutoffProjectors
open scoped Classical
variable {G:Gauge}{C:Family G}
set_option maxRecDepth 6000 in
set_option maxHeartbeats 1200000 in
theorem filed (simple:G.Simple)(H:(Bel C.book).Hierarchy)
    (real:(Bel C.book).conj H.spin 4 (stepField C)=stepField C)
    (signed:∀s,(Bel C.book).mirror H.spin 4 s (stepField C)=stepField C):
    ladder C 4 (stepField C)=(C.labels.level 4).coords (Trace.square4 G):=by
  let x:=stepField C
  let B:=C.labels.level 4
  let y:=ladder C 4 x
  have bar:star y=y:=by
    have move:=ladder_conj H.spin x
    rw [show (Bel C.book).conj H.spin 4 x=x from real] at move
    exact move.symm
  have spin(s:Signed):B.act s.ortho y=y:=by
    have move:=ladder_spin H.spin s x
    rw [show (Bel C.book).mirror H.spin 4 s x=x from signed s] at move
    exact move.symm
  obtain ⟨u,a,shape⟩:=WilsonMeasuredPublicEntranceActionInvariant.coordinates simple B y (fun i=>congrFun bar i) spin
  let project:=((Bel C.book).project 4).restrictScalars ℝ
  have physical:x=u • (Bel C.book).unit 4+a • x:=by
    calc
      x = project y := (ladder_reads x).symm
      _ = project (u • B.e0+a • B.coords (Trace.square4 G)) := congrArg project shape
      _ = u • project B.e0+a • project (B.coords (Trace.square4 G)) := (project.map_add _ _).trans
        (congrArg₂ (· + ·) (project.map_smul _ _) (project.map_smul _ _))
      _ = u • (Bel C.book).unit 4+a • x := by
        have eu:project B.e0=(Bel C.book).unit 4:=by
          rw [show B.e0=ladder C 4 ((Bel C.book).unit 4) from (ladder_unit C 4).symm]
          exact ladder_reads _
        rw [eu]
        rfl
  let mean:=((expectation (Bel C.book) 4).restrictScalars ℝ)
  have h:=congrArg mean physical
  rw [map_add,map_smul,map_smul,show mean x=0 from sceneV H,
    show mean ((Bel C.book).unit 4)=1 from mean_unit H.laws,smul_zero,add_zero] at h
  have hu:u=0:=by simpa [Complex.real_smul] using h.symm
  rw [hu,zero_smul,zero_add] at shape physical
  have hx:x≠0:=scale_alive simple H
  have off:(a-1) • x=0:=by rw [sub_smul,one_smul,←physical,sub_self]
  have ha:a=1:=sub_eq_zero.mp ((smul_eq_zero.mp off).resolve_right hx)
  rw [ha,one_smul] at shape
  exact shape
theorem original {f:Extraction.Order}{S:Table C.book}(F:Final C f S)(simple:G.Simple)
    {H:(Bel C.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{J:Scaling S}{V:∀i,Vane C i}{Z:Arch C}
    (cause:Scribe f J V Z F.sector l F.room.kernel H):
    ladder C 4 (stepField C)=(C.labels.level 4).coords (Trace.square4 G):=by
  obtain ⟨real,turns_⟩:=legitimacy F simple cause
  apply filed simple H real
  intro s
  rw [←(baseRights (C:=C) (H:=H) simple).signed]
  exact turns_ s.ortho
end YM.Integration.WilsonMeasuredPublicEntranceActionLadder
