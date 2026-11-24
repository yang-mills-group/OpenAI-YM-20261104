import YM.Integration.WilsonThermometerUnitFilingStops

/-! Two filings of a true stored cylinder with one intact residual density
at capture. The residual is integrated with the original Wilson kernel. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCompensated
open Function Lattice RG Wilson Labels Source Work.G08 Next.Foundations Trace.Physical
open Trace.Physical.GermGraph RG16 RG16.Literal Bid Overlay MeasureTheory
open Extra.Histories MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingFeed (report)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C" => R.family
local notation "H" => R.family.path

theorem combine {N p b j:ℕ} (jb:j≤b) (A B:Config G ((C).side b p)→ℂ)
    (pa:Integrable A (prior G _)) (pb:Integrable B (prior G _)) :
    reading R (N:=N) (A+B) j jb=reading R (N:=N) A j jb+reading R (N:=N) B j jb := by
  have linear : gust H N p b (A+B) j jb=gust H N p b A j jb+gust H N p b B j jb := by
    induction jb using Nat.decreasingInduction with
    | self => simp only [gust_base]
    | of_succ j hj ih =>
      rw [gust_step H N p b (A+B) hj,gust_step H N p b A hj,gust_step H N p b B hj,ih]
      exact StepData.push_add ((H).levels.transition_mass ..) _ _
        (gust_live H N p b A pa hj) (gust_live H N p b B pb hj)
  unfold reading
  rw [linear,Pi.add_apply,mul_add]

include simple in
theorem original {N p u v b:ℕ} (cu:(C).ref 0≤u) (uv:u≤v) (vb:v≤b) (bN:b≤N)
    (ou:Opened C 0 u p) (ov:Opened C 0 v p)
    (Y:Cut C N p) (cont:Continuous Y) (bu:Booked C N p 0 Y u (uv.trans (vb.trans bN)))
    (bv:Booked C N p 0 Y v (vb.trans bN)) {A B:Config G ((C).side b p)→ℂ} {rem:ℝ}
    (stored:WilsonCenteredFiledAtoms.Store ((H).rep N p b) ((C).localSection 0) (C).params 0
      (safety C b) rem A) (whole:credit C N p 0 Y b bN=A+B) :
    ‖(report R Y u-report R Y v)-
      (reading R (N:=N) B u (uv.trans vb)-reading R (N:=N) B v vb)‖ ≤
      2*capital C b rem 1*Real.exp (-((H).S.scale b-(H).S.scale v)/8) := by
  have price:=WilsonThermometerUnitFilingStops.two_stops R simple cu uv vb bN ou ov stored
  obtain ⟨Q,fmt,paid,field⟩ := stored
  have pa : Integrable A (prior G _) := by
    rw [←funext field]
    exact message 0 N p b R.makes (cu.trans (uv.trans vb)) bN
      (show Trace.Physical.GermGraph.reads («C»:=R.family) 0 N p b Q rem from ⟨fmt,paid⟩)
  have pb : Integrable B (prior G _) := by
    have both := (credit_int C N p 0 Y cont bN).sub pa
    rwa [whole,add_sub_cancel_left] at both
  have hi:=WilsonThermometerUnitFilingCoarse.reported R simple bN (uv.trans vb) Y cont ou bu
  have hj:=WilsonThermometerUnitFilingCoarse.reported R simple bN vb Y cont ov bv
  rw [←hi,←hj,whole,combine R (uv.trans vb) A B pa pb,combine R vb A B pa pb]
  convert price using 2
  abel

end YM.Integration.WilsonThermometerUnitFilingCompensated
