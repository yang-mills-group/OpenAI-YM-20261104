import YM.Integration.WilsonThermometerUnitFilingCoarse

/-! The fixed physical filing date and the shorter perturbative stopping date
of one capture. Both readings include the entire original older Wilson law. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonThermometerUnitFilingStops
open Function Filter Lattice RG Wilson Labels Source Work.G08 Next.Foundations
open Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal Bid
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent
open Extra.Trajectories Extra.Multi Overlay MeasureTheory Cells
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFeed (report)
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "C" => R.family
local notation "H" => R.family.path

private theorem rem_nonneg {n : Side} {F : Frame G 0} {P : Rep G n} {S : SectionData F}
    {Y : Hol G} {y : Site n} {κ amount : ℝ} {A : Config G n→ℂ}
    (stored : WilsonCenteredFiledAtoms.Store P S Y y κ amount A) : 0 ≤ amount := by
  obtain ⟨_,_,⟨_,_,ha,hb,total,_⟩,_⟩ := stored
  exact (add_nonneg ha hb).trans total

include simple in
theorem two_stops {N p u v b : ℕ} (cu : (C).ref 0≤u) (uv : u≤v) (vb : v≤b) (bN : b≤N)
    (ou : Opened C 0 u p) (ov : Opened C 0 v p) {rem : ℝ}
    {A : Config G ((C).side b p)→ℂ} (stored : WilsonCenteredFiledAtoms.Store ((H).rep N p b)
      ((C).localSection 0) (C).params 0 (safety C b) rem A) :
    ‖reading R (N:=N) A u (uv.trans vb)-reading R (N:=N) A v vb‖ ≤
      2*capital C b rem 1*Real.exp (-((H).S.scale b-(H).S.scale v)/8) := by
  obtain ⟨c,price⟩ := WilsonThermometerUnitFilingCoarse.stored R simple cu (uv.trans vb) bN stored
  have pu := price u le_rfl (uv.trans vb) ou
  have pv := price v uv vb ov
  have mono : gainChart H b v ≤ gainChart H b u := by
    apply Real.exp_le_exp.mpr
    have scales : Monotone (C).S.scale := monotone_nat_of_le_succ fun j => by
      rw [Schedule.scale_succ]; exact le_add_of_nonneg_right (Real.log_nonneg
        (by exact_mod_cast ((C).S.block j).pos))
    have h := scales uv
    linarith
  have r0 := rem_nonneg stored
  have cap0 : 0≤capital C b rem 1 := by
    have cols := ((H).levels.params b).columns_ge
    dsimp only [capital];exact mul_nonneg (by linarith) (by linarith)
  have vu : capital C b rem 1/gainChart H b u ≤ capital C b rem 1/gainChart H b v :=
    div_le_div_of_nonneg_left cap0 (Real.exp_pos _) mono
  calc
    _ ≤ ‖reading R (N:=N) A u (uv.trans vb)-c‖+‖reading R (N:=N) A v vb-c‖ := by
      simpa only [dist_eq_norm,norm_sub_rev c (reading R (N:=N) A v vb)] using
        dist_triangle (reading R (N:=N) A u (uv.trans vb)) c (reading R (N:=N) A v vb)
    _ ≤ capital C b rem 1/gainChart H b v + capital C b rem 1/gainChart H b v := add_le_add (pu.trans vu) pv
    _ = 2*(capital C b rem 1/gainChart H b v) := by ring
    _ = _ := by rw [gainChart,div_eq_mul_inv,←Real.exp_neg]; ring_nf

include simple in
theorem original {N p u v b : ℕ} (cu : (C).ref 0≤u) (uv : u≤v) (vb : v≤b) (bN : b≤N)
    (ou : Opened C 0 u p) (ov : Opened C 0 v p) (Y : Cut C N p) (cont : Continuous Y)
    {rem : ℝ} (stored : WilsonCenteredFiledAtoms.Store ((H).rep N p b) ((C).localSection 0)
      (C).params 0 (safety C b) rem (credit C N p 0 Y b bN)) :
    ‖report R Y u-report R Y v‖ ≤
      2*capital C b rem 1*Real.exp (-((H).S.scale b-(H).S.scale v)/8) := by
  have price := two_stops R simple cu uv vb bN ou ov stored
  have r0 := rem_nonneg stored
  obtain ⟨Q,fmt,paid,source⟩ := stored
  let t := rem+((C).labels.level 0).coeffSize Q.x
  have amt : 0≤((C).labels.level 0).coeffSize Q.x := Finset.sum_nonneg fun _ _=>norm_nonneg _
  have funds : Q.remBound 0 ((H).rep N p b) (safety C b) t := by
    obtain ⟨a,b',ha,hb,ab,hκ,rest⟩ := paid
    exact ⟨a,b',ha,hb,ab.trans (le_add_of_nonneg_right amt),hκ,rest⟩
  have room : ((C).labels.level 0).coeffSize Q.x ≤ t := le_add_of_nonneg_left r0
  obtain ⟨_,_,kept⟩ := WilsonMacroscopicRichEnrolledFiling.original C N b u p 0 R.makes
    (R.again simple).1.scrim Y cont Q t 1 one_pos cu (uv.trans vb) bN fmt funds room
    (funext source).symm
  rw [WilsonThermometerUnitFilingCoarse.reported R simple bN (uv.trans vb) Y cont ou
    (kept u le_rfl (uv.trans vb) ou).1,
    WilsonThermometerUnitFilingCoarse.reported R simple bN vb Y cont ov (kept v uv vb ov).1] at price
  exact price

end YM.Integration.WilsonThermometerUnitFilingStops
