import YM.Integration.WilsonThermometerUnitFilingPhysicalStops
import YM.Integration.WilsonThermometerUnitFilingSharp
import YM.Integration.WilsonThermometerUnitFilingDeposit

/-! The unit filing of the physical compact cylinder, at every authentic
independent fine placement. Only the signed expenses on the original hard
addresses remain with the older joint law. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingShape
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels FVA1 Marker Bid Work.G08
open Table Spec XSpace XSpace.Rose Cells Climb Next.UVStress RG12 RG17 PhysicalNext.Repeat.Legato
open RG16 RG16.Literal Trace.Physical.GermGraph MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato.Bandage
open Primitives.GCC.Anchor WilsonPositionThermometerCapStation WilsonThermometerCourseIntake
open WilsonThermometerUnitFilingCylinder (Sites cylinder source)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFeed (report)
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open private rem_nonneg from YM.Integration.WilsonThermometerUnitFilingStops
open private admitted from YM.Integration.WilsonThermometerUnitFilingDeposit
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C" => R.family
local notation "H" => R.family.path
local notation "F" => R.family.labels.level 0
local notation "T" => R.family.localSection 0
local notation "J!" => Stock.census (Fin 3)
include simple in
private theorem decay {N p u v b : ℕ} (cu : (C).ref 0≤u) (uv : u≤v) (vb : v≤b) (bN : b≤N)
    (ou : Opened C 0 u p) (ov : Opened C 0 v p) {rem : ℝ} (η : ℝ) (ηpos : 0<η)
    {A : Config G ((C).side b p)→ℂ} (stored : WilsonCenteredFiledAtoms.Store ((H).rep N p b)
      ((C).localSection 0) (C).params 0 (safety C b) rem A) :
    ‖reading R (N:=N) A u (uv.trans vb)-reading R (N:=N) A v vb‖ ≤
      2*capital C b rem η*Real.exp (-((H).S.scale b-(H).S.scale v)/8) := by
  obtain ⟨c,price⟩ := WilsonThermometerUnitFilingSharp.stored R simple cu (uv.trans vb) bN η ηpos stored
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
  have cap0 : 0≤capital C b rem η := by
    have cols := ((H).levels.params b).columns_ge
    dsimp only [capital];exact mul_nonneg (by linarith) (by linarith)
  have vu : capital C b rem η/gainChart H b u ≤ capital C b rem η/gainChart H b v :=
    div_le_div_of_nonneg_left cap0 (Real.exp_pos _) mono
  calc
    _ ≤ ‖reading R (N:=N) A u (uv.trans vb)-c‖+‖reading R (N:=N) A v vb-c‖ := by
      simpa only [dist_eq_norm,norm_sub_rev c (reading R (N:=N) A v vb)] using
        dist_triangle (reading R (N:=N) A u (uv.trans vb)) c (reading R (N:=N) A v vb)
    _ ≤ capital C b rem η/gainChart H b v + capital C b rem η/gainChart H b v := add_le_add (pu.trans vu) pv
    _ = 2*(capital C b rem η/gainChart H b v) := by ring
    _ = _ := by rw [gainChart,div_eq_mul_inv,←Real.exp_neg]; ring_nf


variable (A:Group R.family 6) (z:UVIndex) (r:ℝ) (φ:Test 3) (Q:Sites R z→Poly J!)
local notation "w!" => WilsonSeparatedOriginalThermometerCells.weight φ
  (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z)
local notation "cut!" y:max => source R A z y (Q y)

private def value (y:Sites R z) (j:ℕ) (live:j≤z.1) : ℂ :=
  (((H).rep z.1 z.2 j).eval (1:Config G ((C).side j z.2)):ℂ)⁻¹ *
    credit C z.1 z.2 0 (cut! y) j live 1

include simple in
private theorem filed {j:ℕ} (live:j≤z.1) (door:Opened C 0 j z.2)
    (book:Booked C z.1 z.2 0 (cylinder R A z r φ Q) j live) :
    report R (cylinder R A z r φ Q) j=∑y,w! y*value R A z Q y j live := by
  rw [WilsonThermometerUnitFilingCourse.filed R simple _ door live book]
  unfold WilsonThermometerUnitFilingCylinder.cylinder
  rw [IntrinsicProductLinearity.credit_sum C z.1 z.2 0 j live _ _ (fun y=>admitted R A z y (Q y)),
    Finset.sum_apply,Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _=>by simp only [value,Pi.smul_apply,smul_eq_mul];ring

include simple in
theorem original {u v b:ℕ} (ref:(C).ref 0≤u) (uv:u≤v) (vb:v≤b) (bN:b≤z.1)
    (ou:Opened C 0 u z.2) (ov:Opened C 0 v z.2)
    (bu:Booked C z.1 z.2 0 (cylinder R A z r φ Q) u (uv.trans (vb.trans bN)))
    (bv:Booked C z.1 z.2 0 (cylinder R A z r φ Q) v (vb.trans bN))
    (Ψ:Sites R z→RG.Rep G ((C).side b z.2))
    (q:Sites R z → Coefficient F ((C).side b z.2)) (rem η:ℝ) (rpos:0≤rem) (ηpos:0<η)
    (live:∀y,w! y≠0→let q0:=WilsonPhysicalMarkedDefect.RegularProjection.soft (q y)
      q0.Format 0 (C).params ((H).rep z.1 z.2 b) ∧
      q0.remBound 0 ((H).rep z.1 z.2 b) (safety C b) rem ∧
      credit C z.1 z.2 0 (cut! y) b bN=
        q0.density 0 T ((H).rep z.1 z.2 b)+WilsonMeasuredCoefficientTransport.account (q y) (Ψ y)) :
    let Y:=cylinder R A z r φ Q
    let force (y:Sites R z):=WilsonMeasuredCoefficientTransport.account (q y) (Ψ y)
    ‖(report R Y u-report R Y v)-
      ∑y,w! y*(reading R (N:=z.1) (force y) u (uv.trans vb)-reading R (N:=z.1) (force y) v vb)‖ ≤
      (∫x:Points 3,‖φ x‖)*(2*capital C b rem η*Real.exp (-((H).S.scale b-(H).S.scale v)/8)) := by
  intro Y force
  let E:=2*capital C b rem η*Real.exp (-((H).S.scale b-(H).S.scale v)/8)
  have E0 : 0≤E := by
    have cols:=((H).levels.params b).columns_ge
    dsimp only [E,capital];positivity
  let d (y:Sites R z):=value R A z Q y u (uv.trans (vb.trans bN))-
    value R A z Q y v (vb.trans bN)-
    (reading R (N:=z.1) (force y) u (uv.trans vb)-reading R (N:=z.1) (force y) v vb)
  have each (y:Sites R z) (hy:w! y≠0) : ‖d y‖ ≤ E := by
    obtain ⟨fmt,paid,whole⟩:=live y hy
    let q0:=WilsonPhysicalMarkedDefect.RegularProjection.soft (q y)
    let a:=q0.density 0 T ((H).rep z.1 z.2 b)
    have store : WilsonCenteredFiledAtoms.Store ((H).rep z.1 z.2 b) T (C).params 0 (safety C b) rem a :=
      ⟨q0,fmt,paid,fun _=>rfl⟩
    have smooth:=admitted R A z y (Q y)
    have pa : Integrable a (prior G _) := message 0 z.1 z.2 b R.makes (ref.trans (uv.trans vb)) bN
      (show Trace.Physical.GermGraph.reads («C»:=R.family) 0 z.1 z.2 b q0 rem from ⟨fmt,paid⟩)
    have pb : Integrable (force y) (prior G _) := by
      have h:Integrable (credit C z.1 z.2 0 (cut! y) b bN-a) (prior G _):=(credit_int C z.1 z.2 0 _ smooth bN).sub pa
      rwa [whole,show q0.density 0 T ((H).rep z.1 z.2 b)=a from rfl,add_sub_cancel_left] at h
    have expr (j:ℕ) (jb:j≤b) : value R A z Q y j (jb.trans bN)=
        reading R (N:=z.1) a j jb+reading R (N:=z.1) (force y) j jb := by
      rw [←WilsonThermometerUnitFilingCompensated.combine R jb a (force y) pa pb]
      change _= reading R (N:=z.1) (q0.density 0 T ((H).rep z.1 z.2 b)
        +WilsonMeasuredCoefficientTransport.account (q y) (Ψ y)) j jb
      rw [←whole]
      unfold value reading
      rw [WilsonThermometerUnitFilingCoarse.cutoff R bN jb _ smooth]
    have dec:=decay R simple ref uv vb bN ou ov η ηpos store
    dsimp only [d];rw [expr u (uv.trans vb),expr v vb]
    convert dec using 2
    abel
  have linear : (report R Y u-report R Y v)-
      ∑y,w! y*(reading R (N:=z.1) (force y) u (uv.trans vb)-reading R (N:=z.1) (force y) v vb)=
      ∑y,w! y*d y := by
    rw [filed R simple A z r φ Q _ ou bu,filed R simple A z r φ Q _ ov bv]
    rw [←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _=>by dsimp only [d];ring
  rw [linear]
  calc
    _ ≤ ∑ y,‖w! y*d y‖ := norm_sum_le ..
    _ ≤ ∑ y,‖w! y‖*E := by
      apply Finset.sum_le_sum;intro y _;by_cases hy:w! y=0
      · simp [hy]
      · rw [norm_mul];exact mul_le_mul_of_nonneg_left (each y hy) (norm_nonneg _)
    _ = (∑ y,‖w! y‖)*E := Finset.sum_mul .. |>.symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (WilsonSeparatedOriginalThermometerCells.variation _ _
      (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)) E0

end YM.Integration.WilsonThermometerUnitFilingShape
