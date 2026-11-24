import YM.Integration.WilsonThermometerUnitFilingCourse
import YM.Integration.WilsonMacroscopicRichEnrolledFiling
import YM.MergeProof.South.Window
import YM.Integration.WilsonCenteredFiledAtoms

/-! True older hearings of an insertion submitted directly at the capture
date. The complete field passes through the original transition kernels. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoarse
open Function Filter Lattice RG Wilson Labels Source Work.G08 Next.Foundations
open Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal RG12 Bid
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent
open Extra.Trajectories Extra.Multi Overlay MeasureTheory Cells
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFeed
open scoped BigOperators Topology Classical
open private flat the_page from YM.Integration.WilsonThermometerUnitFilingCourse
variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "C" => R.family
local notation "F" => R.family.labels.level 0
local notation "H" => R.family.path
local notation "T" => R.family.localSection 0

/-- The complete original conditional numerator, evaluated at flat only
after the entire physical interval has been integrated. -/
def reading {N p b : ℕ} (Z : Config G ((C).side b p) → ℂ) (j : ℕ) (jb : j≤b) : ℂ :=
  (((H).rep N p j).eval (1:Config G ((C).side j p)):ℂ)⁻¹ * gust H N p b Z j jb 1

theorem cutoff {N p b j : ℕ} (live : b≤N) (jb : j≤b) (Y : Cut C N p) (cont : Continuous Y) :
    gust H N p b (credit C N p 0 Y b live) j jb = credit C N p 0 Y j (jb.trans live) := by
  induction jb using Nat.decreasingInduction with
  | self => exact gust_base ..
  | of_succ a ha ih =>
    rw [gust_step H N p b _ ha,ih,credit_step C N p 0 Y cont (ha.trans_le live)]
    simp [transition,blast]

include simple in
theorem reported {N p b j : ℕ} (live : b≤N) (jb : j≤b) (Y : Cut C N p) (cont : Continuous Y)
    (door : Opened C 0 j p) (book : Booked C N p 0 Y j (jb.trans live)) :
    reading R (N:=N) (credit C N p 0 Y b live) j jb = report R Y j := by
  rw [WilsonThermometerUnitFilingCourse.filed R simple Y door (jb.trans live) book]
  unfold reading
  rw [cutoff R live jb Y cont]

private def erase {n : Side} (Q : Coefficient F n) : Coefficient F n := {Q with x:=0}

include simple in
private theorem centered {n : Side} (P : Rep G n) (S : SectionData F) (Q : Coefficient F n)
    (y : Site n) :
    Q.density y S P = (erase R Q).density y S P + Q.x 0 • (fun U => (P.eval U:ℂ)) := by
  have core : (F).core Q.x=0 := by
    obtain ⟨z,hz⟩ := RG12.unit_spans simple C 0 0 (by decide) Q.x
    have c : (F).core (unitVec F H 0)=0 := by
      funext i; by_cases hi:i=0 <;> simp [Labels.Frame.core,unitVec,Labels.Frame.e0,Function.update,hi]
    rw [hz,map_smul,c,smul_zero]
  funext U
  have entry : Q.exponentialEntry y S P U = Q.x 0+(erase R Q).exponentialEntry y S P U := by
    simp only [Coefficient.exponentialEntry,erase,core,map_zero,Pi.zero_apply,zero_add]
    simp only [Coefficient.maskedTerm,add_assoc]
  unfold Coefficient.density
  rw [entry]
  change (P.eval U:ℂ)*(Q.x 0 + (erase R Q).exponentialEntry y S P U)+
    (Real.exp (P.exponent U):ℂ)*(∑' b,Q.marked P b U)=
    ((P.eval U:ℂ)*(erase R Q).exponentialEntry y S P U+
    (Real.exp (P.exponent U):ℂ)*(∑' b,Q.marked P b U))+Q.x 0*(P.eval U:ℂ)
  ring

private theorem vacuum {N p b j : ℕ} (jb : j≤b) (live : b≤N) :
    gust H N p b (fun U => (((H).rep N p b).eval U:ℂ)) j jb =
      (fun U => (((H).rep N p j).eval U:ℂ)) := by
  induction jb using Nat.decreasingInduction with
  | self => exact gust_base ..
  | of_succ a ha ih =>
    rw [gust_step H N p b _ ha,ih]
    exact (vac_transfer H N p a R.makes.wilson (ha.trans_le live)).symm

private theorem shift {N p b j : ℕ} (jb : j≤b) (live : b≤N)
    (A : Config G ((C).side b p) → ℂ) (hi : Integrable A (prior G _)) (c : ℂ) :
    reading R (N:=N) (A+c • liftVac H N p b) j jb = reading R (N:=N) A j jb+c := by
  have eq : gust H N p b (A+c • liftVac H N p b) j jb =
      gust H N p b A j jb+c • liftVac H N p j := by
    induction jb using Nat.decreasingInduction with
    | self => rw [gust_base,gust_base]
    | of_succ i ix ih =>
      have vac := vac_integrable H N p (i+1) R.makes.wilson ((Nat.succ_le_of_lt ix).trans live)
      rw [gust_step H N p b _ ix,ih,StepData.push_add ((H).levels.transition_mass ..) _
        _ (gust_live H N p b A hi ix) (vac.smul c),StepData.push_smul _ _ _ _ vac,
        ←vac_transfer H N p i R.makes.wilson (ix.trans_le live),gust_step H N p b A ix]
  have pos : (((H).rep N p j).eval (1:Config G ((C).side j p)):ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    dsimp only [Rep.eval]
    rw [((H).rep N p j).activities.gas_one (p:=((H).rep N p j).p) (UVNext.CouplingReset.flags_one _),mul_one]
    exact (Real.exp_pos _).ne'
  unfold reading
  rw [eq,Pi.add_apply,Pi.smul_apply,smul_eq_mul, liftVac,mul_add,mul_left_comm,inv_mul_cancel₀ pos,mul_one]

include simple in
private theorem calibration {N p j : ℕ} (door : Opened C 0 j p) (live : j≤N)
    (x : (C).label 0) :
    (((H).rep N p j).eval (1:Config G ((C).side j p)):ℂ)⁻¹ *
      calValues («C»:=C) 0 N p j x 1=x 0 := by
  let q := ((C).factory 0 N p).entries j x
  have accepted := entryOk 0 N p j R.makes door.post live x
  have fit := WilsonThermometerUnitFilingFeed.transfer R simple door live x
  rw [fitting_apply] at fit
  change Trace.Physical.Germ.projection F (C).params (_) 0 q=x at fit
  have aq : q.Format 0 (C).params ((H).rep N p j) := accepted.1
  rw [the_page F (C).params (Q:=q) aq] at fit
  exact (flat R simple _ T q accepted.1).trans (congrFun fit 0)

variable {ψ : ℕ→ℝ} {ζ : ℕ→ℕ→ℝ}
private theorem below {N p u b : ℕ}
    {D : ∀ N p i : ℕ,i<N→GaugeDoor (R.family.path.rep N p (i+1)) (R.family.path.rep N p i)} (start : (C).ref 0 ≤ u) (live : b≤N)
    {μ fee : ℕ→ℝ} (Z : ∀ j:ℕ,Coefficient F ((C).side j p))
    (club : Club H (C).params T (ζ 0) ψ u b N p μ D Z fee live)
    (A : Config G ((C).side b p)→ℂ) (x : (C).label 0)
    (launch : value («C»:=C) 0 N p b (Z b)=A+calValues («C»:=C) 0 N p b (-x))
    {j : ℕ} (uj : u≤j) (jb : j≤b) :
    gust H N p b A j jb = value («C»:=C) 0 N p j (Z j)+calValues («C»:=C) 0 N p j x := by
  induction jb using Nat.decreasingInduction with
  | self =>
    have cancel : calValues («C»:=R.family) 0 N p b (-x)+calValues («C»:=R.family) 0 N p b x=0 := by
      apply (cal_add 0 N p b R.makes (start.trans uj) live (-x) x).symm.trans
      exact (congrArg (calValues («C»:=R.family) 0 N p b) (neg_add_cancel x)).trans
        (zero_cal 0 N p _ R.makes (start.trans uj) live)
    rw [gust_base,launch,add_assoc,cancel,add_zero]
  | of_succ j hj ih =>
    have prior := (start.trans uj).trans (Nat.le_succ j)
    have top := (Nat.succ_le_of_lt hj).trans live
    have admitted := club.ticks (j+1) (uj.trans (Nat.le_succ j)) hj
    have receipt := message 0 N p _ R.makes prior top
      (show reads 0 N p (j+1) (Z (j+1)) _ from admitted)
    have tagged := message 0 N p _ R.makes prior top (entryOk 0 N p _ R.makes prior top x)
    rw [gust_step H N p b A hj,ih (uj.trans (Nat.le_succ j))]
    apply (StepData.push_add ((H).levels.transition_mass ..)
      (value («C»:=R.family) 0 N p (j+1) (Z (j+1))) (calValues («C»:=R.family) 0 N p (j+1) x)
      receipt tagged).trans
    have old := (club.votes _ uj hj).1
    have mark := factory_eq («C»:=R.family) 0 N p j R.makes (start.trans uj) top x
    funext U
    exact congrArg₂ (fun a b:ℂ=>a+b) (by simpa only [value,blast,pow_zero,one_smul] using congrFun old.symm U)
      (by simpa only [transition,blast,pow_zero,one_smul] using congrFun mark.symm U)

open PhysicalNext.Repeat.Legato.Bandage
open WilsonMacroscopicRichCaptureFilingBudget (capital)

include simple in
theorem stored {N p u b : ℕ} (start : (C).ref 0 ≤ u) (ub : u≤b) (live : b≤N)
    {A : Config G ((C).side b p)→ℂ} {rem : ℝ}
    (stored : WilsonCenteredFiledAtoms.Store ((H).rep N p b) T (C).params 0
      (safety C b) rem A) :
    ∃ c : ℂ,∀ j,u≤j → ∀ jb:j≤b, Opened C 0 j p →
      ‖reading R (N:=N) A j jb - c‖ ≤ capital C b rem 1 / gainChart H b j := by
  obtain ⟨Q,fmt,paid,exactQ⟩ := stored
  let q := erase R Q
  have fmt0 : q.Format 0 (C).params ((H).rep N p b) :=
    ⟨fmt.smooth,fmt.origin,fmt.identity_null,fmt.projects,fmt.forcing,fmt.carried,fmt.invariant,fmt.supported,fmt.borel⟩
  have rem0 : q.remBound 0 ((H).rep N p b) (safety C b) rem := paid
  have r0 : 0 ≤ rem := by
    obtain ⟨v,w,hv,hw,bound,_⟩ := paid
    exact (add_nonneg hv hw).trans bound
  have qsize : (F).coeffSize q.x=0 := by simp [q,erase,Labels.Frame.coeffSize]
  let scrim := (R.again simple).1.scrim
  let E := capital C b rem 1
  let θ := ‖alto H u 0‖*(E/gainChart H b u)
  let wage := fly R.alloy.B.a 0 u
  let w := wage/(2*(1+θ))
  have cpos : 0<2*rem+1 := by linarith
  have cols : 1≤((H).levels.params b).columns := ((H).levels.params b).columns_ge
  have Epos : 0<E := by dsimp only [E,capital];exact mul_pos (by linarith) cpos
  have θ0 : 0≤θ := mul_nonneg (norm_nonneg _) (div_nonneg Epos.le (Real.exp_pos _).le)
  have wage0 : 0<wage := scrim.grows 0 u start
  have wp : 0<w := div_pos wage0 (by positivity)
  have reserved : w*‖alto H u 0‖*(E/gainChart H b u) ≤ wage/2 := by
    calc
      _ = w*θ := mul_assoc ..
      _ ≤ w*(1+θ) := mul_le_mul_of_nonneg_left (by linarith) wp.le
      _ = _ := by dsimp only [w];field_simp [show 1+θ ≠ 0 by positivity]
  obtain ⟨X,book,bought,carols,_⟩ := (scrim.costs.aim 0 N p (start.trans (ub.trans live))).lyrics
  have space : (F).coeffSize q.x + rem ≤ 2*rem+1 := by rw [qsize];linarith
  obtain ⟨Z,g,v,club,_,_,_,launch,rates⟩ :=
    retains_cancellation C N b u p 0 R.makes w X scrim q rem (2*rem+1) E
      start ub live bought carols fmt0 rem0 space le_rfl cpos wp reserved
  have file : ((C).factory 0 N p).entries=(X.draft H).inits := book
  have seed : value («C»:=R.family) 0 N p b (Z b)=
      q.density 0 T ((H).rep N p b)+calValues («C»:=R.family) 0 N p b (-v) := by
    change (Z b).density 0 T ((H).rep N p b) = _ +
      (((C).factory 0 N p).entries b (-v)).density 0 T ((H).rep N p b)
    rw [file]; exact launch
  have original : A = q.density 0 T ((H).rep N p b)+
      Q.x 0 • (fun U:Config G ((C).side b p)=>(((H).rep N p b).eval U:ℂ)) :=
    (funext exactQ).symm.trans (centered R simple _ T Q 0)
  have qi := message 0 N p b R.makes (start.trans ub) live
    (show Trace.Physical.GermGraph.reads («C»:=R.family) 0 N p b q rem from ⟨fmt0,rem0⟩)
  refine ⟨v 0+Q.x 0,fun j uj jb door=>?_⟩
  have state := club.ticks j uj jb
  have density := below R start live Z club _ v seed uj jb
  have points : reading R (N:=N) (q.density 0 T ((H).rep N p b)) j jb =
      (Z j).x 0+v 0 := by
    unfold reading
    rw [density,Pi.add_apply,mul_add,calibration R simple door (jb.trans live) v]
    exact congrArg (·+v 0) (flat R simple _ T (Z j) state.1)
  have restored : reading R (N:=N) A j jb = ((Z j).x 0+v 0)+Q.x 0 := by
    apply (congrArg (fun ψ:Config G ((C).side b p)→ℂ=>reading R (N:=N) ψ j jb) original).trans
    exact (shift R jb live _ qi (Q.x 0)).trans (congrArg (·+Q.x 0) points)
  have nonneg : 0 ≤ g j := by
    obtain ⟨a,b',ha,hb,bound,_⟩ := state.2; exact (add_nonneg ha hb).trans bound
  have coordinate : ‖(Z j).x 0‖ ≤ (F).coeffSize (Z j).x :=
    Finset.single_le_sum (f:=fun h=>‖(Z j).x h‖) (fun _ _=>norm_nonneg _) (Finset.mem_univ 0)
  rw [restored,show ((Z j).x 0+v 0)+Q.x 0-(v 0+Q.x 0)=(Z j).x 0 by abel]
  exact coordinate.trans ((le_add_of_nonneg_left nonneg).trans (rates j uj jb))

end YM.Integration.WilsonThermometerUnitFilingCoarse
