import YM.Integration.WilsonThermometerUnitFilingCoarse

/-! The arbitrary strictly positive fee margin is chosen after the signed
source error has been priced. It can be as small as that physical error. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingSharp
open Function Filter Lattice RG Wilson Labels Source Work.G08 Next.Foundations
open Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal RG12 Bid
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent
open Extra.Trajectories Extra.Multi Overlay MeasureTheory Cells
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFeed
open scoped BigOperators Topology Classical
open private flat from YM.Integration.WilsonThermometerUnitFilingCourse
variable {G : Gauge} (R : Run G) (simple : G.Simple)
local notation "C" => R.family
local notation "F" => R.family.labels.level 0
local notation "H" => R.family.path
local notation "T" => R.family.localSection 0

open WilsonThermometerUnitFilingCoarse (reading)
open private erase centered shift below calibration from YM.Integration.WilsonThermometerUnitFilingCoarse
open PhysicalNext.Repeat.Legato.Bandage
open WilsonMacroscopicRichCaptureFilingBudget (capital)
include simple in
theorem stored {N p u b : ℕ} (start : (C).ref 0 ≤ u) (ub : u≤b) (live : b≤N)
    {A : Config G ((C).side b p)→ℂ} {rem : ℝ} (η : ℝ) (ηpos : 0<η)
    (stored : WilsonCenteredFiledAtoms.Store ((H).rep N p b) T (C).params 0
      (safety C b) rem A) :
    ∃ c : ℂ,∀ j,u≤j → ∀ jb:j≤b, Opened C 0 j p →
      ‖reading R (N:=N) A j jb - c‖ ≤ capital C b rem η / gainChart H b j := by
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
  let E := capital C b rem η
  let θ := ‖alto H u 0‖*(E/gainChart H b u)
  let wage := fly R.alloy.B.a 0 u
  let w := wage/(2*(1+θ))
  have cpos : 0<2*rem+η := by linarith
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
  have space : (F).coeffSize q.x + rem ≤ 2*rem+η := by rw [qsize];linarith
  obtain ⟨Z,g,v,club,_,_,_,launch,rates⟩ :=
    retains_cancellation C N b u p 0 R.makes w X scrim q rem (2*rem+η) E
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


include simple in
theorem absolute {N p b j:ℕ} (start : (C).ref 0 ≤ j) (jb : j≤b) (bN : b≤N)
    (oj : Opened C 0 j p) (ob : Opened C 0 b p) {rem : ℝ} (η : ℝ) (ηpos : 0<η)
    (Q : Coefficient F ((C).side b p)) (fmt : Q.Format 0 (C).params ((H).rep N p b))
    (paid : Q.remBound 0 ((H).rep N p b) (safety C b) rem) :
    ‖reading R (N:=N) (Q.density 0 T ((H).rep N p b)) j jb‖ ≤
      ‖Q.x 0‖+2*capital C b rem η := by
  let A := Q.density 0 T ((H).rep N p b)
  have seed : WilsonCenteredFiledAtoms.Store ((H).rep N p b) T (C).params 0 (safety C b) rem A :=
    ⟨Q,fmt,paid,fun _=>rfl⟩
  obtain ⟨c,price⟩ := stored R simple start jb bN η ηpos seed
  have p0 := price b jb le_rfl ob
  have pj := price j le_rfl jb oj
  have flat_b : reading R (N:=N) A b le_rfl=Q.x 0 := by
    unfold reading;rw [gust_base];exact flat R simple _ T Q fmt
  rw [flat_b,gainChart,sub_self,mul_zero,Real.exp_zero,div_one] at p0
  have nonneg : 0≤capital C b rem η := (norm_nonneg _).trans p0
  have scales : Monotone (C).S.scale := monotone_nat_of_le_succ fun i => by
    rw [Schedule.scale_succ];exact le_add_of_nonneg_right (Real.log_nonneg
      (by exact_mod_cast ((C).S.block i).pos))
  have gain : 1≤gainChart H b j := Real.one_le_exp (mul_nonneg (by norm_num) (sub_nonneg.mpr (scales jb)))
  have pj' := pj.trans (div_le_self nonneg gain)
  have pc : ‖c‖ ≤ ‖Q.x 0‖+capital C b rem η := by
    have tc := norm_add_le (Q.x 0) (c-Q.x 0)
    rw [add_comm (Q.x 0) (c-Q.x 0),sub_add_cancel,norm_sub_rev c (Q.x 0)] at tc
    linarith
  have tc := norm_add_le (reading R (N:=N) A j jb-c) c
  rw [sub_add_cancel] at tc
  linarith

end YM.Integration.WilsonThermometerUnitFilingSharp
