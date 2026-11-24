import YM.Integration.WilsonThermometerMixedFourReading
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedVacuumReading
open Finset Filter Function Lattice Wilson RG Marker MeasureTheory QuadraticLocal
open Source Extra.Trajectories RG05Readout Records Native Address Many MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato
open WilsonThermometerMixedAmplitude WilsonThermometerMixedConnectedFace
open WilsonThermometerCenteredAlgebra WilsonThermometerCenteredScalar
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable {G:Gauge}(R:Run G){N per b:ℕ}
local notation "C" => R.family
local notation "X" => Config G ((C).side b per)→Poly (J)

open WilsonThermometerMixedFourReading Extra.Histories Extra.Histories.Relay

private theorem projected (F:X)(paid:Integrable F (prior G _))(s:(J).Mode){j:ℕ}(jb:j ≤ b):
    (fun W=>(gust (C).path N per b F j jb W).part s)=gust (C).path N per b (fun U=>(F U).part s) j jb:=by
  induction jb using Nat.decreasingInduction with
  | self=>rw [gust_base,gust_base]
  | of_succ j jt ih=>
    rw [gust_step (C).path N per b F jt,gust_step (C).path N per b _ jt]
    have pass:=push_get ((C).path.levels.transition_mass j per ((C).path.β N per (j+1)))
      (gust_live (C).path N per b F paid jt) s
    exact pass.trans (congrArg (((C).path.levels.clock.op j per).push ((C).path.β N per (j+1))) ih)

private theorem vacuum {j:ℕ} (jb:j ≤ b) (live:b ≤ N):
    gust (C).path N per b (fun U=>(((C).path.rep N per b).eval U:ℂ)) j jb=
      (fun U=>(((C).path.rep N per j).eval U:ℂ)):=by
  induction jb using Nat.decreasingInduction with
  | self=>exact gust_base ..
  | of_succ a ha ih=>
    rw [gust_step (C).path N per b _ ha,ih]
    exact (vac_transfer (C).path N per a R.makes.wilson (ha.trans_le live)).symm

theorem transferred (F:X)(paid:Integrable F (prior G _))(h:∀U,(F U).part (J).quiet=(((C).path.rep N per b).eval U:ℂ))
    {j:ℕ}(jb:j ≤ b)(cut:b ≤ N)(U): (gust (C).path N per b F j jb U).part (J).quiet=(((C).path.rep N per j).eval U:ℂ):=by
  exact congrFun ((projected R F paid _ jb).trans ((congrArg (fun a=>gust (C).path N per b a j jb) (funext h)).trans
    (vacuum R jb cut))) U

theorem original (F:X)(paid:Integrable F (prior G _))(h:∀U,(F U).part (J).quiet=(((C).path.rep N per b).eval U:ℂ))
    {j:ℕ}(jb:j ≤ b)(cut:b ≤ N): (observed R (N:=N) F jb).part (J).quiet=1:=by
  change _*(gust (C).path N per b F j jb 1).part (J).quiet=1
  rw [transferred R F paid h jb cut]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson (jb.trans cut) _).ne')

theorem same (q:ℂ)(A Y F:X)(small:Integrable A (prior G _))(large:Integrable F (prior G _))
    (h:∀U,Line q (A U) (Y U) (F U)){j:ℕ}(jb:j ≤ b)(s:(J).Mode)(low:s.val.card ≤ 1):
    (observed R (N:=N) Y jb).part s=(observed R (N:=N) A jb).part s:=by
  let a:=gust (C).path N per b A j jb 1
  let y:=gust (C).path N per b Y j jb 1
  let f:=gust (C).path N per b F j jb 1
  have line:Line q a y f:=WilsonThermometerMixedAncestry.original R (N:=N) q A Y F small large h jb 1
  have zero:=line.marked s low
  change f.part s-a.part s=0 at zero
  have at_s:=congrArg (fun z:Poly (J)=>z.part s) line.value
  change y.part s=a.part s+q*(f.part s-a.part s) at at_s
  rw [zero,mul_zero,add_zero] at at_s
  exact congrArg (fun c:ℂ=>((((C).path.rep N per j).eval 1:ℂ)⁻¹)*c) at_s
end YM.Integration.WilsonThermometerMixedVacuumReading
end
