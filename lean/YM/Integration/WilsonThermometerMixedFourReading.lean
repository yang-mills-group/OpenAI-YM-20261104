import YM.Integration.WilsonThermometerMixedConnectedFace
import YM.Integration.WilsonThermometerMixedAncestry

/- Four paid ordinary modes give the old-mixed connected scalar on the
   actual earlier Wilson reading, with the true three one-point means. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedFourReading
open Finset Filter Function Lattice Wilson RG Marker MeasureTheory QuadraticLocal
open Source Extra.Trajectories RG05Readout Records Native Address Many MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato
open WilsonThermometerMixedAmplitude WilsonThermometerMixedConnectedFace
open WilsonThermometerCenteredAlgebra WilsonThermometerCenteredScalar
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable {G:Gauge}(R:Run G){N per b:ℕ}
local notation "C" => R.family
local notation "X" => Config G ((C).side b per)→Poly (J)

def observed (F:X){j:ℕ}(jb:j ≤ b):Poly (J):=
  ((((C).path.rep N per j).eval 1:ℂ)⁻¹) • gust (C).path N per b F j jb 1

theorem coordinate (F:X)(earned:Integrable F (prior G _))(s:(J).Mode){j:ℕ}(jb:j ≤ b):
    (observed R (N:=N) F jb).part s=WilsonThermometerUnitFilingCoarse.reading R (N:=N)
      (fun U=>(F U).part s) j jb:=by
  have h:(fun U=>(gust (C).path N per b F j jb U).part s)=gust (C).path N per b (fun U=>(F U).part s) j jb:=by
    induction jb using Nat.decreasingInduction with
    | self=>rw [gust_base,gust_base]
    | of_succ j jt ih=>
      rw [gust_step (C).path N per b F jt,gust_step (C).path N per b _ jt]
      have pass:=push_get ((C).path.levels.transition_mass j per ((C).path.β N per (j+1)))
        (gust_live (C).path N per b F earned jt) s
      exact pass.trans (congrArg (((C).path.levels.clock.op j per).push ((C).path.β N per (j+1))) ih)
  change _*(gust (C).path N per b F j jb 1).part s=_*gust (C).path N per b _ j jb 1
  rw [congrFun h 1]

theorem four (A Y:Poly (J))(a0:A.part (J).quiet=1)(y0:Y.part (J).quiet=1)
    (low:∀i:Fin 3,read Y {i}=read A {i})(e:ℝ)
    (abc:‖read Y univ-read A univ‖ ≤ e)
    (ab:‖read Y {0,1}-read A {0,1}‖ ≤ e)
    (ac:‖read Y {0,2}-read A {0,2}‖ ≤ e)
    (bc:‖read Y {1,2}-read A {1,2}‖ ≤ e):
    ‖(Extra.Trajectories.connected Y).part full-(Extra.Trajectories.connected A).part full‖ ≤
      e*(1+‖read Y {0}‖+‖read Y {1}‖+‖read Y {2}‖):=by
  have eqn: (Extra.Trajectories.connected Y).part full-(Extra.Trajectories.connected A).part full=
      (read Y univ-read A univ)-
      ((read Y {0,1}-read A {0,1})*read Y {2}+
        (read Y {0,2}-read A {0,2})*read Y {1}+(read Y {1,2}-read A {1,2})*read Y {0}):=by
    rw [WilsonThermometerMixedConnectedFace.original A Y a0 y0 low,heard,heard];ring
  rw [eqn]
  have one:=norm_sub_le (read Y univ-read A univ)
    (((read Y {0,1}-read A {0,1})*read Y {2})+((read Y {0,2}-read A {0,2})*read Y {1})+
      (read Y {1,2}-read A {1,2})*read Y {0})
  have two:=norm_add_le ((read Y {0,1}-read A {0,1})*read Y {2}+(read Y {0,2}-read A {0,2})*read Y {1})
    ((read Y {1,2}-read A {1,2})*read Y {0})
  have three:=norm_add_le ((read Y {0,1}-read A {0,1})*read Y {2}) ((read Y {0,2}-read A {0,2})*read Y {1})
  rw [norm_mul] at two
  rw [norm_mul,norm_mul] at three
  linarith only [one,two,three,abc,mul_le_mul_of_nonneg_right ab (norm_nonneg (read Y {2})),
    mul_le_mul_of_nonneg_right ac (norm_nonneg (read Y {1})),mul_le_mul_of_nonneg_right bc (norm_nonneg (read Y {0}))]

private theorem low_mode {q:ℂ}{A Y F:Poly (J)}(h:Line q A Y F)(s:(J).Mode)(low:s.val.card ≤ 1):
    Y.part s=A.part s:=by
  have zero:=h.marked s low
  change F.part s-A.part s=0 at zero
  have eqn:=congrArg (fun p:Poly (J)=>p.part s) h.value
  change Y.part s=A.part s+q*(F.part s-A.part s) at eqn
  rw [zero,mul_zero,add_zero] at eqn
  exact eqn

theorem original (q:ℂ)(A Y F:X)(small:Integrable A (prior G _))(large:Integrable F (prior G _))
    (line:∀U,Line q (A U) (Y U) (F U)) {j:ℕ}(jb:j ≤ b)
    (unit:(observed R (N:=N) Y jb).part (J).quiet=1)
    (e:ℝ)(paid:∀s:Finset (Fin 3),2 ≤ s.card →
      ‖WilsonThermometerUnitFilingCoarse.reading R (N:=N)
        (fun U=>(Y U).part (face s)-(A U).part (face s)) j jb‖ ≤ e):
    let right:=observed R (N:=N) Y jb
    let left:=observed R (N:=N) A jb
    ‖(Extra.Trajectories.connected right).part full-(Extra.Trajectories.connected left).part full‖ ≤
      e*(1+‖read right {0}‖+‖read right {1}‖+‖read right {2}‖):=by
  intro right left
  let scalar:=(((C).path.rep N per j).eval 1:ℂ)⁻¹
  have transferred:=WilsonThermometerMixedAncestry.original R (N:=N) q A Y F small large line jb 1
  have fresh:Integrable Y (prior G _):=by
    have id:Y=A+q • (F-A):=funext fun U=>(line U).value
    rw [id];exact small.add ((large.sub small).smul _)
  have agreed (s:(J).Mode)(low:s.val.card ≤ 1):right.part s=left.part s:=by
    exact congrArg (fun a:ℂ=>scalar*a) (low_mode transferred s low)
  have quiet:left.part (J).quiet=1:=(agreed _ (by change (∅:Finset (Fin 3)).card ≤ 1;decide)).symm.trans unit
  have faceRate (s:Finset (Fin 3))(high:2 ≤ s.card):‖read right s-read left s‖ ≤ e:=by
    change ‖(observed R (N:=N) Y jb).part _-(observed R (N:=N) A jb).part _‖ ≤ _
    rw [coordinate R Y fresh,coordinate R A small]
    have diff:=WilsonThermometerMixedTapScalar.subtract R (N:=N) (fun U=>(Y U).part (face s)) (fun U=>(A U).part (face s))
      ((Poly.get _).integrable_comp fresh) ((Poly.get _).integrable_comp small) jb
    rw [←diff]
    exact paid s high
  apply four left right quiet unit (fun i=>agreed (face {i}) (by simp [face])) e
  · exact faceRate _ (by decide)
  · exact faceRate _ (by decide)
  · exact faceRate _ (by decide)
  · exact faceRate _ (by decide)

end YM.Integration.WilsonThermometerMixedFourReading
end
