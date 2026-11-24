import YM.Integration.WilsonOriginalCompanionPepperAll
import YM.Integration.WilsonThermometerCorridorFiling

/-! Full signed credits commute with each original Wilson push and with its positive vacuum normalization. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionLinearFiling
open Function Finset Set MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums RG12
open Extra.Histories Extra.Histories.Relay Extra.Multi Extra.Trajectories Ac GridApprox.Nil MergeProof MergeProof.Accent
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many PhysicalNext.Repeat.Legato
open WilsonThermometerCorridorFiling WilsonThermometerCorridorRoster WilsonThermometerUnitFilingCoarse
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p f u:ℕ}{V V':Type}[DecidableEq V][DecidableEq V']{J:Census V}{K:Census V'}
local notation "C" => R.family
local notation "A" => (C).path.levels
local notation "Field" => Config G ((C).side f p)
def amount (F:Field→Poly J)(uf:u≤f):Poly J:=
    ((((C).path.rep N p u).eval 1:ℂ)⁻¹) • gust (C).path N p f F u uf 1

theorem coordinate (F:Field→Poly J)(paid:Integrable F (prior G _))(s:J.Mode)(uf:u≤f):
    (amount R (N:=N) F uf).part s=reading R (N:=N) (fun U=>(F U).part s) u uf:=by
  change _*(gust (C).path N p f F u uf 1).part s=_*gust (C).path N p f _ u uf 1
  rw [congrFun (projected R F paid s uf) 1]

omit R in
private theorem pushed {n m:Side}{S:StepData m n}{F:Config G n→Poly J}{x:ℝ}
    (h:S.IsKernel x G)(live:Integrable F (prior G _))(L:Poly J →L[ℂ] Poly K):
    (fun U=>L (S.push x F U))=S.push x (fun U=>L (F U)):=by
  let D:=L.restrictScalars ℝ
  funext U
  unfold StepData.push
  have eq:=D.integral_comp_comm (StepData.push_slice h U F live)
  simp_rw [D.map_smul] at eq
  exact eq.symm

theorem transformed (L:Poly J →L[ℂ] Poly K)(F:Field→Poly J)(paid:Integrable F (prior G _))(uf:u≤f):
    L (amount R (N:=N) F uf)=amount R (N:=N) (fun U=>L (F U)) uf:=by
  have transit:(fun U=>L (gust (C).path N p f F u uf U))=
      gust (C).path N p f (fun U=> L (F U)) u uf:=by
    induction uf using Nat.decreasingInduction with
    | self=>rw [gust_base,gust_base]
    | of_succ j jt ih=>
      rw [gust_step (C).path N p f F jt,gust_step (C).path N p f _ jt]
      exact (pushed ((A).transition_mass j p ((C).path.β N p (j+1)))
        (gust_live (C).path N p f F paid jt) L).trans
        (congrArg (((A).clock.op j p).push ((C).path.β N p (j+1))) ih)
  unfold amount
  rw [L.map_smul,congrFun transit 1]

theorem credited {I:Type}[Fintype I][DecidableEq I]{j:ℕ}(F:Field→Poly (Stock.census I))(s:(Stock.census I).Mode)
    (copy:Integrable (fun X=>lift (F X)) (prior G _))(height:j+2≤f)(uj:u≤j):
    let upper:=gust (C).path N p f (fun X=>lift (F X)) (j+2) height
    let down:=((A).clock.op (j+1) p).push ((C).path.rep N p (j+2)).beta upper
    WilsonOriginalCompanionPepperAll.pay R (N:=N) uj (fun X=>(down X).part (mask s))=
      reading R (N:=N) (p:=p) (fun X=>(F X).part s) u (uj.trans (by omega)):=by
  intro upper down
  have jf:j<f:=by omega
  have kf:j+1<f:=by omega
  have eq:down=gust (C).path N p f (fun X=>lift (F X)) (j+1) kf.le:=(gust_step _ _ _ _ _ kf).symm
  have present:(fun X=>(down X).part (mask s))=gust (C).path N p f (fun X=>(F X).part s) (j+1) kf.le:=by
    rw [eq,projected R _ copy (mask s) kf.le]
    congr 1
    exact funext (fun X=>WilsonThermometerCorridorRoster.read (F X) s)
  unfold WilsonOriginalCompanionPepperAll.pay
  rw [present,←gust_step (C).path N p f (fun X=>(F X).part s) jf]
  unfold reading
  rw [←tower R _ uj jf.le]

end YM.Integration.WilsonOriginalCompanionLinearFiling
end
