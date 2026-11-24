import YM.Integration.WilsonThermometerPepperFace
import YM.Integration.WilsonThermometerCorridorLawn
import YM.Integration.WilsonThermometerPepperDifference
import YM.Integration.WilsonThermometerMixedFourReading
/- The two true taps of the complete named separated incoming R gallery at
   its exact reference f use the affordable rides from the earlier grouped
   date. The continuation below f has the same actors on every original mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorFiling
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi
open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open WilsonThermometerOwnOffsetField WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => (A).clock.hatBeta
local notation "d" => WilsonThermometerFundedWeakCells.degree
local notation "B" => WilsonThermometerOffsetLedger.cash R
local notation "slots" => (Stock.census (Fin 3))

local notation "CF"=>R.family

open RG05Readout.Pantry WilsonThermometerOwnOffsetJoint

open WilsonThermometerCorridorRoster

local notation "V"=>Unit×Fin 3
local notation "Y"=>Stock.census (V)

open WilsonThermometerMixedAmplitude WilsonThermometerUnitFilingCoarse
variable {N p f u:ℕ}
local notation "U"=>Config G ((CF).side f p)

open Extra.Histories.Relay WilsonThermometerPepperFace

theorem projected {I:Type} [DecidableEq I] {J:Census I}(F:(U)→Poly J)
    (paid:Integrable F (prior G _))(s:J.Mode)(uf:u≤f):
    (fun W=>(gust (CF).path N p f F u uf W).part s)=gust (CF).path N p f (fun X=>(F X).part s) u uf:=by
  induction uf using Nat.decreasingInduction with
  | self=>rw [gust_base,gust_base]
  | of_succ j jt ih=>
    rw [gust_step (CF).path N p f F jt,gust_step (CF).path N p f _ jt]
    exact (push_get ((CF).path.levels.transition_mass j p ((CF).path.β N p (j+1)))
      (gust_live (CF).path N p f F paid jt) s).trans
      (congrArg (((CF).path.levels.clock.op j p).push ((CF).path.β N p (j+1))) ih)

theorem tower {j:ℕ}(F:(U)→ℂ)(uj:u≤j)(jf:j≤f):
    gust (CF).path N p f F u (uj.trans jf)=gust (CF).path N p j (gust (CF).path N p f F j jf) u uj:=by
  induction uj using Nat.decreasingInduction with
  | self=>rw [gust_base]
  | of_succ k kj ih=>rw [gust_step (CF).path N p f F (kj.trans_le jf),gust_step (CF).path N p j _ kj,ih]

theorem lifted (F:(U)→Poly slots)(s:(slots).Mode)(paid:Integrable F (prior G _))
    (copy:Integrable (fun X=>lift (F X)) (prior G _))(uf:u≤f):
    (fun X=>(gust (CF).path N p f (fun X=>lift (F X)) u uf X).part (mask s))=
      (fun X=>(gust (CF).path N p f F u uf X).part s):=by
  rw [projected R _ copy (mask s) uf,projected R F paid s uf]
  congr 1
  exact funext (fun X=>WilsonThermometerCorridorRoster.read (F X) s)

theorem whole_mask:mask (whole (Fin 3))=whole (Unit×Fin 3):=by
  apply Subtype.ext
  ext ⟨⟨⟩,i⟩
  simp [mask,whole,place,Prod.ext_iff]

theorem proper_mask (i:Fin 3):mask (rest ((slots).fire i))=rest ((Y).fire (place i)):=by
  apply Subtype.ext
  ext ⟨⟨⟩,v⟩
  simp [mask,rest,place,Prod.ext_iff]
  change v∉({i}:Finset (Fin 3)) ↔ ((),v)∉({((),i)}:Finset (Unit×Fin 3))
  simp

theorem collected {k:ℕ}(F:(U)→Poly slots)(s:(slots).Mode)(paid:Integrable F (prior G _))
    (copy:Integrable (fun X=>lift (F X)) (prior G _))(height:k+2≤f)(uk:u≤k):
    let upper:=gust (CF).path N p f (fun X=>lift (F X)) (k+2) height
    let down:=((A).clock.op (k+1) p).push ((CF).path.β N p (k+2)) upper
    let held:=((A).clock.op k p).push ((CF).path.β N p (k+1)) (fun X=>(down X).part (mask s))
    reading R (N:=N) (p:=p) held u uk=(WilsonThermometerMixedFourReading.observed R (N:=N) F (uk.trans (by omega))).part s:=by
  intro upper down held
  have kf:k<f:=by omega
  have kf':k+1<f:=by omega
  have eq:down=gust (CF).path N p f (fun X=>lift (F X)) (k+1) kf'.le:=(gust_step _ _ _ _ _ kf').symm
  have present:(fun X=>(down X).part (mask s))=gust (CF).path N p f (fun X=>(F X).part s) (k+1) kf'.le:=by
    rw [eq,lifted R F s paid copy kf'.le,projected R F paid s kf'.le]
  have knot:held=gust (CF).path N p f (fun X=>(F X).part s) k kf.le:=by
    dsimp only [held];rw [present,←gust_step (CF).path N p f (fun X=>(F X).part s) kf]
  rw [knot,WilsonThermometerMixedFourReading.coordinate R F paid s]
  unfold WilsonThermometerUnitFilingCoarse.reading
  rw [←tower R _ uk kf.le]

end YM.Integration.WilsonThermometerCorridorFiling
end
