import YM.Integration.WilsonPositionProgramTrialPublicSpatialSum
import YM.Integration.WilsonOriginalPublicNodalTestedChronology

/-! Reassemble the exact finite site portfolio under its old N vacuum at the appointed spatial pulse. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicPulse
open private accounts from YM.Integration.WilsonOriginalPublicNodalTestedChronology
open Precision Function Finset Lattice Laurent Wilson RG Source Labels Marker Tree Exterior PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Soil
open WilsonCoeffUV.Shard
open WilsonFiniteMarkedHistoryStep
open WilsonOriginalPublicNodalChildSites (digits here)
open WilsonPositionProgramTrialPublicSpatialSum (visit held)
open WilsonReceivedCanonicalSocketSeed (contact)
open WilsonPositionProgramTrialPublicGather (gather)
open WilsonPositionProgramTrialPublicOldReturn (portfolio)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentRawPhysicalFaces (ordered entered)
open WilsonOriginalPhysicalFruitVerse (written)
open PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]

abbrev choices (D:I→ℕ)(T:(i:I)→Rarity (D i))(x:I→ℝ)(y:ℝ)(o:I→CellR)(S:Finset I):Type:=
  (i:S)→visit (D i) (T i) (x i) y (o i)

def sites (D:I→ℕ)(T:(i:I)→Rarity (D i))(x:I→ℝ)(y:ℝ)(o:I→CellR)(S:Finset I)
    (z:choices D T x y o S)(i:I):Cover:=if hi:i∈S then (z ⟨i,hi⟩).val else 0

def frame (D d:I→ℕ)(T:(i:I)→Rarity (D i))(x:I→ℝ)(y:ℝ)(o:I→CellR)(S:Finset I)
    (z:choices D T x y o S):Case D:=
  fun i=>held (D i) (T i) (x i) y (o i) (d i) (sites D T x y o S z i)

def survey (R:Run G)(W:Initialize G)(D d:I→ℕ)(cut:∀i,d i<D i)
    (v:∀i,(R.family.labels.level (d i)).Coeff)(φ:I→ℂ→L[ℝ]ℝ)(T:(i:I)→Rarity (D i))
    (x:I→ℝ)(y:ℝ)(o:I→CellR)(S:Finset I)[Nonempty S]:Era G ℝ:=
  gather (fun i:S=>word (Shrine (plate (sectionAt R W false (d i)) (cut i)) (written _ (v i) (φ i)))
    (T i) (x i) y (o i) (d i)) ordered

theorem original (R:Run G)(W:Initialize G)(D d:I→ℕ)(cut:∀i,d i<D i)(S:Finset I)[Nonempty S]
    (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (φ:I→ℂ→L[ℝ]ℝ)(T:(i:I)→Rarity (D i))(x:I→ℝ)(xp:∀i,0<x i)(y:ℝ)(o:I→CellR)
    (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (N m c K:ℕ)(mc:m≤c)(cK:c≤K)(KN:K≤N):
    (∑z:choices D T x y o S,portfolio R D d (fun i=>contact (D i)) (fun _=>zeroC) S fill v φ
      (frame D d T x y o S z) L O N (digits L K (sites D T x y o S z)) m c K
      (here L K (sites D T x y o S z) c))=
    cruises L O N (mass d S) K m (survey R W D d cut v φ T x y o S):=by
  let J (i:S):=visit (D i) (T i) (x i) y (o i)
  let P (i:S)(z:J i):=planted R W false (cut i)
    (held (D i) (T i) (x i) y (o i) (d i) z.val) (written _ (v i) (φ i)) z.val
  have auth (i:S)(z:J i):Auth (d i) (P i z):=WilsonIndependentMatchedOpeningFiled.enrolled ..
  have wage (z:(i:S)→J i):Auth (mass d S) (gather (fun i:S=>P i (z i)) ordered):=by
    have ready:=WilsonPositionProgramTrialPublicGather.funded _ (fun i:S=>d i) (fun i:S=>auth i (z i)) ordered
    have h:(ordered (I:=S)).accounts (fun i:S=>d i)=mass d S:=
      (accounts (fun i:S=>d i)).trans (Finset.sum_coe_sort S d)
    exact h ▸ ready
  have together:survey R W D d cut v φ T x y o S=∑z:((i:S)→J i),gather (fun i:S=>P i (z i)) ordered:=by
    unfold survey
    simp_rw [WilsonPositionProgramTrialPublicSpatialSum.leg R W (cut _) _ _ _ _ _ _ (xp _)]
    exact WilsonPositionProgramTrialPublicSpatialSum.combine J (fun i:S=>d i) P auth
  rw [together]
  have split:=WilsonOriginalPublicNodalProfiles.sum L O simple ratio N K m (mass d S) (mc.trans cK) KN
    univ (fun _ : ((i:S)→J i)=>1) (fun z=>gather (fun i:S=>P i (z i)) ordered) (fun z _=>wage z)
  simp only [one_smul] at split
  rw [split]
  apply Finset.sum_congr rfl
  intro z _
  rw [WilsonPositionProgramTrialPublicVisits.original R W D d cut S fill v φ _ L O simple ratio N m c K mc cK KN]
  apply congrArg (cruises L O N (mass d S) K m)
  apply congrArg (fun h=>gather h (ordered (I:=S)))
  funext i
  simp only [P,frame,sites,dif_pos i.2]

end YM.Integration.WilsonPositionProgramTrialPublicPulse
end
