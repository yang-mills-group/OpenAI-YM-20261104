import YM.Integration.WilsonPositionProgramTrialPublicGather
import YM.Integration.WilsonPositionProgramTrialPublicPaidFace

/-! The joint actual K-socket, including each earlier mixed and scalar output after it
is subsequently run on the N vacuum. The identity is at its authenticated birth. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJoint
open Function Finset Lattice Laurent Wilson RG Source Labels Tree Exterior PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonIndependentMatchedOpeningRoster (field seat)
open WilsonIndependentRawRosterWord (degree fold)
open WilsonIndependentRawPhysicalFaces (ordered entered)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentMatchedOpeningFiled (planted)
open WilsonIndependentMatchedOrdinarySeat (here)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonPositionProgramTrialPublicPaidFace (cost amount columns originalRow)
open WilsonPositionProgramTrialPublicGather (gather ear)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]

omit [Fintype I] in
theorem original (R:Run G)(W:Initialize G)(D d:I→ℕ){stamps:I→ℕ}(cut:∀i,d i<stamps i)
    (κ:(i:I)→Knob (D i))(pt:I→Chamber)(o:I → Cover)(S:Finset I)[Nonempty S]
    (v:∀i,(R.family.labels.level (d i)).Coeff)(φ:I→ℂ→L[ℝ]ℝ)(A:Case D):
    gather (fun i:S=>planted R W false (cut i) (ear (stamps i) (claim (D i) (κ i) (pt i) (A i)))
      (written (R.family.labels.level (d i)) (v i) (φ i)) (o i)) ordered=columns R W D d cut κ pt o S v φ A:=by
  let J:=ordered (I:=S)
  let P (i:S):=planted R W false (cut i) (ear (stamps i) (claim (D i) (κ i) (pt i) (A i)))
    (written (R.family.labels.level (d i)) (v i) (φ i)) (o i)
  let C (i:S)(j:(R.family.labels.level (d i)).Index):=
    column R W false (cut i) (seat (R.family.labels.level (d i)) j) (o i)
  let dS:=fun i:S=>d i
  let H:=J.accounts dS
  let paid i j:=cost R D d κ pt v φ A i j
  have p (i:S):Auth (d i) (P i):=WilsonIndependentMatchedOpeningFiled.enrolled .. 
  have rate (i:S)(j:(R.family.labels.level (d i)).Index):Auth (d i) (affiled (paid i j) (C i j)):=
    (WilsonIndependentMatchedOpeningPayment.enrolled R W false (cut i) (seat (R.family.labels.level (d i)) j) (o i) (paid i j)).tall
      (valence_cap _ _)
  let Z:=((i:S)→(R.family.labels.level (d i)).Index)
  let B (b:Z):=field R W (fun _:S=>false) dS b (fun i:S=>cut i) (fun i:S=>o i) J
  have ready (b:Z):Auth H (B b):=by
    apply (WilsonIndependentMatchedOpeningRoster.enrolled R W (fun _:S=>false) dS b (fun i:S=>cut i)
      (fun i:S=>o i) J).tall
    exact WilsonPositionProgramTrialPublicGather.extent (fun i:S=>valence_cap (R.family.labels.level (d i)) (seat (R.family.labels.level (d i)) (b i))) J
  let weight (b:Z):=∏i:S,paid i (b i)
  have rows (b:Z):Auth H (affiled (weight b) (B b)):=WilsonIndependentMatchedOpeningFee.grant _ (ready b) _
  apply WilsonIndependentMatchedOpeningFaithful.original (WilsonPositionProgramTrialPublicGather.funded P dS p J)
    (Auth.sum (fun b _=>rows b))
  intro n y
  have leaf (i:S):here n y (flash ((P i).1 n))=
      ∑j:(R.family.labels.level (d i)).Index,paid i j*here n y (flash ((C i j).1 n)):=by
    have same:P i=∑j,affiled (paid i j) (C i j):=by
      simpa only [P,WilsonPositionProgramTrialPublicSticker.paidWord,paid,cost,amount,
        WilsonPositionProgramTrialPublicGather.heard] using
        WilsonPositionProgramTrialPublicSticker.original R W (cut i)
          (ear (stamps i) (claim (D i) (κ i) (pt i) (A i))) (v i) (φ i) (o i)
    rw [same,WilsonIndependentMatchedOpeningMass.sum _ _ _ (rate i)]
    exact Finset.sum_congr rfl (fun j _=>WilsonIndependentMatchedOpeningFee.read _
      (WilsonIndependentMatchedOpeningColumn.enrolled R W false (cut i) (seat (R.family.labels.level (d i)) j) (o i)) _ n y)
  change here n y (flash ((gather P J).1 n))=here n y (flash ((∑b:Z,affiled (weight b) (B b)).1 n))
  rw [WilsonPositionProgramTrialPublicGather.read P dS p n y J,entered.product,
    WilsonIndependentMatchedOpeningMass.sum _ _ _ rows]
  simp_rw [leaf]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [WilsonIndependentMatchedOpeningFee.read _ (ready b) (weight b) n y,Finset.prod_mul_distrib]
  apply congrArg (weight b * ·)
  change (∏i:S,here n y (flash ((C i (b i)).1 n)))=here n y (flash ((B b).1 n))
  have folded:=WilsonOriginalPublicNodalTestedRoster.folded R W dS b (fun i:S=>cut i) (fun i:S=>o i) J n
  rw [show flash ((B b).1 n)=_ from folded,entered.product,map_prod]

theorem measured (R:Run G)(W:Initialize G)(D d:I→ℕ){stamps:I→ℕ}(cut:∀i,d i<stamps i)
    (κ:(i:I)→Knob (D i))(pt:I→Chamber)(o:I → Cover)(S:Finset I)[Nonempty S]
    (v:∀i,(R.family.labels.level (d i)).Coeff)(φ:I→ℂ→L[ℝ]ℝ)(A:Case D)(fill:∀i,(R.family.labels.level (d i)).Index):
    originalRow R D d κ pt o S fill v φ A=
    gather (fun i:S=>planted R W false (cut i) (ear (stamps i) (claim (D i) (κ i) (pt i) (A i)))
      (written (R.family.labels.level (d i)) (v i) (φ i)) (o i)) ordered:=
  (WilsonPositionProgramTrialPublicPaidFace.original R W D d cut κ pt o S fill v φ A).trans
    (original R W D d cut κ pt o S v φ A).symm

end YM.Integration.WilsonPositionProgramTrialPublicJoint
end
