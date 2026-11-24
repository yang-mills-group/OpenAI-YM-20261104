import YM.Integration.WilsonPublicForkTrialHearing
import YM.Integration.WilsonOriginalTwoFlatPublicLimit

/-! At each generic aligned node the original physical field is recovered before taking the
weak-scale and independent inversion limits. All chronological differences below use the
same full ordinary source and the same original quiet. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkOpticalPoint
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot PhysicalNext PhysicalNext.Repeat.Legato
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open RG05Readout Next.Rank Next.Rank.Station
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonThermometerUnitFilingFlatTelescope WilsonOriginalTwoFlatTelescope
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{n j u v c K:ℕ}
local notation "C" => R.family

private lemma remove {x y:ℝ} (paid:∀ε:ℝ,0<ε → x ≤ y+ε):x ≤ y:=by
  by_contra! wrong
  have lower:=paid ((x-y)/2) (by linarith)
  linarith

include F
theorem original (order:(l:Filter _) ≤ f.fuse)(uj:u ≤ j)(jK:j ≤ K)(uv:u ≤ v)(vc:v ≤ c)(ck:c ≤ K)
    (d:Fin n→ℕ)(fields:∀i,S.Field (d i))(arms:∀i,Arm C S (l:Filter _) (d i) (fields i))
    (o:Fin n → Cover)(gen:tag ((C).S.a j) o∈generic n)(sep:tag ((C).S.a j) o∈conf n)
    (M:∀(_N per i:ℕ),Config G ((C).side i per)→ℂ)(I:ℂ)(phase upper across endFee:ℝ)
    (hi lo:ℕ→ℝ)
    (reflected:∀N per,∀top:j<N,‖gap R N per u (uj.trans top.le)
      (word R d j N per top.le o (fun i=>(arms i).source (N,per)))‖ ≤ phase)
    (signed:∀ᶠ z:ℕ×ℕ in f.fuse,∀top:K<z.1,
      let Y:=word R d j z.1 z.2 (jK.trans top.le) o (fun i=>(arms i).source z)
      let cut:=numerator R z.1 z.2 c (M z.1 z.2 c)
      let endPoint:=numerator R z.1 z.2 v (M z.1 z.2 v)
      (∀i,v ≤ i → i ≤ K → Integrable (numerator R z.1 z.2 i (M z.1 z.2 i)) (prior G _)) ∧
      entrance R Y (uv.trans (vc.trans ck)) top.le (M z.1 z.2) ≤ upper ∧
      (∀i∈Finset.Ico c K,‖feeAt R z.1 z.2 u (M z.1 z.2) i‖ ≤ hi i) ∧
      ‖reading R (N:=z.1) cut u (uv.trans vc)-reading R (N:=z.1) cut v vc‖ ≤ across ∧
      (∀i∈Finset.Ico v c,‖feeAt R z.1 z.2 v (M z.1 z.2) i‖ ≤ lo i) ∧
      ‖reading R (N:=z.1) endPoint v le_rfl-I‖ ≤ endFee):
    ‖S.classMoment S d (tag ((C).S.a j) o) fields-I‖ ≤
      phase+(upper+(∑i∈Finset.Ico c K,hi i)+across+(∑i∈Finset.Ico v c,lo i)+endFee):=by
  have late:∀ᶠ z:ℕ×ℕ in f.fuse,K<z.1:=by
    rw [Order.fused];exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_gt_atTop K
  have node:=WilsonOriginalTwoFlatPublicLimit.at_nodes F order uj d fields o gen sep arms phase reflected
  apply remove
  intro ε ep
  obtain ⟨z,arrival,contract,after⟩:=(node ε ep |>.and ((signed.filter_mono order).and (late.filter_mono order))).exists
  obtain ⟨_,flat⟩:=arrival
  obtain ⟨wage,entry,old,cap,young,last⟩:=contract after
  let Y:=word R d j z.1 z.2 (jK.trans after.le) o (fun i=>(arms i).source z)
  have healthy:Continuous Y:=continuous_finsetProd _ fun i _=>(C).continuousO _ _ _ _ _
  have read:=WilsonPublicForkTrialHearing.fixed R uv vc ck after.le Y healthy (M z.1 z.2) wage I
  dsimp only at read
  have total:=read.trans (add_le_add (add_le_add (add_le_add (add_le_add entry
    (Finset.sum_le_sum old)) cap) (Finset.sum_le_sum young)) last)
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add flat total).trans_eq (by ring))

end YM.Integration.WilsonMovingForkOpticalPoint
