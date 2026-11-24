import YM.Integration.WilsonMovingForkSeededPoint
import YM.Integration.WilsonAddressedMixedEnrolledTrial

/-! Each incoming color carries the original finite inverse fitted at its own
report date. The independent whole product uses those very doses and relative
positions on the common fine mesh. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkMixedSeed
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot PhysicalNext PhysicalNext.Repeat.Legato
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open RG05Readout Next.Rank Next.Rank.Station
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonThermometerUnitFilingFlatTelescope WilsonOriginalTwoFlatTelescope
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonOriginalMicroscopicGuardedPage
open WilsonMovingForkSeededPoint (seats)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ)
local notation "C" => R.family

def doses (station:Fin n→ℕ){N per:ℕ}(A:∀i,(C).label (d i) ≃ₗ[ℂ] (C).label (d i))
    (Y:∀i,(C).label (d i))(i:Fin n):(C).label (d i):=
  (A i).symm (fitted R (d i) (station i) N per (Y i))

theorem page {station:Fin n→ℕ}{N per:ℕ}(live:∀i,station i ≤ N)
    (A:∀i,(C).label (d i) ≃ₗ[ℂ] (C).label (d i))(Y:∀i,(C).label (d i))(i:Fin n):
    A i (doses R d station (N:=N) (per:=per) A Y i)=full R (d i) N per (station i) (Y i):=by
  rw [doses,LinearEquiv.apply_symm_apply,page_at R (d i) (live i)]
  rfl

/-- Engineering restoration of the native optical column in its actual K group word. -/
def units (K:ℕ)(w:∀i,(C).label (d i))(i:Fin n):(C).label (d i):=
  ((((C).S.a K:ℂ)^(d i))⁻¹) • w i

def product {N per K:ℕ}(ξ:Fin n→Site ((C).side K per))(w:∀i,(C).label (d i))
    (U:Config G ((C).side K per)):ℂ:=
  ∏i,WilsonPositionProgramBlockedTrialAddBack.uncut R (d i) N per K (ξ i) (units R d K w i) U

variable {R}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {l:Ultrafilter (ℕ×ℕ)}{j u v c K:ℕ}

include F
/-- Actual fixed-site comparison from the two dated deposits, the
common captured shift, and the true late physical read. The kernel
propagates all ordinary faces before any connected extraction. -/
theorem original (order:(l:Filter _) ≤ f.fuse)(uj:u ≤ j)(jK:j ≤ K)(uv:u ≤ v)(vc:v ≤ c)(ck:c ≤ K)
    (fields:∀i,S.Field (d i))(arms:∀i,Arm C S (l:Filter _) (d i) (fields i))
    (station:Fin n→ℕ)(o:Fin n→ Cover)(gen:tag ((C).S.a j) o∈generic n)(sep:tag ((C).S.a j) o∈conf n)
    (A:∀_N _per:ℕ,∀i,(C).label (d i) ≃ₗ[ℂ] (C).label (d i))
    (print:∀(_N per:ℕ),((i:Fin n)→(C).label (d i))→(Fin n→Site ((C).side K per))→
      ∀i:ℕ,Config G ((C).side i per)→ℂ)
    (seed:∀N per:ℕ,K<N → ∀w ξ,print N per w ξ K=product R d (N:=N) ξ w)
    (prediction:Points n→ℂ)(phase upper across terminal:ℝ)(fine coarse:ℕ→ℝ)
    (reflected:∀N per,∀top:j<N,‖gap R N per u (uj.trans top.le)
      (word R d j N per top.le o (fun i=>(arms i).source (N,per)))‖ ≤ phase):
    let M:=fun N per=>print N per (doses R d station (N:=N) (per:=per) (A N per) (fun i=>(arms i).source (N,per)))
      (seats (R:=R) jK per o)
    (∀ᶠ z:ℕ×ℕ in f.fuse,∀top:K<z.1,
      let Y:=word R d j z.1 z.2 (jK.trans top.le) o (fun i=>(arms i).source z)
      let w:=doses R d station (N:=z.1) (per:=z.2) (A z.1 z.2) (fun i=>(arms i).source z)
      let raw:=product R d (N:=z.1) (seats (R:=R) jK z.2 o) w
      let cut:=numerator R z.1 z.2 c (M z.1 z.2 c)
      let endPoint:=numerator R z.1 z.2 v (M z.1 z.2 v)
      (∀i,v ≤ i → i ≤ K → Integrable (numerator R z.1 z.2 i (M z.1 z.2 i)) (prior G _)) ∧
      ‖reading R (N:=z.1) (credit C z.1 z.2 0 Y K top.le) u (uv.trans (vc.trans ck))-
        reading R (N:=z.1) (numerator R z.1 z.2 K raw) u (uv.trans (vc.trans ck))‖ ≤ upper ∧
      (∀i∈Finset.Ico c K,‖feeAt R z.1 z.2 u (M z.1 z.2) i‖ ≤ fine i) ∧
      ‖reading R (N:=z.1) cut u (uv.trans vc)-reading R (N:=z.1) cut v vc‖ ≤ across ∧
      (∀i∈Finset.Ico v c,‖feeAt R z.1 z.2 v (M z.1 z.2) i‖ ≤ coarse i) ∧
      ‖reading R (N:=z.1) endPoint v le_rfl-prediction (tag ((C).S.a j) o)‖ ≤ terminal) →
    ‖S.classMoment S d (tag ((C).S.a j) o) fields-prediction (tag ((C).S.a j) o)‖ ≤ 
      phase+(upper+(∑i∈Finset.Ico c K,fine i)+across+(∑i∈Finset.Ico v c,coarse i)+terminal):=by
  intro M bills
  apply WilsonMovingForkOpticalPoint.original F order uj jK uv vc ck d fields arms o gen sep M
    (prediction (tag ((C).S.a j) o)) phase upper across terminal fine coarse reflected
  filter_upwards [bills] with z spent
  intro top
  obtain ⟨integrable,topPaid,hi,bridge,lo,endPaid⟩:=spent top
  refine ⟨integrable,?_,hi,bridge,lo,endPaid⟩
  unfold entrance
  change ‖_-reading R (N:=z.1) (numerator R z.1 z.2 K (print z.1 z.2 _ _ K)) u _‖ ≤ upper
  rw [seed z.1 z.2 top]
  exact topPaid

end YM.Integration.WilsonMovingForkMixedSeed
