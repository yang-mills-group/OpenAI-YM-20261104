import YM.Integration.WilsonMovingForkOpticalPoint
import YM.Integration.WilsonMovingForkRawSeed

/-! At each generic aligned node the original physical field is recovered before taking the
weak-scale and independent inversion limits. All chronological differences below use the
same full ordinary source and the same original quiet. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSeededPoint
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

open WilsonOriginalMicroscopicGuardedPage WilsonOriginalMicroscopicGuardedReporters

/-- These are the physical K-seats for the previously enrolled optical points. -/
def seats (jK:j ≤ K)(per:ℕ)(o:Fin n → Cover):Fin n → Site ((C).side K per):=
  fun i=>((C).S.toDepth jK per).embed (wrap _ (o i))

theorem upper_positions {N per:ℕ}(jK:j ≤ K)(kn:K ≤ N)(o:Fin n → Cover)(i:Fin n):
    ((C).S.toDepth kn per).embed (seats (R:=R) jK per o i)=
    ((C).S.toDepth (jK.trans kn) per).embed (wrap _ (o i)):=by
  exact (Next.Rank.Station.embed_comp _ _ _ _).symm

/-- Finite independent renderers are submitted as functions of the given doses and sites.
The entire planted contribution at K is then fixed before the original signed returns. -/
def fresh {D:ℕ}(d:Fin n→Fin (D+1))(Y:∀i:Fin n,ℕ×ℕ→(C).label (d i))
    (o:Fin n → Cover)(jK:j ≤ K)(A:∀_N _per:ℕ,∀e:Fin (D+1),(C).label e ≃ₗ[ℂ] (C).label e)
    (print:∀(_N per:ℕ),((i:Fin n) → (C).label (d i)) → (Fin n→ Site ((C).side K per)) →
      ∀ i : ℕ, Config G ((C).side i per)→ℂ)(N per i:ℕ):Config G ((C).side i per)→ℂ:=
  print N per (fun a=>WilsonMovingForkRawSeed.column R (j:=j) (N:=N) (per:=per) (A N per (d a)) (Y a (N,per)))
    (seats (R:=R) jK per o) i

include F
theorem original (order:(l:Filter _) ≤ f.fuse)(uj:u ≤ j)(jK:j ≤ K)(uv:u ≤ v)(vc:v ≤ c)(ck:c ≤ K)
    (D:ℕ)(d:Fin n→Fin (D+1))(fields:∀i,S.Field (d i).val)(arms:∀i,Arm C S (l:Filter _) (d i).val (fields i))
    (o:Fin n → Cover)(gen:tag ((C).S.a j) o∈generic n)(sep:tag ((C).S.a j) o∈conf n)
    (A:∀_N _per:ℕ,∀e:Fin (D+1),(C).label e ≃ₗ[ℂ] (C).label e)
    (renderer:∀(_N per:ℕ),((i:Fin n)→(C).label (d i))→(Fin n→ Site ((C).side K per))→
      ∀ i : ℕ, Config G ((C).side i per)→ℂ)
    (seed:∀N per:ℕ,K<N → ∀w ξ U,renderer N per w ξ K U=
        ∏i,WilsonPositionProgramBlockedTrialAddBack.uncut R (d i) N per K (ξ i) (w i) U)
    (prediction:Points n→ℂ)(phase upper across endFee:ℝ)
    (hi lo:ℕ→ℝ)
    (reflected:∀N per,∀top:j<N,‖gap R N per u (uj.trans top.le)
      (word R (fun i=>(d i).val) j N per top.le o (fun i=>(arms i).source (N,per)))‖ ≤ phase)
    (signed:∀ᶠ z:ℕ×ℕ in f.fuse,∀top:K<z.1,
      let Y:=word R (fun i=>(d i).val) j z.1 z.2 (jK.trans top.le) o (fun i=>(arms i).source z)
      let Y₀:=fun i=>(arms i).source
      let M:=fresh (R:=R) d Y₀ o jK A renderer
      let raw:=WilsonMovingForkRawSeed.print R (j:=j) (N:=z.1) (per:=z.2) d (A z.1 z.2)
        (fun i=>(arms i).source z) (seats (R:=R) jK z.2 o) univ
      let cut:=numerator R z.1 z.2 c (M z.1 z.2 c)
      let endPoint:=numerator R z.1 z.2 v (M z.1 z.2 v)
      (∀i,v ≤ i → i ≤ K → Integrable (numerator R z.1 z.2 i (M z.1 z.2 i)) (prior G _)) ∧
      ‖reading R (N:=z.1) (credit C z.1 z.2 0 Y K top.le) u (uv.trans (vc.trans ck))-
        reading R (N:=z.1) (numerator R z.1 z.2 K raw) u (uv.trans (vc.trans ck))‖ ≤ upper ∧
      (∀i∈Finset.Ico c K,‖feeAt R z.1 z.2 u (M z.1 z.2) i‖ ≤ hi i) ∧
      ‖reading R (N:=z.1) cut u (uv.trans vc)-reading R (N:=z.1) cut v vc‖ ≤ across ∧
      (∀i∈Finset.Ico v c,‖feeAt R z.1 z.2 v (M z.1 z.2) i‖ ≤ lo i) ∧
      ‖reading R (N:=z.1) endPoint v le_rfl-prediction (tag ((C).S.a j) o)‖ ≤ endFee):
    ‖S.classMoment S (fun i=>(d i).val) (tag ((C).S.a j) o) fields-prediction (tag ((C).S.a j) o)‖ ≤
      phase+(upper+(∑i∈Finset.Ico c K,hi i)+across+(∑i∈Finset.Ico v c,lo i)+endFee) := by
  let Y₀:=fun i=>(arms i).source
  let M:=fresh (R:=R) d Y₀ o jK A renderer
  apply WilsonMovingForkOpticalPoint.original F order uj jK uv vc ck (fun i=>(d i).val) fields arms o gen sep M
    (prediction (tag ((C).S.a j) o)) phase upper across endFee hi lo reflected
  filter_upwards [signed] with z sale
  intro top
  obtain ⟨paid,entry,old,cap,young,terminal⟩:=sale top
  refine ⟨paid,?_,old,cap,young,terminal⟩
  have same:M z.1 z.2 K=WilsonMovingForkRawSeed.print R (j:=j) (N:=z.1) (per:=z.2) d (A z.1 z.2)
      (fun i=>(arms i).source z) (seats (R:=R) jK z.2 o) univ:=by
    funext U
    exact seed z.1 z.2 top _ _ U
  unfold entrance
  rw [same]
  exact entry

end YM.Integration.WilsonMovingForkSeededPoint
