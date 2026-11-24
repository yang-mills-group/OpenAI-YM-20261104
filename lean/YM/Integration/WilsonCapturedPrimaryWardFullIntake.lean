import YM.Integration.WilsonCapturedPrimaryWardEnrolled
import YM.Integration.WilsonCapturedPrimaryWardCarton

/-! Undo the booked per-letter rescaling on the original deposited Wilson polynomial.
The one charge per occupied marker stays on every subsequent face, on the same
genuine quiet representative, regular words and complete forced gallery. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardFullIntake
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction Extra.Histories PhysicalNext.Repeat.Legato
open Bandage Stock RG16.Literal RG05Readout Native Address Many Records Harvest Copper
open RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat Legato
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells Accent Motion
open Trace.Physical.GermGraph GridApprox Next.Rank Ribbon Trace.Physical
open XSpace XSpace.Rose Push.GridApprox OPE OPE.Cards OPE.Orbits Spec
open WilsonCapturedPrimaryPhysicalArray WilsonCapturedPrimaryActiveArms
open WilsonCapturedPrimaryFaceWallet WilsonThermometerOwnOffsetField WilsonReflectedPhysicalRate
open WilsonCapturedPrimaryWardRestoration
open scoped Classical Topology BigOperators
open Table Spec Trace RG17 PhysMS PhysMS.Frame Maxwell XSpace.Normalize
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerReading
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap

variable {G : Gauge} (R : Run G) {f : Extraction.Order} {T : Table R.family.book}
    {l : Ultrafilter (ℕ×ℕ)} {H : (Bel R.family.book).Hierarchy}
variable (F : Final R.family f T) (J : ℝ → PhysMS.tower T) (O : Store G) (A : ℝ → Group R.family 6)
variable (V : ∀d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
    (P : ∀d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)) (b : Presentation R.family)

open WilsonCapturedPrimaryWardAppointment (share trimmed)
open WilsonCapturedPrimaryWardThermometer (input)
open WilsonThermometerIntrinsicRoster
open Marker Extra.Multi

open WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetInvoice
open WilsonCapturedPrimaryWardEnrolled WilsonThermometerMarchSource WilsonCapturedPrimaryWardFiring
set_option quotPrecheck false
variable {G:Gauge} (R:Run G) {n k N p:ℕ} (d:Fin n→ℕ)
variable (o:Fin n→Site (R.family.side N p))
variable (S:Shelf (N:=N) (p:=p) R k d o) (live:k≤N) (v:(i:Fin n)→R.family.label (d i))
variable (y:(i:Fin n)→Palette R.family (d i))
local notation "J" => Stock.census (Fin n)
local notation "ρ" => (fun i=>charge (y i))
local notation "Q" => (fun j i=>state (k:=k) R (S.viewer i) (S.route i) (trimmed R d y i) (o i) j)
local notation "D" => (density R d o (trimmed R d y) S.route J live)

def full {j:ℕ} (hj:j≤N):=gust R.family.path N p N (WilsonCapturedPrimaryWardAppointment.input R d o v J) j hj

theorem undo {t:ℕ} (h:Fine t S live v y) {j:ℕ} (hj:j≤N) :
    (fun U=>names J ρ (D hj U))=full R d o v hj:=by
  funext U
  ext s
  have face:=congrFun (h.2 j hj s) U
  change (D hj U).part s=(∏ i∈s.val,share R d y i)*(full R d o v hj U).part s at face
  rw [names_part,face,←mul_assoc]
  have one:(Poly.toll ρ s:ℂ)*(∏ i∈s.val,share R d y i)=1:=by
    simp only [Poly.toll,Complex.ofReal_prod,WilsonCapturedPrimaryWardAppointment.share]
    rw [←Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _=>mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (charged (y i)).ne')
  rw [one,one_mul]

theorem original {t:ℕ} (h:Fine t S live v y) {j:ℕ} (lower:k≤j) (upper:j≤N) :
    Integrable (full R d o v upper) (prior G _) ∧
      Accent.Served (R.family.path.rep N p j) (fun i U=>(charge (y i):ℂ)*(Q j i).2.1 U)
        (fun i p' U=>(charge (y i):ℂ)*Accent.tapes R.family.path p N (fun i' l=>(Q i' l).2.2) j i p' U)
        (full R d o v upper) (WilsonThermometerOwnOffsetJoint.origins R o j)
        (fun i=>WilsonThermometerOwnOffsetRadii.radius R t k j/charge (y i)) (topPitch R.family.path N j) 1:=by
  obtain ⟨paid,_,served⟩:=h.1 j lower upper
  rw [←undo R d o S live v y h upper]
  refine ⟨?_,WilsonCapturedPrimaryWardCarton.original ρ (fun i=>charged (y i)) _ served⟩
  let L:(Poly J)→L[ℂ](Poly J):=(names J ρ).toLinearMap.toContinuousLinearMap
  exact L.integrable_comp paid

theorem rate (t:ℕ) (s:(J).Mode):
    (Poly.toll (fun i=>WilsonThermometerOwnOffsetRadii.radius R t k k/charge (y i)) s)⁻¹=
      (R.family.path.levels.clock.hatBeta k)^(t*s.val.card) * ∏ i∈s.val,charge (y i):=by
  unfold Poly.toll
  simp_rw [radius_start]
  rw [Finset.prod_div_distrib]
  simp [←pow_mul,div_eq_mul_inv]
  exact mul_comm _ _

end YM.Integration.WilsonCapturedPrimaryWardFullIntake
