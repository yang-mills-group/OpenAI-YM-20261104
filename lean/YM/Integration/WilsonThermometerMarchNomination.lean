import YM.Integration.WilsonThermometerMarchSource
import YM.Integration.WilsonThermometerMarchFaceTransport
import YM.Integration.WilsonThermometerCourseIntake

/-! The compensated original grouped density on all eight faces, including each
displaced cutoff field, every mixed subword, and the genuine common vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerMarchNomination
open Extra.Trajectories FVA1 RG05Readout.Records ActualRunUnmaskedPartners
open Finset Function Filter MeasureTheory Lattice Wilson RG Source Extraction Table Spec Marker
open Climb Trace.Pilot Next.Rank Next.UVStress PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open OriginalForcedAddresses Push.GridApprox.Nil RG05Readout Native Address Many
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonThermometerMarchSource
open scoped Topology Classical BigOperators
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple) {m N p : ℕ}
local notation "d" => (fun i : Fin 3 => (grade i).val)
local notation "j" => (fun i : Fin 3 => index A (grade i))
local notation "w" => vector A (Finset.univ : Finset (Fin 3))
local notation "J" => Stock.census (Fin 3)

def prepared (r : (i : Fin 3) → Emblems R.family (d i)) (hm : m ≤ N) :=
  fun i => reduce (coordinate R A (p:=p) r hm i)

theorem startup (r : (i : Fin 3) → Emblems R.family (d i)) (hm : m ≤ N)
    (o : Positions (Fin 3) (R.family.side N p)) (ref : ∀ i, R.family.ref (d i) ≤ N)
    (s : (Stock.census (Fin 3)).Mode) :
    (fun U => (Accent.birth J (R.family.path.rep N p N)
      (WilsonThermometerIntrinsicRoster.source R d o.origin (prepared R A (p:=p) r hm) r hm) U).part s) =
    (∏ i ∈ s.val,weight R A (p:=p) r hm i) • (fun U =>
      (WilsonPositionThermometerDepositedFaces.pages R simple N p A.station (j) (w) o U).part s) := by
  rw [WilsonPositionThermometerDepositedFaces.entered R simple N p A.station (j) (w) o ref]
  funext U
  have on_site (i : Fin 3) : WilsonThermometerIntrinsicRoster.source R d o.origin (prepared R A (p:=p) r hm)
      r hm i U = weight R A (p:=p) r hm i * WilsonPositionThermometerDepositedFaces.leg R N p A.station (j) (w) o i U :=
    congrFun (WilsonThermometerMarchSource.leg R A r hm o.origin i) U
  simp only [Accent.birth,Accent.Mach,Poly.part_smul,pass_fire,Pi.smul_apply,smul_eq_mul,on_site]
  rw [Finset.prod_mul_distrib]
  ring

theorem reads (r : (i : Fin 3) → Emblems R.family (d i)) (hm : m ≤ N)
    (o : Positions (Fin 3) (R.family.side N p)) (ref : ∀ i, R.family.ref (d i) ≤ N)
    (paid : Integrable (WilsonThermometerIntrinsicRoster.density R d o.origin (prepared R A (p:=p) r hm)
      r J hm (Nat.le_refl N)) (prior G _)) (s : (Stock.census (Fin 3)).Mode) {b : ℕ} (hb : b ≤ N) :
    (fun U => (WilsonThermometerIntrinsicRoster.density R d o.origin (prepared R A (p:=p) r hm)
      r J hm hb U).part s) =
      (∏ i ∈ s.val,weight R A (p:=p) r hm i) •
        (fun U => (WilsonThermometerCourseIntake.incoming R A simple hb o U).part s) := by
  unfold WilsonThermometerIntrinsicRoster.density at paid
  rw [gust_base] at paid
  have original := WilsonPositionThermometerDepositedFaces.paid R simple N p A.station (j) (w) o ref (Nat.le_refl N)
  rw [gust_base] at original
  apply WilsonThermometerMarchFaceTransport.restored R.family _ _ _ _ paid original _ hb
  exact startup R A simple r hm o ref s

end YM.Integration.WilsonThermometerMarchNomination
